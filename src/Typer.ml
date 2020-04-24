let (^/^) = PPrint.(^/^)

open FcType
open FcTerm

type 'a typing = {term : 'a; typ : FcType.t; eff : Ast.effect}

exception TypeError

module Env = struct
    type scope
        = Repl of (Name.t, lvalue) Hashtbl.t
        | Existential of binding list ref * level
        | Universal of ov list
        | Fn of lvalue 

    type t = {scopes : scope list; current_level : level ref}

    let initial_level = 1

    let interactive () =
        { scopes = [Repl (Hashtbl.create 0); Existential (ref [], initial_level)]
        ; current_level = ref initial_level }

    let repl_define env ({name; _} as binding) =
        let rec define scopes =
            match scopes with
            | Repl kvs :: _ -> Hashtbl.replace kvs name binding
            | _ :: scopes' -> define scopes'
            | [] -> failwith "Typer.Env.repl_define: non-interactive type environment"
        in define env.scopes

    let with_incremented_level {current_level; _} body =
        current_level := !current_level + 1;
        Fun.protect body
            ~finally:(fun () -> current_level := !current_level - 1)

    let with_existential ({scopes; current_level} as env) f =
        with_incremented_level env (fun () ->
            let bindings = ref [] in
            f {env with scopes = Existential (bindings, !current_level) :: scopes} bindings
        )

    let generate env binding =
        let rec generate = function
            | Existential (bindings, level) :: _ ->
                bindings := binding :: !bindings;
                (binding, level)
            | _ :: scopes' -> generate scopes'
            | [] -> failwith "Typer.Env.generate: missing root Existential scope"
        in generate env.scopes

    let skolemizing_domain ({scopes; current_level} as env) (existentials, domain) f =
        with_incremented_level env (fun () ->
            let level = !current_level in
            let skolems = List.map (fun binding -> (binding, level)) existentials in
            let substitution = List.fold_left (fun substitution (((name, _), _) as skolem) ->
                Name.Map.add name (Ov skolem) substitution
            ) Name.Map.empty skolems in
            f {env with scopes = Universal skolems :: scopes}
              (substitute substitution domain)
        )

    let uv {current_level = {contents = level}; _} binding =
        ref (Unassigned (binding, level))

    let push_domain env binding = {env with scopes = Fn binding :: env.scopes}

    let get env name =
        let rec get scopes name =
            match scopes with
            | Repl kvs :: scopes' ->
                (match Hashtbl.find_opt kvs name with
                | Some def -> def
                | None -> get scopes' name)
            | Fn ({name = name'; _} as def) :: scopes' ->
                if name' = name then def else get scopes' name
            | (Existential _ | Universal _) :: scopes' -> get scopes' name
            | [] -> raise TypeError
        in get env.scopes name
end

(* # Effects *)

let join_effs eff eff' = match (eff, eff') with
    | (Ast.Pure, Ast.Pure) -> Ast.Pure
    | _ -> Impure

(* # Expressions *)

let rec typeof env (expr : Ast.expr Ast.with_pos) = match expr.v with
    | Ast.Fn ({pat = name; ann}, body) ->
        let ann = match ann with
            | Some ann -> ann
            | None -> failwith "todo" in
        let (universals, _) as domain = kindcheck env ann in
        Env.skolemizing_domain env domain (fun env domain ->
            let env = Env.push_domain env {name; typ = domain} in
            Env.with_existential env (fun env existentials ->
                let {term = body; typ = codomain; eff} = typeof env body in
                { term = {expr with v = Fn ( {name; typ = codomain}, body)} (* FIXME: bind existentials *)
                ; typ = (universals, Arrow (domain, eff, (!existentials, codomain)))
                ; eff = Pure }
            )
        )
    | Ast.App (callee, arg) -> (* TODO: Support "dynamic" sealing of `if`-arg? *)
        let {term = callee; typ = callee_typ; eff = callee_eff} = typeof env callee in
        (match focalize callee.pos env callee_typ (Arrow (([], Int), Impure, ([], ([], Int)))) with
        | (coerce, Arrow (domain, app_eff, codomain)) ->
            let {term = arg; typ = _; eff = arg_eff} = check env ([], domain) arg in
            { term = {expr with v = App ({expr with v = App (coerce, callee)}, arg)}
            ; typ = snd codomain (* FIXME: Translate from existential to F_c *)
            ; eff = join_effs (join_effs callee_eff arg_eff) app_eff }
        | _ -> failwith "unreachable")
    | Ast.Proxy typ ->
        let typ = kindcheck env typ in
        {term = {expr with v = Proxy typ}; typ = ([], Type typ); eff = Pure}
    | Ast.Use name ->
        let ({typ; _} as def) : lvalue = Env.get env name in
        {term = {expr with v = Use def}; typ; eff = Pure}
    | Ast.Const c -> {term = {expr with v = Const c}; typ = ([], Int); eff = Pure}

and check env ((params, _) as typ : FcType.abs) (expr : Ast.expr Ast.with_pos) =
    let check_concrete_unconditional env (typ : FcType.t) (expr : Ast.expr Ast.with_pos) =
        let {term; typ = expr_typ; eff} = typeof env expr in
        let coerce = subtype expr.pos true env expr_typ typ in
        {term = {expr with v = App ({v = coerce; pos = expr.pos}, term)}; typ; eff}
    in
    let rec implement env ((params, body) as typ : FcType.abs) (expr : Ast.expr Ast.with_pos) =
        match expr.v with
        | Ast.If (cond, conseq, alt) ->
            let {term = cond; eff = cond_eff} = check env ([], ([], Bool)) cond in
            let {term = conseq; eff = conseq_eff} = implement env typ conseq in
            let {term = alt; eff = alt_eff} = implement env typ alt in
            { term = {expr with v = If (cond, conseq, alt)}
            ; typ = body
            ; eff = join_effs cond_eff (join_effs conseq_eff alt_eff) }
        | _ ->
            (match params with
            | _ :: _ -> failwith "todo: create axioms"
            | [] -> ());
            check_concrete_unconditional env body expr
    in
    (match params with
    | _ :: _ -> failwith "todo: hoist abstract types"
    | [] -> ());
    implement env typ expr

(* # Definitions and Statements *)

and deftype env : Ast.def -> def typing = function
    | (pos, {Ast.pat = name; ann = Some ann}, expr) ->
        let abs_typ = kindcheck env ann in
        let {term = expr; typ; eff} = check env abs_typ expr in
        {term = (pos, {name; typ}, expr); typ; eff}
    | (pos, {Ast.pat = name; ann = None}, expr) ->
        let {term = expr; typ; eff} = typeof env expr in
        {term = (pos, {name; typ}, expr); typ; eff}

(* # Type Elaboration *)

and kindcheck env (typ : Ast.typ Ast.with_pos) =
    let reabstract env (params, body) =
        let substitution = List.fold_left (fun substitution ((name, _) as param) ->
            let skolem = Env.generate env (freshen param) in
            Name.Map.add name (Ov skolem) substitution
        ) Name.Map.empty params
        in substitute substitution body
    in
    let rec elaborate env (typ : Ast.typ Ast.with_pos) =
        match typ.v with
        | Ast.Pi ({name; typ = domain}, eff, codomain) ->
            let (universals, _) as domain = kindcheck env domain in
            Env.skolemizing_domain env domain (fun env domain ->
                let name = match name with
                    | Some name -> name
                    | None -> Name.fresh () in
                let env = Env.push_domain env {name; typ = domain} in
                let (existentials, _) as codomain = kindcheck env codomain in
                match eff with
                | Pure ->
                    let existentials' = existentials |> List.map (fun (name, kind) ->
                        ( Name.freshen name
                        , List.fold_right (fun (_, arg_kind) kind -> ArrowK (arg_kind, kind))
                                          universals kind )
                    ) in
                    let substitution = List.fold_left2 (fun substitution (name, _) existential ->
                        let path = List.fold_left (fun path arg ->
                            FcType.App (([], path), ([], Use arg))
                        ) (FcType.Use existential) universals in
                        Name.Map.add name path substitution
                    ) Name.Map.empty existentials existentials' in
                    let codomain = (existentials', substitute substitution (snd codomain)) in
                    let codomain = reabstract env codomain in
                    (universals, Arrow (domain, eff, ([], codomain)))
                | Impure -> (universals, Arrow (domain, eff, codomain))
            )
        | Ast.Path expr ->
            (match typeof env {typ with v = expr} with
            | {term = _; typ = ([], Type typ); eff = Pure} -> reabstract env typ
            | _ -> raise TypeError)
        | Ast.Singleton expr ->
            (match typeof env expr with
            | {term = _; typ; eff = Pure} -> typ
            | _ -> raise TypeError)
        | Ast.Type ->
            let ov = Env.generate env (Name.fresh (), TypeK) in
            ([], Type ([], ([], Ov ov)))
        | Ast.Int -> ([], Int)
        | Ast.Bool -> ([], Bool)
    in
    Env.with_existential env (fun env params ->
        let typ = elaborate env typ in
        (!params, typ)
    )

(* # Articulation *)

and articulate uv template = match uv with
    | {contents = Assigned _} -> failwith "unreachable"
    | {contents = Unassigned _} ->
        let typ =
            match template with
            | Arrow _ -> Arrow (([], Uv (sibling uv)), Impure, ([], ([], Uv (sibling uv))))
            | Type _ -> Type ([], ([], Uv (sibling uv)))
            | Int | Bool -> template
        in
        uv := Assigned typ;
        typ

(* # Focalization *)

and focalize pos env typ template =
    let focalize_unq typ template = match (typ, template) with
        | (Arrow _, Arrow _) ->
            let param = {name = Name.fresh (); typ = ([], typ)} in
            ({Ast.v = Fn (param, {Ast.v = Use param; pos}); pos}, typ)
    in
    match typ with
    | ([], body) -> focalize_unq body template
    | (universals, body) ->
        let uvs = List.map (fun (name, _) -> Env.uv env name) universals in
        let substitution = List.fold_left2 (fun substitution (name, _) uv ->
            Name.Map.add name (Uv uv) substitution
        ) Name.Map.empty universals uvs in
        let (coerce_instance, typ') = focalize_unq (substitute_unq substitution body) template in
        let param = {name = Name.fresh (); typ} in
        let body =
            List.fold_left (fun body uv -> {Ast.pos; v = TApp (body, {pos; v = Uv uv})})
                {pos; v = Use param} uvs in
        ( {pos; v = Fn (param, {pos; v = App (coerce_instance, body)})}
        , typ' )

(* # Subtyping *)

and sub_eff eff eff' = match (eff, eff') with
    | (Ast.Pure, Ast.Pure) -> ()
    | (Ast.Pure, Ast.Impure) -> ()
    | (Ast.Impure, Ast.Pure) -> raise TypeError
    | (Ast.Impure, Ast.Impure) -> ()

and subtype_abs pos (occ : bool) env (typ : abs) (super : abs) = match (typ, super) with
    | (([], body), ([], body')) -> subtype pos occ env body body'

and subtype pos (occ : bool) env (typ : FcType.t) (super : FcType.t) = match (typ, super) with
    | (([], body), ([], body')) -> subtype_unq pos occ env body body'

and subtype_unq pos (occ : bool) env (typ : FcType.unq) (super : FcType.unq) =
    match (typ, super) with
    | (Uv _, Uv _) -> failwith "todo"
    | (Uv uv, super) ->
        (match !uv with
        | Assigned typ -> subtype_unq pos occ env typ super
        | Unassigned _ -> subtype_unq pos false env (articulate uv super) super)
    | (typ, Uv uv) ->
        (match !uv with
        | Assigned super -> subtype_unq pos occ env typ super
        | Unassigned _ -> subtype_unq pos false env typ (articulate uv typ))
    | (Arrow (domain, eff, codomain), Arrow (domain', eff', codomain')) ->
        let coerce_domain = subtype pos occ env domain' domain in
        sub_eff eff eff';
        let coerce_codomain = subtype_abs pos occ env codomain codomain' in
        let param = {name = Name.fresh (); typ = ([], typ)} in
        Fn (param, {pos; v = App ( {pos; v = coerce_codomain}
                                 , {pos; v = App ( {pos; v = coerce_domain}
                                                 , {pos; v = Use param} )} )})
    | (Type carrie, Type carrie') -> (* TODO: Use unification (?) *)
        let _ = subtype_abs pos occ env carrie carrie' in
        let _ = subtype_abs pos occ env carrie carrie' in
        let lvalue = {name = Name.fresh (); typ = ([], typ)} in
        Fn (lvalue, {v = Use lvalue; pos})
    | (Int, Int) | (Bool, Bool) ->
        let lvalue = {name = Name.fresh (); typ = ([], typ)} in
        Fn (lvalue, {v = Use lvalue; pos})
    | _ -> failwith (Util.doc_to_string (PPrint.string "todo:"
                                         ^/^ (PPrint.infix 4 1 (PPrint.string "<:") (unq_to_doc typ)
                                                               (unq_to_doc super))))

(* # REPL support *)

let check_interaction env : Ast.stmt -> stmt typing = function
    | Ast.Def ((_, {pat = name; _}, _) as def) ->
        let {term; typ; eff} = deftype env def in
        Env.repl_define env {name; typ};
        {term = Def term; typ; eff}
    | Ast.Expr expr ->
        let {term; typ; eff} = typeof env expr in
        {term = Expr term; typ; eff}

