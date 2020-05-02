let (^/^) = PPrint.(^/^)

open FcType
open FcTerm
type 'a with_pos = 'a Ast.with_pos

type 'a typing = {term : 'a; typ : FcType.t; eff : Ast.effect}

exception TypeError

module Env = struct
    type val_binder =
        | WhiteDecl of Ast.decl
        | GreyDecl of Ast.decl
        | BlackDecl of lvalue
        | WhiteDef of Ast.lvalue * Ast.expr with_pos
        | GreyDef of Ast.lvalue * Ast.expr with_pos
        | BlackAnn of lvalue * Ast.expr with_pos * ov list
        | BlackUnn of lvalue * expr with_pos * effect

    type scope
        = Repl of (Name.t, val_binder ref) Hashtbl.t
        | Existential of binding list ref * level
        | Universal of ov list
        | Axiom of (Name.t * ov * FcType.t) Name.Map.t
        | Fn of val_binder ref
        | Sig of val_binder ref Name.Map.t
        | Struct of val_binder ref Name.Map.t

    type t = {scopes : scope list; current_level : level ref}

    let initial_level = 1

    let interactive () =
        { scopes = [Repl (Hashtbl.create 0); Existential (ref [], initial_level)]
        ; current_level = ref initial_level }

    let repl_define env ({name; _} as binding) =
        let rec define scopes =
            match scopes with
            | Repl kvs :: _ -> Hashtbl.replace kvs name (ref (BlackDecl binding))
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

    let skolemizing ({scopes; current_level} as env) (params, body) f =
        with_incremented_level env (fun () ->
            let level = !current_level in
            let skolems = List.map (fun binding -> (binding, level)) params in
            let substitution = List.fold_left (fun substitution (((name, _), _) as skolem) ->
                Name.Map.add name (Ov skolem) substitution
            ) Name.Map.empty skolems in
            f {env with scopes = Universal skolems :: scopes}
              (substitute substitution body)
        )

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

    let push_domain env binding =
        {env with scopes = Fn (ref (BlackDecl binding)) :: env.scopes}

    let push_sig env bindings =
        let bindings = List.fold_left (fun bindings ({Ast.name; _} as binding) ->
            Name.Map.add name (ref (WhiteDecl binding)) bindings
        ) Name.Map.empty bindings in
        {env with scopes = Sig bindings :: env.scopes}

    let push_struct env bindings =
        let bindings = List.fold_left (fun bindings ({Ast.pat = name; _} as binding, expr) ->
            Name.Map.add name (ref (WhiteDef (binding, expr))) bindings
        ) Name.Map.empty bindings in
        {env with scopes = Struct bindings :: env.scopes}

    let push_axioms env axioms =
        let bindings = List.fold_left (fun bindings ((_, ((k, _), _), _) as v) ->
            Name.Map.add k v bindings
        ) Name.Map.empty axioms in
        {env with scopes = Axiom bindings :: env.scopes}

    let get env name =
        let rec get scopes = match scopes with
            | Repl kvs :: scopes' ->
                (match Hashtbl.find_opt kvs name with
                | Some def -> ({env with scopes}, def)
                | None -> get scopes')
            | Fn ({contents = BlackDecl {name = name'; _}} as def) :: scopes' ->
                if name' = name
                then ({env with scopes}, def)
                else get scopes'
            | (Sig kvs | Struct kvs) :: scopes' ->
                (match Name.Map.find_opt name kvs with
                | Some def -> ({env with scopes}, def)
                | None -> get scopes')
            | (Existential _ | Universal _) :: scopes' -> get scopes'
            | [] -> raise TypeError
        in get env.scopes

    let get_implementation env ((name, _), _) =
        let rec get = function
            | Axiom kvs :: scopes ->
                (match Name.Map.find_opt name kvs with
                | Some axiom -> Some axiom
                | None -> get scopes)
            | _ :: scopes -> get scopes
            | [] -> None
        in get env.scopes
end

(* # Effects *)

let join_effs eff eff' = match (eff, eff') with
    | (Ast.Pure, Ast.Pure) -> Ast.Pure
    | _ -> Impure

(* # Expressions *)

let rec typeof env (expr : Ast.expr with_pos) = match expr.v with
    | Ast.Fn ({pat = name; ann}, body) ->
        let ann = match ann with
            | Some ann -> ann
            | None -> failwith "todo" in
        let (universals, _) as domain = kindcheck env ann in
        Env.skolemizing_domain env domain (fun env domain ->
            let env = Env.push_domain env {name; typ = domain} in
            Env.with_existential env (fun env existentials ->
                let {term = body; typ = codomain; eff} = typeof env body in
                { term = {expr with v = Fn (universals, {name; typ = domain}, body)} (* FIXME: bind existentials *)
                ; typ = Pi (universals, domain, eff, (!existentials, codomain))
                ; eff = Pure }
            )
        )
    | Ast.App (callee, arg) -> (* TODO: Support "dynamic" sealing of `if`-arg? *)
        let {term = callee; typ = callee_typ; eff = callee_eff} = typeof env callee in
        (match focalize callee.pos env callee_typ (Pi ([], Int, Impure, ([], Int))) with
        | (coerce, Pi (universals, domain, app_eff, codomain)) ->
            let uvs = List.map (fun (name, _) -> Uv (Env.uv env name)) universals in
            let substitution = List.fold_left2 (fun substitution (name, _) uv ->
                Name.Map.add name uv substitution
            ) Name.Map.empty universals uvs in
            let domain = substitute substitution domain in
            let codomain = substitute_abs substitution codomain in
            let {term = arg; typ = _; eff = arg_eff} = check env ([], domain) arg in
            { term = {expr with v = App ({expr with v = App (coerce, [], callee)}, uvs, arg)}
            ; typ = snd codomain (* FIXME: Hoist, unpack, axioms, coerce *)
            ; eff = join_effs (join_effs callee_eff arg_eff) app_eff }
        | _ -> failwith "unreachable")
    | Ast.Seal (expr, typ) -> check env (kindcheck env typ) expr
    | Ast.Struct defs ->
        let bindings = List.map (fun (_, lvalue, expr) -> (lvalue, expr)) defs in
        let env = Env.push_struct env bindings in
        let (defs, fields, field_typs, eff) = field_types env defs in
        { term = {expr with v = letrec defs {expr with v = Record fields}}
        ; typ = FcType.Record field_typs
        ; eff }
    | Ast.Proxy typ ->
        let typ = kindcheck env typ in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Pure}
    | Ast.Use name ->
        let {name = _; typ} as def = lookup env name in
        {term = {expr with v = Use def}; typ; eff = Pure}
    | Ast.Const c -> {term = {expr with v = Const c}; typ = Int; eff = Pure}

and field_types env fields =
    let (defs, fields, typs, eff) = List.fold_left (fun (defs, fields, typs, eff) field ->
        let {term = (pos, ({name; _} as lvalue), _) as def; typ; eff = field_eff} = deftype env field in
        let label = Name.to_string name in
        ( def :: defs
        , {label; expr = {pos; v = Use lvalue}} :: fields
        , {label; typ} :: typs
        , join_effs eff field_eff )
    ) ([], [], [], Pure) fields in
    (List.rev defs, List.rev fields, List.rev typs, eff)

and check env (typ : FcType.abs) (expr : Ast.expr with_pos) =
    implement env (reabstract env typ) expr

and implement env ((params, body) as typ : ov list * FcType.t) (expr : Ast.expr with_pos) =
    match expr.v with
    | Ast.If (cond, conseq, alt) ->
        let {term = cond; eff = cond_eff} = check env ([], Bool) cond in
        let {term = conseq; eff = conseq_eff} = implement env typ conseq in
        let {term = alt; eff = alt_eff} = implement env typ alt in
        { term = {expr with v = If (cond, conseq, alt)}
        ; typ = body
        ; eff = join_effs cond_eff (join_effs conseq_eff alt_eff) }
    | _ ->
        let {term; typ = expr_typ; eff} = typeof env expr in
        let coerce = coercion expr.pos true env expr_typ typ in
        {term = {expr with v = App ({v = coerce; pos = expr.pos}, [], term)}; typ = body; eff}

(* # Definitions and Statements *)

and deftype env (pos, {Ast.pat = name; _}, _) = (* FIXME: When GreyDecl has been encountered *)
    let _ = lookup env name in
    match Env.get env name with
    | (env, {contents = BlackAnn ({typ; _} as lvalue, expr, existentials)}) ->
        let {term = expr; typ; eff} = implement env (existentials, typ) expr in
        {term = (pos, lvalue, expr); typ; eff}
    | (env, {contents = BlackUnn ({typ; _} as lvalue, expr, eff)}) ->
        {term = (pos, lvalue, expr); typ; eff}

(* # Type Elaboration *)

and reabstract env (params, body) =
    let params' = List.map (fun param -> Env.generate env (freshen param)) params in
    let substitution = List.fold_left2 (fun substitution (name, _) param' ->
        Name.Map.add name (Ov param') substitution
    ) Name.Map.empty params params' in
    (params', substitute substitution body)

and kindcheck env (typ : Ast.typ with_pos) =
    let rec elaborate env (typ : Ast.typ with_pos) =
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
                            FcType.App (path, Use arg)
                        ) (FcType.Use existential) universals in
                        Name.Map.add name path substitution
                    ) Name.Map.empty existentials existentials' in
                    let codomain = (existentials', substitute substitution (snd codomain)) in
                    let (_, codomain) = reabstract env codomain in
                    Pi (universals, domain, eff, ([], codomain))
                | Impure -> Pi (universals, domain, eff, codomain)
            )
        | Ast.Sig decls ->
            let env = Env.push_sig env decls in
            Record (List.map (elaborate_decl env) decls)
        | Ast.Path expr ->
            (match typeof env {typ with v = expr} with
            | {term = _; typ = Type typ; eff = Pure} -> snd (reabstract env typ)
            | _ -> raise TypeError)
        | Ast.Singleton expr ->
            (match typeof env expr with
            | {term = _; typ; eff = Pure} -> typ
            | _ -> raise TypeError)
        | Ast.Type ->
            let ov = Env.generate env (Name.fresh (), TypeK) in
            Type ([], Ov ov)
        | Ast.Int -> Int
        | Ast.Bool -> Bool

    and elaborate_decl env {name; _} =
        let {name; typ} = lookup env name in
        {label = Name.to_string name; typ}
    in
    Env.with_existential env (fun env params ->
        let typ = elaborate env typ in
        (!params, typ)
    )

(* # Lookup *)

and lookup env name =
    match Env.get env name with
    | (env, ({contents = Env.WhiteDecl ({name; typ} as decl)} as binding)) ->
        binding := Env.GreyDecl decl;
        let lvalue = {name; typ = snd (reabstract env (kindcheck env typ))} in
        binding := Env.BlackDecl lvalue;
        lvalue
    | (env, {contents = Env.GreyDecl _}) -> raise TypeError
    | (_, {contents = Env.BlackDecl def}) -> def

    | (env, ({contents = Env.WhiteDef ({pat = name; ann = Some typ} as lvalue, expr)} as binding)) ->
        binding := Env.GreyDef (lvalue, expr);
        let (existentials, typ) = reabstract env (kindcheck env typ) in
        let lvalue = {name; typ} in
        binding := Env.BlackAnn (lvalue, expr, existentials);
        lvalue
    | (env, ({contents = Env.WhiteDef ({pat = name; ann = None} as lvalue, expr)} as binding)) ->
        binding := Env.GreyDef (lvalue, expr);
        let {term = expr; typ; eff} = typeof env expr in
        let lvalue = {name; typ} in
        binding := Env.BlackUnn (lvalue, expr, eff);
        lvalue
    | (env, ({contents = Env.GreyDef ({pat = name; ann = None} as lvalue, expr)} as binding)) ->
        let lvalue = {name; typ = Uv (Env.uv env (Name.fresh ()))} in (* FIXME: uv level is wrong *)
        binding := Env.BlackAnn (lvalue, expr, []);
        lvalue
    | (_, {contents = Env.BlackAnn (lvalue, _, _) | Env.BlackUnn (lvalue, _, _)}) -> lvalue

(* # Articulation *)

and articulate uv template = match uv with
    | {contents = Assigned _} -> failwith "unreachable"
    | {contents = Unassigned _} ->
        let typ =
            match template with
            | Pi _ -> Pi ([], Uv (sibling uv), Impure, ([], Uv (sibling uv)))
            | Type _ -> Type ([], Uv (sibling uv))
            | Int | Bool -> template
        in
        uv := Assigned typ;
        typ

(* # Focalization *)

and focalize pos env typ template = match (typ, template) with
    | (Pi _, Pi _) ->
        let param = {name = Name.fresh (); typ} in
        ({pos; v = Fn ([], param, {pos; v = Use param})}, typ)
    | (Uv uv, _) ->
        let param = {name = Name.fresh (); typ} in
        ({pos; v = Fn ([], param, {pos; v = Use param})}, articulate uv template)

(* # Subtyping *)

and sub_eff eff eff' = match (eff, eff') with
    | (Ast.Pure, Ast.Pure) -> ()
    | (Ast.Pure, Ast.Impure) -> ()
    | (Ast.Impure, Ast.Pure) -> raise TypeError
    | (Ast.Impure, Ast.Impure) -> ()

and coercion pos (occ : bool) env (typ : FcType.t) ((existentials, super) : ov list * FcType.t) =
    let axioms = List.map (fun (((name, _), _) as param) ->
        (Name.fresh (), param, Uv (Env.uv env name))
    ) existentials in
    let env = Env.push_axioms env axioms in
    let coerce = subtype pos occ env typ super in
    let param = {name = Name.fresh (); typ = typ} in
    Fn ([], param, {pos; v = Axiom (axioms, {pos; v = App ( {pos; v = coerce}, []
                                                          , {pos; v = Use param} )})})

and subtype_abs pos (occ : bool) env (typ : abs) (super : abs) = match (typ, super) with
    | (([], body), ([], body')) -> subtype pos occ env body body'

and subtype pos (occ : bool) env (typ : FcType.t) (super : FcType.t) =
    match (typ, super) with
    | (Uv _, Uv _) -> failwith "todo"
    | (Uv uv, super) ->
        (match !uv with
        | Assigned typ -> subtype pos occ env typ super
        | Unassigned _ -> subtype pos false env (articulate uv super) super)
    | (typ, Uv uv) ->
        (match !uv with
        | Assigned super -> subtype pos occ env typ super
        | Unassigned _ -> subtype pos false env typ (articulate uv typ))
    | (typ, Ov ov) ->
        (match Env.get_implementation env ov with
        | Some (axname, _, super) ->
            let coerce = subtype pos occ env typ super in
            let param = {name = Name.fresh (); typ = typ} in
            Fn ([], param, {pos; v = Cast ( {pos; v = App ({pos; v = coerce}, [], {pos; v = Use param})}
                                          , Symm (AUse axname) )})
        | None -> failwith "todo")
    | (Pi ([], domain, eff, codomain), Pi ([], domain', eff', codomain')) -> (* TODO: non-[] *)
        let coerce_domain = subtype pos occ env domain' domain in
        sub_eff eff eff';
        let coerce_codomain = subtype_abs pos occ env codomain codomain' in
        let param = {name = Name.fresh (); typ = typ} in
        Fn ([], param, {pos; v = App ( {pos; v = coerce_codomain}, []
                                     , {pos; v = App ( {pos; v = coerce_domain}, []
                                                     , {pos; v = Use param} )} )})
    | (Type carrie, Type carrie') -> (* TODO: Use unification (?) *)
        let _ = subtype_abs pos occ env carrie carrie' in
        let _ = subtype_abs pos occ env carrie carrie' in
        let lvalue = {name = Name.fresh (); typ = typ} in
        Fn ([], lvalue, {v = Proxy carrie'; pos})
    | (Int, Int) | (Bool, Bool) ->
        let lvalue = {name = Name.fresh (); typ = typ} in
        Fn ([], lvalue, {v = Use lvalue; pos})
    | _ -> failwith (Util.doc_to_string (PPrint.string "todo:"
                                         ^/^ (PPrint.infix 4 1 (PPrint.string "<:") (to_doc typ)
                                                               (to_doc super))))

(* # REPL support *)

let check_interaction env : Ast.stmt -> stmt typing = function
    | Ast.Def ((_, ({pat = name; _} as lvalue), expr) as def) ->
        let env = Env.push_struct env [(lvalue, expr)] in
        let {term; typ; eff} = deftype env def in
        Env.repl_define env {name; typ};
        {term = Def term; typ; eff}
    | Ast.Expr expr ->
        let {term; typ; eff} = typeof env expr in
        {term = Expr term; typ; eff}

