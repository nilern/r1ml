let (^/^) = PPrint.(^/^)

open FcType
open FcTerm
type 'a with_pos = 'a Ast.with_pos

type 'a typing = {term : 'a; typ : FcType.typ; eff : Ast.effect}

(* Newtype to allow ignoring subtyping coercions without partial application warning: *)
(* TODO: triv_expr with_pos -> expr with_pos to avoid bugs that would delay side effects
         or that duplicate large/nontrivial terms: *)
type coercer = Cf of (expr with_pos -> expr with_pos)

exception TypeError of span

let type_error_to_string (({pos_fname; _}, _) as span : Ast.span) =
    "Type error in " ^ pos_fname ^ " at " ^ Ast.span_to_string span

module Env = struct
    type val_binder =
        | WhiteDecl of Ast.decl
        | GreyDecl of Ast.decl
        | BlackDecl of lvalue * locator
        | WhiteDef of Ast.lvalue * Ast.expr with_pos
        | GreyDef of Ast.lvalue * Ast.expr with_pos
        | BlackAnn of lvalue * Ast.expr with_pos * ov list * locator * coercion option
        | BlackUnn of lvalue * expr with_pos * effect

    type scope
        = Repl of (Name.t, val_binder ref) Hashtbl.t
        | Existential of binding list ref * level
        | Universal of ov list
        | Axiom of (Name.t * ov * FcType.typ) Name.Map.t
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
            | Repl kvs :: _ -> Hashtbl.replace kvs name (ref (BlackDecl (binding, Hole)))
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

    let skolemizing_domain ({scopes; current_level} as env) (existentials, locator, domain) f =
        with_incremented_level env (fun () ->
            let level = !current_level in
            let skolems = List.map (fun binding -> (binding, level)) existentials in
            let substitution = List.fold_left (fun substitution (((name, _), _) as skolem) ->
                Name.Map.add name (Ov skolem) substitution
            ) Name.Map.empty skolems in
            f {env with scopes = Universal skolems :: scopes}
              (substitute substitution locator, substitute substitution domain)
        )

    let skolemizing_abs ({scopes; current_level} as env) (existentials, locator, body) f =
        with_incremented_level env (fun () ->
            let level = !current_level in
            let existentials' = List.map FcType.freshen existentials in
            let skolems = List.map (fun binding -> (binding, level)) existentials' in
            let substitution = List.fold_left (fun substitution (((name, _), _) as skolem) ->
                Name.Map.add name (Ov skolem) substitution
            ) Name.Map.empty skolems in
            f {env with scopes = Existential (ref existentials', level) :: scopes}
              (existentials', substitute substitution locator, substitute substitution body)
        )

    let skolemizing_arrow ({scopes; current_level} as env) (universals, domain, eff, codomain) f =
        with_incremented_level env (fun () ->
            let level = !current_level in
            let universals' = List.map FcType.freshen universals in
            let skolems = List.map (fun binding -> (binding, level)) universals' in
            let substitution = List.fold_left2 (fun substitution (name, _) skolem ->
                Name.Map.add name (Ov skolem) substitution
            ) Name.Map.empty universals skolems in
            f {env with scopes = Universal skolems :: scopes}
              (universals', substitute substitution domain, eff, substitute_abs substitution codomain)
        )

    let uv {current_level = {contents = level}; _} binding =
        ref (Unassigned (binding, level))

    let push_domain env binding locator =
        {env with scopes = Fn (ref (BlackDecl (binding, locator))) :: env.scopes}

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

    let get pos env name =
        let rec get scopes = match scopes with
            | Repl kvs :: scopes' ->
                (match Hashtbl.find_opt kvs name with
                | Some def -> ({env with scopes}, def)
                | None -> get scopes')
            | Fn ({contents = BlackDecl ({name = name'; _}, _)} as def) :: scopes' ->
                if name' = name
                then ({env with scopes}, def)
                else get scopes'
            | Fn _ :: _ -> failwith "unreachable: Fn scope with non-BlackDecl in `Env.get`"
            | (Sig kvs | Struct kvs) :: scopes' ->
                (match Name.Map.find_opt name kvs with
                | Some def -> ({env with scopes}, def)
                | None -> get scopes')
            | (Existential _ | Universal _ | Axiom _) :: scopes' -> get scopes'
            | [] -> raise (TypeError pos)
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

let instantiate_abs env (existentials, locator, body) =
    let uvs = List.map (fun (name, _) -> Uv (Env.uv env name)) existentials in
    let substitution = List.fold_left2 (fun substitution (name, _) uv ->
            Name.Map.add name uv substitution
    ) Name.Map.empty existentials uvs in
    (uvs, substitute substitution locator, substitute substitution body)

let instantiate_arrow env (universals, (domain_locator : template), domain, eff, codomain) =
    let uvs : typ list = List.map (fun (name, _) -> Uv (Env.uv env name)) universals in
    let substitution = List.fold_left2 (fun substitution (name, _) uv ->
            Name.Map.add name uv substitution
    ) Name.Map.empty universals uvs in
    ( uvs, substitute substitution domain_locator, substitute substitution domain
    , eff, substitute_abs substitution codomain )

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
        let (universals, domain_locator, domain) = kindcheck env ann in
        Env.skolemizing_domain env (universals, domain_locator, domain) (fun env (domain_locator, domain) ->
            let env = Env.push_domain env {name; typ = domain} domain_locator in
            Env.with_existential env (fun env existentials ->
                let {term = body; typ = codomain; eff} = typeof env body in
                { term = {expr with v = Fn (universals, {name; typ = domain}, body)} (* FIXME: bind existentials *)
                ; typ = Pi (universals, domain_locator, domain, eff, (!existentials, Hole, codomain)) (* HACK: Hole *)
                ; eff = Pure }
            )
        )
    | Ast.App (callee, arg) -> (* TODO: Support "dynamic" sealing of `if`-arg? *)
        let {term = callee_expr; typ = callee_typ; eff = callee_eff} = typeof env callee in
        let callee = {name = Name.fresh (); typ = callee_typ} in
        (match focalize callee_expr.pos env callee_typ (Pi ([], Hole, Hole, Impure, ([], Hole, Hole))) with
        | (coerce, Pi (universals, locator, domain, app_eff, ((_, _, concr_cod) as codomain))) ->
            let (uvs, domain_locator, domain, app_eff, codomain) =
                instantiate_arrow env (universals, locator, domain, app_eff, codomain) in

            let {term = arg; typ = _; eff = arg_eff} = check env ([], Hole, domain) arg in
            { term = { pos = callee_expr.pos
                     ; v = Letrec ( [(callee_expr.pos, callee, callee_expr)]
                                  , {expr with v = App (coerce {expr with v = Use callee}, uvs, arg)} ) }
            ; typ = concr_cod (* FIXME: Hoist, unpack, axioms, coerce *)
            ; eff = join_effs (join_effs callee_eff arg_eff) app_eff }
        | _ -> failwith "unreachable: callee focalization returned non-function")
    | Ast.If _ -> (* TODO: Unification? *)
        check env ([], Hole, Uv (Env.uv env (Name.fresh ()))) expr
    | Ast.Seal (expr, typ) ->
        let (existentials, _, _) as typ = kindcheck env typ in
        let res = check env typ expr in
        let gen_eff = match existentials with
            | _ :: _ -> Ast.Impure
            | [] -> Ast.Pure in
        {res with eff = join_effs res.eff gen_eff}
    | Ast.Struct defs ->
        let bindings = List.map (fun (_, lvalue, expr) -> (lvalue, expr)) defs in
        let env = Env.push_struct env bindings in
        let (defs, fields, field_typs, eff) = field_types env defs in
        { term = {expr with v = letrec defs {expr with v = Record fields}}
        ; typ = FcType.Record field_typs
        ; eff }
    | Ast.Select (record, label) ->
        let {term = record; typ = record_typ; eff} = typeof env record in
        let label = Name.to_string label in
        let shape = FcType.Record [{label; typ = Hole}] in
        (match focalize record.pos env record_typ shape with
        | (coerce, Record [{label = _; typ}]) ->
            let selectee = {name = Name.fresh (); typ = record_typ} in
            { term = {expr with v = Letrec ( [(record.pos, selectee, record)]
                                           , {expr with v = Select (coerce {expr with v = Use selectee}, label)} )}
            ; typ; eff}
        | _ -> failwith "unreachable: selectee focalization returned non-record")
    | Ast.Proxy typ ->
        let typ = kindcheck env typ in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Pure}
    | Ast.Use name ->
        let (_, ({name = _; typ} as def)) = lookup expr.pos env name in
        {term = {expr with v = Use def}; typ; eff = Pure}
    | Ast.Const c ->
        let typ = match c with
            | Const.Int _ -> Int
            | Const.Bool _ -> Bool in
        {term = {expr with v = Const c}; typ; eff = Pure}

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

and check env (typ : FcTerm.abs) (expr : Ast.expr with_pos) =
    implement env (reabstract env typ) expr

and implement env ((params, locator, body) as typ) (expr : Ast.expr with_pos) =
    match expr.v with
    | Ast.If (cond, conseq, alt) ->
        let {term = cond; eff = cond_eff} = check env ([], Hole, Bool) cond in
        let {term = conseq; eff = conseq_eff} = implement env typ conseq in
        let {term = alt; eff = alt_eff} = implement env typ alt in
        { term = {expr with v = If (cond, conseq, alt)}
        ; typ = body
        ; eff = join_effs cond_eff (join_effs conseq_eff alt_eff) }
    | _ ->
        let {term; typ = expr_typ; eff} = typeof env expr in
        let lvalue = {name = Name.fresh (); typ = expr_typ} in
        let coerce = coercion expr.pos true env expr_typ typ in
        { term = {expr with v = Letrec ([(expr.pos, lvalue, term)], coerce {expr with v = Use lvalue})}
        ; typ = body; eff}

(* # Definitions and Statements *)

and deftype env (pos, {Ast.pat = name; _}, _) = (* FIXME: When GreyDecl has been encountered *)
    let _ = lookup pos env name in
    match Env.get pos env name with
    | (env, {contents = BlackAnn ({typ; _} as lvalue, expr, existentials, locator, coercion)}) -> (* FIXME: use coercion *)
        let {term = expr; typ; eff} = implement env (existentials, locator, typ) expr in
        {term = (pos, lvalue, expr); typ; eff}
    | (env, {contents = BlackUnn ({typ; _} as lvalue, expr, eff)}) ->
        {term = (pos, lvalue, expr); typ; eff}
    | (_, {contents = WhiteDecl _ | GreyDecl _ | BlackDecl _ | WhiteDef _ | GreyDef _; _}) ->
        failwith "unreachable: decl or non-black binding in `deftype`"

(* # Types *)

and reabstract env (params, locator, body) =
    let params' = List.map (fun param -> Env.generate env (freshen param)) params in
    let substitution = List.fold_left2 (fun substitution (name, _) param' ->
        Name.Map.add name (Ov param') substitution
    ) Name.Map.empty params params' in
    (params', substitute substitution locator, substitute substitution body)

and kindcheck env (typ : Ast.typ with_pos) =
    let rec elaborate env (typ : Ast.typ with_pos) =
        match typ.v with
        | Ast.Pi ({name; typ = domain}, eff, codomain) ->
            let (universals, _, _) as domain = kindcheck env domain in
            Env.skolemizing_domain env domain (fun env (domain_locator, domain) ->
                let name = match name with
                    | Some name -> name
                    | None -> Name.fresh () in
                let env = Env.push_domain env {name; typ = domain} domain_locator in
                let (existentials, codomain_locator, codomain_impl) as codomain = kindcheck env codomain in
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
                    let codomain = ( existentials', substitute substitution codomain_locator
                                   , substitute substitution codomain_impl ) in
                    let (_, codomain_locator, codomain) = reabstract env codomain in
                    ( Pi (universals, Hole, Hole, eff, ([], Hole, codomain_locator))
                    , Pi (universals, domain_locator, domain, eff, ([], Hole, codomain)) )
                | Impure -> ( Pi (universals, Hole, Hole, eff, ([], Hole, Hole))
                            , Pi (universals, domain_locator, domain, eff, codomain) )
            )
        | Ast.Sig decls ->
            let env = Env.push_sig env decls in
            let (locators, decls) = List.split (List.map (elaborate_decl env) decls) in
            (Record locators, Record decls)
        | Ast.Path expr ->
            (match typeof env {typ with v = expr} with
            | {term = _; typ = proxy_typ; eff = Pure} ->
                (match focalize typ.pos env proxy_typ (Type ([], Hole, Hole)) with
                | (_, Type typ) ->
                    let (_, locator, typ) = reabstract env typ in
                    (locator, typ)
                | _ -> raise (TypeError typ.pos))
            | _ -> raise (TypeError typ.pos))
        | Ast.Singleton expr ->
            (match typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> raise (TypeError typ.pos))
        | Ast.Type ->
            let ov = Env.generate env (Name.fresh (), TypeK) in
            (Type ([], Hole, Ov ov), Type ([], Hole, Ov ov))
        | Ast.Int -> (Hole, Int)
        | Ast.Bool -> (Hole, Bool)

    and elaborate_decl env {name; typ} =
        let (locator, {name; typ}) = lookup typ.pos env name in
        let label = Name.to_string name in
        ({label; typ = locator}, {label; typ})
    in
    Env.with_existential env (fun env params ->
        let (locator, typ) = elaborate env typ in
        (!params, locator, typ)
    )

and whnf pos env typ : FcType.typ * coercion option =
    let rec eval : FcType.typ -> FcType.typ * coercion option = function
        | App (callee, arg) ->
            let (callee, callee_co) = eval callee in
            let (typ, co) = apply callee arg in
            ( typ
            , match (callee_co, co) with
              | (Some callee_co, Some co) -> Some (Trans (co, Inst (callee_co, arg)))
              | (Some callee_co, None) -> Some (Inst (callee_co, arg))
              | (None, Some co) -> Some co
              | (None, None) -> None )
        | Fn _ as typ -> (typ, None)
        | Ov ov as typ ->
            (match Env.get_implementation env ov with
            | Some (axname, _, typ) ->
                let (typ, co) = eval typ in
                ( typ
                , match co with
                  | Some co -> Some (Trans (AUse axname, co))
                  | None -> Some (AUse axname) )
            | None -> (typ, None))
        | Uv uv as typ ->
            (match !uv with
            | Assigned typ -> eval typ
            | Unassigned _ -> (typ, None))
        | (Pi _ | Record _ | Type _ | Int | Bool) as typ -> (typ, None)
        | Use _ -> failwith "unreachable: `Use` in `whnf`"

    and apply : FcType.typ -> FcType.typ -> FcType.typ * coercion option = fun callee arg ->
        match callee with
        | Fn (param, body) -> eval (substitute (Name.Map.singleton param arg) body)
        | Ov _ | App _ -> (FcType.App (callee, arg), None)
        | Uv uv ->
            (match !uv with
            | Assigned callee -> apply callee arg
            | Unassigned _ ->
                let f = match arg with
                    | Ov ((name, _), _) -> FcType.Fn (name, (Uv (sibling uv))) in
                uv := Assigned f;
                apply f arg)
        | Pi _ | Record _ | Type _ | Int | Bool | Use _ ->
            failwith "unreachable: uncallable type in `whnf`"
    in eval typ
    
(* # Lookup *)

and lookup pos env name =
    match Env.get pos env name with
    | (env, ({contents = Env.WhiteDecl ({name; typ} as decl)} as binding)) ->
        binding := Env.GreyDecl decl;
        let typ = kindcheck env typ in
        (match !binding with
        | Env.GreyDecl _ ->
            let (_, locator, typ) = reabstract env typ in
            let lvalue = {name; typ} in
            binding := Env.BlackDecl (lvalue, locator);
            (locator, lvalue)
        | Env.BlackDecl ({name = _; typ = typ'} as lvalue, locator) ->
            (match typ with
            | ([], Hole, typ) ->
                let _ = unify pos env typ typ' in
                (Hole, lvalue)
            | _ -> raise (TypeError pos))
        | _ -> failwith "unreachable: non-decl from decl `lookup`")
    | (env, ({contents = Env.GreyDecl _} as binding)) ->
        let lvalue = {name; typ = Uv (Env.uv env (Name.fresh ()))} in (* FIXME: uv level is wrong *)
        binding := Env.BlackDecl (lvalue, Hole);
        (Hole, lvalue)
    | (_, {contents = Env.BlackDecl (lvalue, locator)}) -> (locator, lvalue)

    | (env, ({contents = Env.WhiteDef ({pat = name; ann = Some typ} as lvalue, expr)} as binding)) ->
        binding := Env.GreyDef (lvalue, expr);
        let typ = kindcheck env typ in
        (match !binding with
        | Env.GreyDef _ ->
            let (existentials, locator, typ) = reabstract env typ in
            let lvalue = {name; typ} in
            binding := Env.BlackAnn (lvalue, expr, existentials, locator, None);
            (locator, lvalue)
        | Env.BlackAnn ({name = _; typ = typ'} as lvalue, expr, existentials, locator, None) ->
            (match typ with
            | ([], Hole, typ) ->
                let co = unify pos env typ typ' in
                binding := Env.BlackAnn (lvalue, expr, existentials, locator, co);
                (Hole, lvalue)
            | _ -> raise (TypeError pos))
        | _ -> failwith "unreachable: non-ann from ann `lookup`")
    | (env, ({contents = Env.WhiteDef ({pat = name; ann = None} as lvalue, expr)} as binding)) ->
        binding := Env.GreyDef (lvalue, expr);
        let {term = expr; typ; eff} = typeof env expr in
        (match !binding with
        | Env.GreyDef _ ->
            let lvalue = {name; typ} in
            binding := Env.BlackUnn (lvalue, expr, eff);
            (Hole, lvalue)
        | Env.BlackAnn ({name = _; typ = typ'} as lvalue, _, _, _, _) ->
            let Cf coerce = subtype expr.pos true env typ typ' in
            binding := Env.BlackUnn (lvalue, coerce expr, eff); (* FIXME: Coercing nontrivial `expr` *)
            (Hole, lvalue)
        | _ -> failwith "unreachable: non-unn from unn `lookup`")
    | (env, ({contents = Env.GreyDef ({pat = name; ann = _}, expr)} as binding)) ->
        let lvalue = {name; typ = Uv (Env.uv env (Name.fresh ()))} in (* FIXME: uv level is wrong *)
        binding := Env.BlackAnn (lvalue, expr, [], Hole, None);
        (Hole, lvalue)
    | (_, {contents = Env.BlackAnn (lvalue, _, _, locator, _)}) -> (locator, lvalue)
    | (_, {contents = Env.BlackUnn (lvalue, _, _)}) -> (Hole, lvalue)

(* # Articulation *)

and articulate pos = function
    | Uv uv as uv_typ -> fun template ->
        (match uv with
        | {contents = Assigned _} -> failwith "unreachable: `articulate` on assigned uv"
        | {contents = Unassigned (_, level)} ->
            (match template with
            | Pi _ ->
                let typ = Pi ([], Hole, Uv (sibling uv), Impure, ([], Hole, Uv (sibling uv))) in
                uv := Assigned typ;
                typ
            | Type _ ->
                let typ = Type ([], Hole, Uv (sibling uv)) in
                uv := Assigned typ;
                typ
            | Int -> uv := Assigned Int; Int
            | Bool -> uv := Assigned Bool; Bool
            | Ov ov ->
                let typ = Ov ov in
                uv := Assigned typ;
                typ
            | Uv uv' ->
                (match !uv' with
                | Assigned template -> articulate pos uv_typ template
                | Unassigned (_, level') ->
                    if level' <= level then begin
                        let typ = Uv uv' in
                        uv := Assigned typ;
                        typ
                    end else begin
                        let typ = Uv uv in
                        uv' := Assigned typ;
                        typ
                    end)
            | Record _ -> raise (TypeError pos) (* no can do without row typing *)
            | Use _ -> failwith "unreachable: `Use` as template of `articulate`"))
    | _ -> failwith "unreachable: `articulate` on non-uv"

(* # Focalization *)

and focalize pos env typ (template : FcType.template) = match (typ, template) with
    | (Uv uv, _) ->
        (match !uv with
        | Assigned typ -> focalize pos env typ template
        | Unassigned _ -> ((fun v -> v), articulate pos typ template))
    | (Pi _, Pi _) | (Type _, Type _) -> ((fun v -> v), typ)
    | (FcType.Record fields, FcType.Record ({label; typ = _} :: _)) ->
        (match List.find_opt (fun {label = label'; typ = _} -> label' = label) fields with
        | Some {label = _; typ = field_typ} -> ((fun v -> v), Record [{label; typ = field_typ}])
        | None -> raise (TypeError pos))

(* # Subtyping *)

and sub_eff pos eff eff' = match (eff, eff') with
    | (Ast.Pure, Ast.Pure) -> ()
    | (Ast.Pure, Ast.Impure) -> ()
    | (Ast.Impure, Ast.Pure) -> raise (TypeError pos)
    | (Ast.Impure, Ast.Impure) -> ()

and coercion pos (occ : bool) env (typ : FcType.typ) ((existentials, locator, super) : ov list * typ * typ) =
    let axiom_bindings = List.map (fun (((name, _), _) as param) ->
        (Name.fresh (), param, Uv (Env.uv env name))
    ) existentials in
    let env = Env.push_axioms env axiom_bindings in
    let Cf coerce = subtype pos occ env typ super in

    let axioms = List.map (fun (axname, (((_, kind) as binding, _) as param), impl) ->
        let rec axiomatize l r = function
            | ArrowK (domain, codomain) ->
                let def = (Name.fresh (), domain) in
                let l = FcType.App (l, Use def) in
                let r = FcType.App (r, Use def) in
                let (universals, l, r) = axiomatize l r codomain in
                (def :: universals, l, r)
            | TypeK -> ([], l, r) in
        let (universals, l, r) = axiomatize (Use binding) impl kind in
        (axname, universals, l, r)
    ) axiom_bindings in
    match axioms with
    | _ :: _ -> fun v -> {pos; v = Axiom (axioms, coerce v)}
    | [] -> coerce

and subtype_abs pos (occ : bool) env (typ : abs) (super : abs) =
    Env.skolemizing_abs env typ (fun env (existentials, sub_locator, typ) ->
        let (uvs, super_locator, super) = instantiate_abs env super in

        let Cf coerce = subtype pos occ env typ super in

        let impl = {name = Name.fresh (); typ} in
        let body = coerce {Ast.pos; v = Use impl} in
        let body = match uvs with
            | _ :: _ -> {Ast.pos; v = Pack (uvs, body)}
            | [] -> body in
        Cf (fun v ->
                match existentials with
                | _ :: _ -> {pos; v = Unpack (existentials, impl, v, body)}
                | [] -> {pos; v = Letrec ([(pos, impl, v)], body)})
    )

and subtype pos (occ : bool) env (typ : FcType.typ) (super : FcType.typ) : coercer =
    let rec subtype_whnf typ super = match (typ, super) with
        | (Uv uv, _) ->
            (match !uv with
            | Assigned typ -> subtype pos occ env typ super
            | Unassigned _ -> subtype pos false env (articulate pos typ super) super)
        | (_, Uv uv) ->
            (match !uv with
            | Assigned super -> subtype pos occ env typ super
            | Unassigned _ -> subtype pos false env typ (articulate pos super typ))
        | ( Pi (universals, domain_locator, domain, eff, codomain)
          , Pi (universals', domain_locator', domain', eff', codomain') ) ->
            Env.skolemizing_arrow env (universals', domain', eff', codomain')
                (fun env (universals', domain', eff', codomain') ->
                    let (uvs, domain_locator, domain, eff, codomain) =
                        instantiate_arrow env (universals, domain_locator, domain, eff, codomain) in

                    let Cf coerce_domain = subtype pos occ env domain' domain in
                    sub_eff pos eff eff';
                    let Cf coerce_codomain = subtype_abs pos occ env codomain codomain' in

                    let param = {name = Name.fresh (); typ = domain'} in
                    let arg = coerce_domain {pos; v = Use param} in
                    Cf (fun v ->
                            let body = coerce_codomain {pos; v = App (v, uvs, arg)} in
                            {pos; v = Fn (universals', param, body)})
                )
        | (FcType.Record fields, FcType.Record super_fields) ->
            let selectee = {name = Name.fresh (); typ = typ} in
            let fields = List.map (fun {label; typ = super} ->
                match List.find_opt (fun {label = label'; typ = _} -> label' = label) fields with
                | Some {label = _; typ} ->
                    let Cf coerce = subtype pos occ env typ super in
                    {label; expr = coerce {pos; v = Select ({pos; v = Use selectee}, label)}}
                | None -> raise (TypeError pos)
            ) super_fields in
            Cf (fun v -> {pos; v = Letrec ([(pos, selectee, v)], {pos; v = Record fields})})
        | (Type carrie, Type carrie') -> (* TODO: Use unification (?) *)
            let _ = subtype_abs pos occ env carrie carrie' in
            let _ = subtype_abs pos occ env carrie carrie' in
            Cf (fun _ -> {v = Proxy carrie'; pos})
        | (App _, App _) | (Ov _, Ov _) ->
            (match unify_whnf pos env typ super with
            | Some co -> Cf (fun v -> {pos; v = Cast (v, co)})
            | None -> Cf (fun v -> v))
        | (Int, Int) | (Bool, Bool) -> Cf (fun v -> v)
        | (Fn _, _) | (_, Fn _) -> failwith "unreachable: Fn in subtype_whnf"
        | (Use _, _) | (_, Use _) -> failwith "unreachable: Use in subtype_whnf" in
    let (typ, co) = whnf pos env typ in
    let (super, co') = whnf pos env super in
    let Cf coerce = subtype_whnf typ super in
    match (co, co') with
    | (Some co, Some co') ->
        Cf (fun v -> {pos; v = Cast (coerce {pos; v = Cast (v, co)}, Symm co')})
    | (Some co, None) -> Cf (fun v -> coerce {pos; v = Cast (v, co)})
    | (None, Some co') -> Cf (fun v -> {pos; v = Cast (coerce v, Symm co')})
    | (None, None) -> Cf coerce

and unify_abs pos env typ typ' : coercion option = match (typ, typ') with
    | (([], Hole, typ), ([], Hole, typ')) -> unify pos env typ typ'

and unify pos env typ typ' : coercion option=
    let (typ, co) = whnf pos env typ in
    let (typ', co'') = whnf pos env typ' in
    let co' = unify_whnf pos env typ typ' in
    match (co, co', co'') with
    | (Some co, Some co', Some co'') -> Some (Trans (Trans (co, co'), Symm co''))
    | (Some co, Some co', None) -> Some (Trans (co, co'))
    | (Some co, None, Some co'') -> Some (Trans (co, Symm co''))
    | (Some co, None, None) -> Some co
    | (None, Some co', Some co'') -> Some (Trans (co', Symm co''))
    | (None, Some co', None) -> Some co'
    | (None, None, Some co'') -> Some (Symm co'')
    | (None, None, None) -> None

and unify_whnf pos env (typ : typ) (typ' : typ) : coercion option = match (typ, typ') with
    | (Uv uv, _) ->
        (match !uv with
        | Assigned typ -> unify_whnf pos env typ typ'
        | Unassigned (_, level) ->
            check_uv_assignee pos uv level typ';
            uv := Assigned typ';
            None)
    | (_, Uv uv) ->
        (match !uv with
        | Assigned typ' -> unify_whnf pos env typ typ'
        | Unassigned (_, level) ->
            check_uv_assignee pos uv level typ;
            uv := Assigned typ;
            None)
    | (Type carrie, Type carrie') ->
        (match unify_abs pos env carrie carrie' with
        | Some co -> Some (TypeCo co)
        | None -> None)
    | (FcType.App (callee, arg), FcType.App (callee', arg')) ->
        let callee_co = unify_whnf pos env callee callee' in
        let arg_co = unify pos env arg arg' in
        (match (callee_co, arg_co) with
        | (Some callee_co, Some arg_co) -> Some (Comp (callee_co, arg_co))
        | (Some callee_co, None) -> Some (Comp (callee_co, Refl arg'))
        | (None, Some arg_co) -> Some (Comp (Refl callee', arg_co))
        | (None, None) -> None)
    | (Ov ov, Ov ov')->
        if ov = ov'
        then None
        else raise (TypeError pos)
    | (Int, Int) | (Bool, Bool) -> None
    | (Fn _, _) | (_, Fn _) -> failwith "unreachable: Fn in unify_whnf"

and check_uv_assignee_abs pos uv level : FcTerm.abs -> unit = function
    | ([], Hole, typ) -> check_uv_assignee pos uv level typ
    | (_ :: _, _, _) -> raise (TypeError pos) (* not a monotype *)

(* Monotype check, occurs check, ov escape check and uv level updates. Complected for speed. *)
and check_uv_assignee pos uv level : typ -> unit = function
    | Uv uv' ->
        if uv = uv'
        then raise (TypeError pos) (* occurs *)
        else
            (match !uv' with
            | Assigned typ -> check_uv_assignee pos uv level typ
            | Unassigned (name, level') ->
                if level' <= level
                then ()
                else uv' := Unassigned (name, level)) (* hoist *)
    | Ov (_, level') ->
        if level' <= level
        then ()
        else raise (TypeError pos) (* ov would escape *)
    | Pi ([], domain_locator, domain, _, codomain) ->
        check_uv_assignee pos uv level domain;
        check_uv_assignee_abs pos uv level codomain
    | Pi (_ :: _, _, _, _, _) -> raise (TypeError pos) (* not a monotype *)
    | Record fields ->
        List.iter (fun {label = _; typ} -> check_uv_assignee pos uv level typ) fields
    | Type carrie -> check_uv_assignee_abs pos uv level carrie
    | App (callee, arg) ->
        check_uv_assignee pos uv level callee;
        check_uv_assignee pos uv level arg
    | Int | Bool -> ()
    | Use _ -> failwith "unreachable: `Use` in `check_uv_assignee`"

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

