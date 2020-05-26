module Make (M : TyperSigs.MATCHING) : TyperSigs.CHECKING = struct

open FcType
open Effect
open FcTerm
open TypeError

type 'a with_pos = 'a Ast.with_pos

let instantiate_abs env (existentials, locator, body) =
    let uvs = Vector1.map (fun (name, _) -> Env.uv env name) existentials in
    let substitution = Vector1.fold_left2 (fun substitution (name, _) uv ->
            Name.Map.add name (UvP uv) substitution
    ) Name.Map.empty existentials uvs in
    (uvs, substitute_locator substitution locator, substitute substitution body)

let instantiate_arrow env (universals, domain_locator, domain, eff, codomain) =
    let uvs = Vector.map (fun (name, _) -> Env.uv env name) universals in
    let substitution = Vector.fold_left2 (fun substitution (name, _) uv ->
            Name.Map.add name (UvP uv) substitution
    ) Name.Map.empty universals uvs in
    ( uvs, substitute_locator substitution domain_locator, substitute substitution domain
    , eff, substitute_abs substitution codomain )

(* # Effects *)

let join_effs eff eff' = match (eff, eff') with
    | (Pure, Pure) -> Pure
    | _ -> Impure

(* # Expressions *)

let rec typeof env (expr : Ast.Term.expr with_pos) = match expr.v with
    | Ast.Term.Fn ({pat = name; ann}, body) ->
        let ann = match ann with
            | Some ann -> ann
            | None -> failwith "todo" in
        let domain = kindcheck env ann in
        let (env, universals, domain_locator, domain) = Env.push_domain_skolems env domain in
        let env = Env.push_domain env {name; typ = domain} domain_locator in
        let (env, existentials) = Env.push_existential env in
        let {Env.term = body; typ = codomain; eff} = typeof env body in

        let universals = Vector.map fst universals in
        let (body, codomain) = match Vector1.of_list (!existentials) with
            | Some existentials ->
                let uses = Vector1.map (fun binding -> FcType.Use binding) existentials in
                ( {body with Ast.v = LetType (existentials, {body with v = Pack (uses, body)})}
                , Exists (existentials, Hole, codomain) ) (* HACK: Hole *)
            | None -> (body, NoE codomain) in
        { term = {expr with v = Fn (universals, {name; typ = domain}, body)}
        ; typ = Pi (universals, domain_locator, domain, eff, codomain)
        ; eff = Pure }

    | Ast.Term.App (callee, arg) -> (* TODO: Support "dynamic" sealing of `if`-arg? *)
        let {Env.term = callee_expr; typ = callee_typ; eff = callee_eff} = typeof env callee in
        let callee = {name = Name.fresh (); typ = callee_typ} in
        (match M.focalize callee_expr.pos env callee_typ (PiL (Vector.of_list [], Impure, Hole)) with
        | (Cf coerce, Pi (universals, locator, domain, app_eff, codomain)) ->
            let (uvs, domain_locator, domain, app_eff, codomain) =
                instantiate_arrow env (universals, locator, domain, app_eff, codomain) in
            
            let {Env.term = arg; typ = _; eff = arg_eff} = check env (NoE domain) arg in

            let term =
                { Ast.pos = callee_expr.pos
                ; v = Letrec ( Vector1.singleton (callee_expr.pos, callee, callee_expr)
                             , {expr with v = App ( coerce {expr with v = Use callee}
                                                  , Vector.map (fun uv -> Uv uv) uvs, arg )} ) } in
            let eff = join_effs (join_effs callee_eff arg_eff) app_eff in
            (match codomain with
            | Exists (existentials, codomain_locator, concr_codo) ->
                let (env, existentials, codomain_locator, concr_codo) =
                    Env.push_abs_skolems env (existentials, codomain_locator, concr_codo) in
                let (_, _, res_typ) as typ = reabstract env codomain in
                let {coercion = Cf coerce; residual} = M.coercion expr.pos true env concr_codo typ in
                M.solve expr.pos env residual;

                let def = {name = Name.fresh (); typ = concr_codo} in
                { term = {term with v = Unpack (existentials, def, term, coerce {expr with v = Use def})}
                ; typ = res_typ
                ; eff = Impure }
            | NoE codomain -> {term; typ = codomain; eff})
        | _ -> failwith "unreachable: callee focalization returned non-function")

    | Ast.Term.If _ -> check env (NoE (Uv (Env.uv env (Name.fresh ())))) expr (* TODO: Unification? *)

    | Ast.Term.Seal (expr, typ) ->
        let typ = kindcheck env typ in
        let res = check env typ expr in
        let gen_eff = match typ with
            | Exists _ -> Impure
            | NoE _ -> Pure in
        {res with eff = join_effs res.eff gen_eff}

    | Ast.Term.Struct defs ->
        let bindings = Vector.map (fun (_, lvalue, expr) -> (lvalue, expr)) defs in
        let env = Env.push_struct env bindings in
        let (defs, fields, field_typs, eff) = field_types env defs in
        { term = {expr with v = letrec defs {expr with v = Record fields}}
        ; typ = FcType.Record field_typs
        ; eff }

    | Ast.Term.Select (record, label) ->
        let {Env.term = record; typ = record_typ; eff} = typeof env record in
        let label = Name.to_string label in
        let shape = FcType.RecordL (Vector.singleton {label; typ = Hole}) in
        (match M.focalize record.pos env record_typ shape with
        | (Cf coerce, Record fields) ->
            let {label = _; typ} = Vector.get fields 0 in
            let selectee = {name = Name.fresh (); typ = record_typ} in
            { term = {expr with v = Letrec ( Vector1.singleton (record.pos, selectee, record)
                                           , {expr with v = Select (coerce {expr with v = Use selectee}, label)} )}
            ; typ; eff}
        | _ -> failwith "unreachable: selectee focalization returned non-record")

    | Ast.Term.Proxy typ ->
        let typ = kindcheck env typ in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Pure}

    | Ast.Term.Use name ->
        let (_, ({name = _; typ} as def)) = lookup expr.pos env name in
        {term = {expr with v = Use def}; typ; eff = Pure}

    | Ast.Term.Const c ->
        let typ = match c with
            | Const.Int _ -> Int
            | Const.Bool _ -> Bool in
        {term = {expr with v = Const c}; typ; eff = Pure}

and field_types env fields =
    let (defs, fields, typs, eff) = Vector.fold_left (fun (defs, fields, typs, eff) field ->
        let {Env.term = (pos, ({name; _} as lvalue), _) as def; typ; eff = field_eff} = deftype env field in
        let label = Name.to_string name in
        ( def :: defs
        , {label; expr = {pos; v = Use lvalue}} :: fields
        , {label; typ} :: typs
        , join_effs eff field_eff )
    ) ([], [], [], Pure) fields in
    (Vector.of_list (List.rev defs), Vector.of_list (List.rev fields), Vector.of_list (List.rev typs), eff)

and check env (typ : abs) (expr : Ast.Term.expr with_pos) =
    implement env (reabstract env typ) expr

and implement env ((_, _, body) as typ) (expr : Ast.Term.expr with_pos) =
    match expr.v with
    | Ast.Term.If (cond, conseq, alt) ->
        let {Env.term = cond; eff = cond_eff} = check env (NoE Bool) cond in
        let {Env.term = conseq; eff = conseq_eff} = implement env typ conseq in
        let {Env.term = alt; eff = alt_eff} = implement env typ alt in
        { term = {expr with v = If (cond, conseq, alt)}
        ; typ = body
        ; eff = join_effs cond_eff (join_effs conseq_eff alt_eff) }
    | _ ->
        let {Env.term; typ = expr_typ; eff} = typeof env expr in
        let lvalue = {name = Name.fresh (); typ = expr_typ} in
        let {coercion = Cf coerce; residual} = M.coercion expr.pos true env expr_typ typ in
        M.solve expr.pos env residual;
        { term = {expr with v = Letrec ( Vector1.singleton (expr.pos, lvalue, term)
                                       , coerce {expr with v = Use lvalue} )}
        ; typ = body; eff}

(* # Definitions and Statements *)

and deftype env (pos, {Ast.Term.pat = name; _}, _) = (* FIXME: When GreyDecl has been encountered *)
    let _ = lookup pos env name in
    match Env.get pos env name with
    | (env, {contents = BlackAnn ({typ; _} as lvalue, expr, existentials, locator, coercion)}) -> (* FIXME: use coercion *)
        let {Env.term = expr; typ; eff} = implement env (existentials, locator, typ) expr in
        {term = (pos, lvalue, expr); typ; eff}
    | (env, {contents = BlackUnn ({typ; _} as lvalue, expr, eff)}) ->
        {term = (pos, lvalue, expr); typ; eff}
    | (_, {contents = WhiteDecl _ | GreyDecl _ | BlackDecl _ | WhiteDef _ | GreyDef _; _}) ->
        failwith "unreachable: decl or non-black binding in `deftype`"

(* # Types *)

and reabstract env : abs -> ov Vector.t * locator * typ = function
    | Exists (params, locator, body) ->
        let params' = Vector1.map (fun param -> Env.generate env (freshen param)) params in
        let substitution = Vector1.fold_left2 (fun substitution (name, _) param' ->
            Name.Map.add name (OvP param') substitution
        ) Name.Map.empty params params' in
        (Vector1.to_vector params', substitute_locator substitution locator, substitute substitution body)
    | NoE typ -> (Vector.of_list [], Hole, typ)

and kindcheck env (typ : Ast.Type.t with_pos) =
    let rec elaborate env (typ : Ast.Type.t with_pos) =
        match typ.v with
        | Ast.Type.Pi ({name; typ = domain}, eff, codomain) ->
            let domain = kindcheck env domain in
            let (env, universals, domain_locator, domain) = Env.push_domain_skolems env domain in
            let name = match name with
                | Some name -> name
                | None -> Name.fresh () in
            let env = Env.push_domain env {name; typ = domain} domain_locator in

            let universals = Vector.map fst universals in
            (match (eff, kindcheck env codomain) with
            | (Pure, Exists (existentials, codomain_locator, concr_codo)) ->
                let existentials' = existentials |> Vector1.map (fun (name, kind) ->
                    ( Name.freshen name
                    , Vector.fold_right (fun (_, arg_kind) kind -> ArrowK (arg_kind, kind))
                                        universals kind )
                ) in
                let substitution = Vector1.fold_left2 (fun substitution (name, _) existential ->
                    let path = Vector.fold_left (fun path arg ->
                        AppP (path, UseP arg)
                    ) (UseP existential) universals in
                    Name.Map.add name path substitution
                ) Name.Map.empty existentials existentials' in
                let codomain =
                    Exists ( existentials', substitute_locator substitution codomain_locator
                           , substitute substitution concr_codo ) in
                let (_, codomain_locator, concr_codo) = reabstract env codomain in
                ( PiL (universals, eff, codomain_locator)
                , Pi (universals, domain_locator, domain, eff, (NoE concr_codo)) )
            | (_, codomain) ->
                ( PiL (universals, eff, Hole)
                , Pi (universals, domain_locator, domain, eff, codomain) ))

        | Ast.Type.Sig decls ->
            let env = Env.push_sig env decls in
            let (locators, decls) = Vector.split (Vector.map (elaborate_decl env) decls) in
            (RecordL locators, Record decls)

        | Ast.Type.Path expr ->
            (match typeof env {typ with v = expr} with
            | {term = _; typ = proxy_typ; eff = Pure} ->
                (match M.focalize typ.pos env proxy_typ (TypeL (UseP (Name.fresh (), TypeK))) with
                | (_, Type typ) ->
                    let (_, locator, typ) = reabstract env typ in
                    (locator, typ)
                | _ -> failwith "unreachable")
            | _ -> raise (TypeError (typ.pos, ImpureType expr)))

        | Ast.Type.Singleton expr ->
            (match typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> raise (TypeError (typ.pos, ImpureType expr.v)))

        | Ast.Type.Type ->
            let ov = Env.generate env (Name.fresh (), TypeK) in
            (TypeL (OvP ov), Type (NoE (Ov ov)))

        | Ast.Type.Int -> (Hole, Int)
        | Ast.Type.Bool -> (Hole, Bool)

    and elaborate_decl env {name; typ} =
        let (locator, {name; typ}) = lookup typ.pos env name in
        let label = Name.to_string name in
        ({label; typ = locator}, {label; typ}) in

    let (env, params) = Env.push_existential env in
    let (locator, typ) = elaborate env typ in
    match Vector1.of_list (!params) with
    | Some params -> Exists (params, locator, typ)
    | None -> NoE typ

(* TODO: boolean flags considered harmful *)
and whnf pos env typ : bool * FcType.typ * coercion option =
    let rec eval : FcType.typ -> bool * FcType.typ * coercion option = function
        | App (callee, arg) ->
            let (decidable, callee, callee_co) = eval callee in
            let (decidable', typ, co) = apply callee arg in
            ( decidable && decidable'
            , typ
            , match (callee_co, co) with
              | (Some callee_co, Some co) -> Some (Trans (co, Inst (callee_co, arg)))
              | (Some callee_co, None) -> Some (Inst (callee_co, arg))
              | (None, Some co) -> Some co
              | (None, None) -> None )
        | Fn _ as typ -> (true, typ, None)
        | Ov ov as typ ->
            (match Env.get_implementation env ov with
            | Some (axname, _, uv) ->
                let typ = Uv uv in
                let (decidable, typ, co) = eval typ in
                ( decidable
                , typ
                , match co with
                  | Some co -> Some (Trans (AUse axname, co))
                  | None -> Some (AUse axname) )
            | None -> (true, typ, None))
        | Uv uv as typ ->
            (match !uv with
            | Assigned typ -> eval typ
            | Unassigned _ -> (true, typ, None))
        | (Pi _ | Record _ | Type _ | Int | Bool) as typ -> (true, typ, None)
        | Use _ -> failwith "unreachable: `Use` in `whnf`"

    and apply : typ -> typ -> bool * typ * coercion option = fun callee arg ->
        match callee with
        | Fn (param, body) -> eval (substitute_any (Name.Map.singleton param arg) body)
        | Ov _ | App _ -> (true, FcType.App (callee, arg), None)
        | Uv uv ->
            (match !uv with
            | Assigned callee -> apply callee arg
            | Unassigned _ -> (false, FcType.App (callee, arg), None))
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
            | NoE typ ->
                let {Env.coercion; residual} = M.unify pos env typ typ' in
                M.solve pos env residual;
                (Hole, lvalue)
            | _ -> raise (TypeError (pos, PolytypeInference typ)))
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
            | NoE typ ->
                let {Env.coercion = co; residual} = M.unify pos env typ typ' in
                M.solve pos env residual;
                binding := Env.BlackAnn (lvalue, expr, existentials, locator, co);
                (Hole, lvalue)
            | _ -> raise (TypeError (pos, PolytypeInference typ)))
        | _ -> failwith "unreachable: non-ann from ann `lookup`")
    | (env, ({contents = Env.WhiteDef ({pat = name; ann = None} as lvalue, expr)} as binding)) ->
        binding := Env.GreyDef (lvalue, expr);
        let {Env.term = expr; typ; eff} = typeof env expr in
        (match !binding with
        | Env.GreyDef _ ->
            let lvalue = {name; typ} in
            binding := Env.BlackUnn (lvalue, expr, eff);
            (Hole, lvalue)
        | Env.BlackAnn ({name = _; typ = typ'} as lvalue, _, _, _, _) ->
            let {coercion = Cf coerce; residual} = M.subtype expr.pos true env typ Hole typ' in
            M.solve pos env residual;
            binding := Env.BlackUnn (lvalue, coerce expr, eff); (* FIXME: Coercing nontrivial `expr` *)
            (Hole, lvalue)
        | _ -> failwith "unreachable: non-unn from unn `lookup`")
    | (env, ({contents = Env.GreyDef ({pat = name; ann = _}, expr)} as binding)) ->
        let lvalue = {name; typ = Uv (Env.uv env (Name.fresh ()))} in (* FIXME: uv level is wrong *)
        binding := Env.BlackAnn (lvalue, expr, Vector.of_list [], Hole, None);
        (Hole, lvalue)
    | (_, {contents = Env.BlackAnn (lvalue, _, _, locator, _)}) -> (locator, lvalue)
    | (_, {contents = Env.BlackUnn (lvalue, _, _)}) -> (Hole, lvalue)
end

