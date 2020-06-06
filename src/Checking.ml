module Make (M : TyperSigs.MATCHING) : TyperSigs.CHECKING = struct

open FcType
open Effect
open FcTerm
open TypeError

type 'a with_pos = 'a Ast.with_pos

let instantiate_abs env (existentials, locator, body) =
    let uvs = Vector.map (fun _ -> Env.uv env (Name.fresh ())) existentials in
    let substitution = Vector.map (fun uv -> UvP uv) uvs in
    (uvs, expose_locator substitution locator, expose substitution body)

let instantiate_arrow env (universals, domain_locator, domain, eff, codomain) =
    let uvs = Vector.map (fun _ -> Env.uv env (Name.fresh())) universals in
    let substitution = Vector.map (fun uv -> UvP uv) uvs in
    ( uvs, expose_locator substitution domain_locator, expose substitution domain, eff
    , expose_abs substitution codomain )

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
        let (body, codomain) =
            let existentials = Vector.of_list (!existentials) in
            let (_, substitution) = Vector.fold_left (fun (i, substitution) (name, _) ->
                (i + 1, Name.Map.add name i substitution)
            ) (0, Name.Map.empty) existentials in
            ( (match Vector1.of_vector existentials with
              | Some existentials ->
                  let uses = Vector1.map (fun binding -> FcType.Use binding) existentials in
                  {body with Ast.v = LetType (existentials, {body with v = Pack (uses, body)})}
              | None -> body)
            , Exists (Vector.map snd existentials, Hole, close substitution codomain) ) in (* HACK: Hole *)
        let term = {expr with v = Fn (universals, {name; typ = domain}, body)} in

        let typ = 
            let (domain_locator, domain, codomain) = match Vector1.of_vector universals with
                | Some universals ->
                    let (_, substitution) = Vector1.fold_left (fun (i, substitution) (name, _) ->
                        (i + 1, Name.Map.add name i substitution)
                    ) (0, Name.Map.empty) universals in
                    ( close_locator substitution domain_locator, close substitution domain
                    , close_abs substitution codomain )
                | None -> (domain_locator, domain, codomain) in
            Pi (Vector.map snd universals, domain_locator, domain, eff, codomain) in

        {term; typ; eff = Pure}

    | Ast.Term.App (callee, arg) -> (* TODO: Support "dynamic" sealing of `if`-arg? *)
        let {Env.term = callee_expr; typ = callee_typ; eff = callee_eff} = typeof env callee in
        let callee = {name = Name.fresh (); typ = callee_typ} in
        (match M.focalize callee_expr.pos env callee_typ (PiL (Vector.of_list [], Impure, Hole)) with
        | (Cf coerce, Pi (universals, locator, domain, app_eff, codomain)) ->
            let (uvs, _, domain, app_eff, codomain) =
                instantiate_arrow env (universals, locator, domain, app_eff, codomain) in
            
            let {Env.term = arg; typ = _; eff = arg_eff} = check env (to_abs domain) arg in

            let term =
                { Ast.pos = callee_expr.pos
                ; v = Letrec ( Vector1.singleton (callee_expr.pos, callee, callee_expr)
                             , {expr with v = App ( coerce {expr with v = Use callee}
                                                  , Vector.map (fun uv -> Uv uv) uvs, arg )} ) } in
            let eff = join_effs (join_effs callee_eff arg_eff) app_eff in
            let Exists (existentials, codomain_locator, concr_codo) = codomain in
            let (env, skolems, codomain_locator, concr_codo) =
                Env.push_abs_skolems env (existentials, codomain_locator, concr_codo) in
            (match Vector1.of_vector skolems with
            | Some skolems ->
                let (_, _, res_typ) as typ = reabstract env codomain in
                let {coercion = Cf coerce; residual} = M.coercion expr.pos true env concr_codo typ in
                M.solve expr.pos env residual;
                let def = {name = Name.fresh (); typ = concr_codo} in
                { term = {term with v = Unpack (skolems, def, term, coerce {expr with v = Use def})}
                ; typ = res_typ
                ; eff = Impure }
            | None -> {term; typ = concr_codo; eff})
        | _ -> failwith "unreachable: callee focalization returned non-function")

    | Ast.Term.If _ -> check env (to_abs (Uv (Env.uv env (Name.fresh ())))) expr (* TODO: Unification? *)

    | Ast.Term.Seal (expr, typ) ->
        let Exists (existentials, _, _) as typ = kindcheck env typ in
        let res = check env typ expr in
        let gen_eff = if Vector.length existentials > 0 then Impure else Pure in
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
        let pt = match c with
            | Const.Int _ -> Prim.Int
            | Const.Bool _ -> Prim.Bool in
        {term = {expr with v = Const c}; typ = Prim pt; eff = Pure}

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
        let {Env.term = cond; typ = _; eff = cond_eff} = check env (to_abs (Prim Bool)) cond in
        let {Env.term = conseq; typ = _; eff = conseq_eff} = implement env typ conseq in
        let {Env.term = alt; typ = _; eff = alt_eff} = implement env typ alt in
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
    | (env, {contents = BlackAnn ({typ; _} as lvalue, expr, existentials, locator, coercion)}) ->
        let {Env.term = expr; typ; eff} = implement env (existentials, locator, typ) expr in
        let expr = match coercion with
            | Some coercion -> {expr with v = Cast (expr, coercion)}
            | None -> expr in
        {term = (pos, lvalue, expr); typ; eff}
    | (_, {contents = BlackUnn ({typ; _} as lvalue, expr, eff)}) ->
        {term = (pos, lvalue, expr); typ; eff}
    | (_, {contents = WhiteDecl _ | GreyDecl _ | BlackDecl _ | WhiteDef _ | GreyDef _; _}) ->
        failwith "unreachable: decl or non-black binding in `deftype`"

(* # Types *)

and reabstract env (Exists (params, locator, body)) =
    let params' = Vector.map (fun kind -> Env.generate env (Name.fresh (), kind)) params in
    let substitution = Vector.map (fun ov -> OvP ov) params' in
    (params', expose_locator substitution locator, expose substitution body)

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

            let ubs = Vector.map fst universals in
            let ukinds = Vector.map snd ubs in
            let (codomain_locator, codomain) =
                match (eff, kindcheck env codomain) with
                | (Pure, Exists (existentials, codomain_locator, concr_codo)) ->
                    let substitution = Vector.map (fun kind ->
                        let kind =
                            Vector.fold_right (fun arg_kind kind -> ArrowK (arg_kind, kind))
                                              ukinds kind in
                        let ov = Env.generate env (Name.freshen name, kind) in
                        Vector.fold_left (fun path arg -> AppP (path, OvP arg)) (OvP ov) universals
                    ) existentials in
                    ( expose_locator substitution codomain_locator
                    , to_abs (expose substitution concr_codo) )
                | (_, codomain) -> (Hole, codomain) in

            (match Vector1.of_vector ubs with
            | Some universals1 ->
                let (_, substitution) = Vector1.fold_left (fun (i, substitution) (name, _) ->
                    (i + 1, Name.Map.add name i substitution)
                ) (0, Name.Map.empty) universals1 in
                ( PiL (ukinds, eff, close_locator substitution codomain_locator)
                , Pi ( ukinds, close_locator substitution domain_locator
                     , close substitution domain, eff, close_abs substitution codomain ) )
            | None ->
                ( PiL (ukinds, eff, codomain_locator)
                , Pi (ukinds, domain_locator, domain, eff, codomain) ))

        | Ast.Type.Sig decls ->
            let env = Env.push_sig env decls in
            let (locators, decls) = Vector.split (Vector.map (elaborate_decl env) decls) in
            (RecordL locators, Record decls)

        | Ast.Type.Path expr ->
            (match typeof env {typ with v = expr} with
            | {term = _; typ = proxy_typ; eff = Pure} ->
                (match M.focalize typ.pos env proxy_typ (TypeL (UvP (Env.uv env (Name.fresh ())))) with
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
            (TypeL (OvP ov), Type (to_abs (Ov ov)))

        | Ast.Type.Prim pt -> (Hole, Prim pt)

    and elaborate_decl env {name; typ} =
        let (locator, {name; typ}) = lookup typ.pos env name in
        let label = Name.to_string name in
        ({label; typ = locator}, {label; typ}) in

    let (env, params) = Env.push_existential env in
    let (locator, typ) = elaborate env typ in
    let (_, substitution) = List.fold_left (fun (i, substitution) (name, _) ->
        (i + 1, Name.Map.add name i substitution)
    ) (0, Name.Map.empty) (!params) in
    Exists ( Vector.map snd (Vector.of_list (!params)), close_locator substitution locator
           , close substitution typ )

and whnf env typ =
    let (>>=) = Option.bind in

    let rec eval = function
        | FcType.App (callee, arg) ->
            eval callee >>= fun (callee, callee_co) ->
            apply callee arg |> Option.map (fun (typ, co) ->
            ( typ
            , match (callee_co, co) with
              | (Some callee_co, Some co) -> Some (Trans (co, Inst (callee_co, arg)))
              | (Some callee_co, None) -> Some (Inst (callee_co, arg))
              | (None, Some co) -> Some co
              | (None, None) -> None ))
        | Fn _ as typ -> Some (typ, None)
        | Ov ov as typ ->
            (match Env.get_implementation env ov with
            | Some (axname, _, uv) ->
                let typ = Uv uv in
                eval typ |> Option.map (fun (typ, co) ->
                ( typ
                , match co with
                  | Some co -> Some (Trans (AUse axname, co))
                  | None -> Some (AUse axname) ))
            | None -> Some (typ, None))
        | Uv uv as typ ->
            (match !uv with
            | Assigned typ -> eval typ
            | Unassigned _ -> Some (typ, None))
        | (Pi _ | Record _ | Type _ | Prim _) as typ -> Some (typ, None)
        | Bv _ -> failwith "unreachable: `Bv` in `whnf`"
        | Use _ -> failwith "unreachable: `Use` in `whnf`"

    and apply callee arg = match callee with
        | Fn (param, body) ->
            let substitution = Vector.singleton (UvP {contents = Assigned arg}) in (* HACK *)
            eval (expose substitution body)
        | Ov _ | App _ -> Some (FcType.App (callee, arg), None)
        | Uv uv ->
            (match !uv with
            | Unassigned _ -> None
            | Assigned _ -> failwith "unreachable: Assigned in `apply`.")
        | Pi _ | Record _ | Type _ | Prim _ | Bv _ | Use _ ->
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
        | Env.BlackDecl ({name = _; typ = typ'} as lvalue, _) ->
            let Exists (existentials, _, body) = typ in
            if Vector.length existentials = 0 then begin
                let {Env.coercion = _; residual} = M.unify pos env body typ' in
                M.solve pos env residual;
                (Hole, lvalue)
            end else raise (TypeError (pos, PolytypeInference typ))
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
            let Exists (existentials', _, body) = typ in
            if Vector.length existentials' = 0 then begin
                let {Env.coercion = co; residual} = M.unify pos env body typ' in
                M.solve pos env residual;
                binding := Env.BlackAnn (lvalue, expr, existentials, locator, co);
                (Hole, lvalue)
            end else raise (TypeError (pos, PolytypeInference typ))
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

