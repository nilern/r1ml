module Make (E : TyperSigs.ELABORATION) (M : TyperSigs.MATCHING) : TyperSigs.CHECKING = struct

open FcType
open Effect
open FcTerm
open TypeError

type 'a with_pos = 'a Ast.with_pos

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
        let domain = E.kindcheck env ann in
        let (env, universals, domain_locator, domain) = Env.push_domain_skolems env domain in
        let env = Env.push_domain env {name; typ = domain} domain_locator in
        let (env, existentials) = Env.push_existential env in
        let {TyperSigs.term = body; typ = codomain; eff} = typeof env body in

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
        let {TyperSigs.term = callee_expr; typ = callee_typ; eff = callee_eff} = typeof env callee in
        let name = Name.fresh () in
        let callee = {name; typ = callee_typ} in
        (match M.focalize callee_expr.pos env callee_typ (PiL (Vector.of_list [], Impure, Hole)) with
        | (Cf coerce, Pi (universals, locator, domain, app_eff, codomain)) ->
            let (uvs, _, domain, app_eff, codomain) =
                Env.instantiate_arrow env universals locator domain app_eff codomain in
            
            let {TyperSigs.term = arg; typ = _; eff = arg_eff} = check env (to_abs domain) arg in

            let term =
                { Ast.pos = callee_expr.pos
                ; v = Letrec ( Vector1.singleton (callee_expr.pos, callee, callee_expr)
                             , {expr with v = App ( coerce {expr with v = Use name}
                                                  , Vector.map (fun uv -> Uv uv) uvs, arg )} ) } in
            let eff = join_effs (join_effs callee_eff arg_eff) app_eff in
            let Exists (existentials, codomain_locator, concr_codo) = codomain in
            let (env, skolems, _, concr_codo) =
                Env.push_abs_skolems env (existentials, codomain_locator, concr_codo) in
            (match Vector1.of_vector skolems with
            | Some skolems ->
                let (_, _, res_typ) as typ = Env.reabstract env codomain in
                let Cf coerce = M.solving_coercion expr.pos env concr_codo typ in
                let name = Name.fresh () in
                let def = {name; typ = concr_codo} in
                { term = {term with v = Unpack (skolems, def, term, coerce {expr with v = Use name})}
                ; typ = res_typ
                ; eff = Impure }
            | None -> {term; typ = concr_codo; eff})
        | _ -> failwith "unreachable: callee focalization returned non-function")

    | Ast.Term.If _ -> check env (to_abs (Uv (Env.uv env (Name.fresh ())))) expr (* TODO: Unification? *)

    | Ast.Term.Seal (expr, typ) ->
        let Exists (existentials, _, _) as typ = E.kindcheck env typ in
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
        let {TyperSigs.term = record; typ = record_typ; eff} = typeof env record in
        let label = Name.to_string label in
        let shape = FcType.RecordL (Vector.singleton {label; typ = Hole}) in
        (match M.focalize record.pos env record_typ shape with
        | (Cf coerce, Record fields) ->
            let {label = _; typ} = Vector.get fields 0 in
            let name = Name.fresh () in
            let selectee = {name; typ = record_typ} in
            { term = {expr with v = Letrec ( Vector1.singleton (record.pos, selectee, record)
                                           , {expr with v = Select (coerce {expr with v = Use name}, label)} )}
            ; typ; eff}
        | _ -> failwith "unreachable: selectee focalization returned non-record")

    | Ast.Term.Proxy typ ->
        let typ = E.kindcheck env typ in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Pure}

    | Ast.Term.Use name ->
        let (_, {name; typ}) = lookup expr.pos env name in
        {term = {expr with v = Use name}; typ; eff = Pure}

    | Ast.Term.Const c ->
        let pt = match c with
            | Const.Int _ -> Prim.Int
            | Const.Bool _ -> Prim.Bool in
        {term = {expr with v = Const c}; typ = Prim pt; eff = Pure}

and field_types env fields =
    let (defs, fields, typs, eff) = Vector.fold_left (fun (defs, fields, typs, eff) field ->
        let {TyperSigs.term = (pos, {name; _}, _) as def; typ; eff = field_eff} = deftype env field in
        let label = Name.to_string name in
        ( def :: defs
        , {label; expr = {pos; v = Use name}} :: fields
        , {label; typ} :: typs
        , join_effs eff field_eff )
    ) ([], [], [], Pure) fields in
    (Vector.of_list (List.rev defs), Vector.of_list (List.rev fields), Vector.of_list (List.rev typs), eff)

and check env (typ : abs) (expr : Ast.Term.expr with_pos) =
    implement env (Env.reabstract env typ) expr

and implement env ((_, _, body) as typ) (expr : Ast.Term.expr with_pos) =
    match expr.v with
    | Ast.Term.If (cond, conseq, alt) ->
        let {TyperSigs.term = cond; typ = _; eff = cond_eff} = check env (to_abs (Prim Bool)) cond in
        let {TyperSigs.term = conseq; typ = _; eff = conseq_eff} = implement env typ conseq in
        let {TyperSigs.term = alt; typ = _; eff = alt_eff} = implement env typ alt in
        { term = {expr with v = If (cond, conseq, alt)}
        ; typ = body
        ; eff = join_effs cond_eff (join_effs conseq_eff alt_eff) }
    | _ ->
        let {TyperSigs.term; typ = expr_typ; eff} = typeof env expr in
        let name = Name.fresh () in
        let lvalue = {name; typ = expr_typ} in
        let Cf coerce = M.solving_coercion expr.pos env expr_typ typ in
        { term = {expr with v = Letrec ( Vector1.singleton (expr.pos, lvalue, term)
                                       , coerce {expr with v = Use name} )}
        ; typ = body; eff}

(* # Definitions and Statements *)

and deftype env (pos, {Ast.Term.pat = name; _}, expr) = (* FIXME: When GreyDecl has been encountered *)
    let _ = lookup pos env name in
    match Env.get pos env name with
    | (env, {contents = BlackDecl ({name = _; typ} as lvalue, existentials, locator)}) ->
        let {TyperSigs.term = expr; typ; eff} = implement env (existentials, locator, typ) expr in
        {term = (pos, lvalue, expr); typ; eff}
    | (_, {contents = BlackDef ({name = _; typ} as lvalue, eff, expr)}) ->
        {term = (pos, lvalue, expr); typ; eff}
    | (_, {contents = WhiteDecl _ | GreyDecl _ | WhiteDef _ | GreyDef _; _}) ->
        failwith "unreachable: decl or non-black binding in `deftype`"

(* # Lookup *)

and lookup pos env name =
    match Env.get pos env name with
    | (env, ({contents = Env.WhiteDecl (_, typ)} as binding)) ->
        binding := Env.GreyDecl (name, typ);
        let typ = E.kindcheck env typ in
        (match !binding with
        | Env.GreyDecl _ ->
            let (existentials, locator, typ) = Env.reabstract env typ in
            let lvalue = {name; typ} in
            binding := Env.BlackDecl (lvalue, existentials, locator);
            (locator, lvalue)
        | Env.BlackDecl ({name = _; typ = typ'} as lvalue, _, _) ->
            let Exists (existentials, _, body) = typ in
            if Vector.length existentials = 0 then begin
                let _ = M.solving_unify pos env body typ' in
                (Hole, lvalue)
            end else raise (TypeError (pos, PolytypeInference typ))
        | _ -> failwith "unreachable")
    | (env, ({contents = Env.GreyDecl _} as binding)) ->
        let lvalue = {name; typ = Uv (Env.uv env (Name.fresh ()))} in (* FIXME: uv level is wrong *)
        binding := Env.BlackDecl (lvalue, Vector.of_list [], Hole);
        (Hole, lvalue)
    | (_, {contents = Env.BlackDecl (lvalue, _, locator)}) -> (locator, lvalue)

    | (env, ({contents = Env.WhiteDef (name, expr)} as binding)) ->
        binding := Env.GreyDef (name, expr);
        let {TyperSigs.term = expr; typ; eff} = typeof env expr in
        (match !binding with
        | Env.GreyDef _ ->
            let lvalue = {name; typ} in
            binding := Env.BlackDef (lvalue, eff, expr);
            (Hole, lvalue)
        | Env.BlackDecl ({name = _; typ = typ'} as lvalue, _, _) ->
            let Cf coerce = M.solving_subtype expr.pos env typ Hole typ' in
            binding := Env.BlackDef (lvalue, eff, coerce expr); (* FIXME: Coercing nontrivial `expr` *)
            (Hole, lvalue)
        | _ -> failwith "unreachable")
    | (env, ({contents = Env.GreyDef _} as binding)) ->
        let lvalue = {name; typ = Uv (Env.uv env (Name.fresh ()))} in (* FIXME: uv level is wrong *)
        binding := Env.BlackDecl (lvalue, Vector.of_list [], Hole);
        (Hole, lvalue)
    | (_, {contents = Env.BlackDef (lvalue, _, _)}) -> (Hole, lvalue)
end

