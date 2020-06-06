module Make (C : TyperSigs.CHECKING) (M : TyperSigs.MATCHING) : TyperSigs.ELABORATION = struct

open FcTerm
open FcType
open TypeError

let rec kindcheck env (typ : Ast.Type.t with_pos) =
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
            (match C.typeof env {typ with v = expr} with
            | {term = _; typ = proxy_typ; eff = Pure} ->
                (match M.focalize typ.pos env proxy_typ (TypeL (UvP (Env.uv env (Name.fresh ())))) with
                | (_, Type typ) ->
                    let (_, locator, typ) = Env.reabstract env typ in
                    (locator, typ)
                | _ -> failwith "unreachable")
            | _ -> raise (TypeError (typ.pos, ImpureType expr)))

        | Ast.Type.Singleton expr ->
            (match C.typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> raise (TypeError (typ.pos, ImpureType expr.v)))

        | Ast.Type.Type ->
            let ov = Env.generate env (Name.fresh (), TypeK) in
            (TypeL (OvP ov), Type (to_abs (Ov ov)))

        | Ast.Type.Prim pt -> (Hole, Prim pt)

    and elaborate_decl env {name; typ} =
        let (locator, {name; typ}) = C.lookup typ.pos env name in
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
        | Fn body ->
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
end

