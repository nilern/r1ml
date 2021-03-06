module ResidualMonoid = struct
    include Monoid.OfSemigroup(Residual)

    let skolemized skolems m = Option.map (fun r -> Residual.Skolems (skolems, r)) m
end

module Make (E : TyperSigs.ELABORATION) : TyperSigs.MATCHING = struct

open Residual
open FcType
open Effect
open FcTerm
open TypeError

type coercer = TyperSigs.coercer

type 'a matching = {coercion : 'a; residual : Residual.t option}

(* # Focalization *)

let rec focalize pos env typ (template : FcType.template) : coercer * typ =
    let articulate_template pos uv_typ template = match uv_typ with
        | Uv uv ->
            (match uv with
            | {contents = Unassigned _} ->
                let (uv, typ) = match template with
                    | PiL _ ->
                        (uv, Pi (Vector.of_list [], Hole, Uv (sibling uv), Impure, (to_abs (Uv (sibling uv)))))
                    | TypeL _ -> (uv, Type (to_abs (Uv (sibling uv))))

                    | RecordL _ -> raise (TypeError (pos, RecordArticulationL template)) (* no can do without row typing *)
                    | Hole -> failwith "unreachable: Hole as template in `articulate_template`" in
                uv := Assigned typ;
                typ
            | {contents = Assigned _} -> failwith "unreachable: `articulate_template` on assigned uv")
        | _ -> failwith "unreachable: `articulate_template` on non-uv" in

    let focalize_whnf typ = match typ with
        | Uv {contents = Unassigned _} -> (TyperSigs.Cf Fun.id, articulate_template pos typ template)
        | Uv {contents = Assigned _} -> failwith "unreachable: Assigned uv in `focalize`."
        | _ ->
            (match template with
            | PiL _ ->
                (match typ with
                | Pi _ -> (Cf Fun.id, typ)
                | _ -> raise (TypeError (pos, Unusable (template, typ))))
            | TypeL _ ->
                (match typ with
                | Type _ -> (Cf Fun.id, typ)
                | _ -> raise (TypeError (pos, Unusable (template, typ))))
            | RecordL req_fields ->
                (match typ with
                | FcType.Record fields ->
                    let {label; typ = _} = Vector.get req_fields 0 in
                    (match Vector.find_opt (fun {label = label'; typ = _} -> label' = label) fields with
                    | Some {label = _; typ = field_typ} -> (Cf (fun v -> v), Record (Vector.singleton {label; typ = field_typ}))
                    | None -> raise (TypeError (pos, MissingField (typ, label))))
                | _ -> raise (TypeError (pos, Unusable (template, typ))))
            | Hole -> failwith "unreachable: Hole as template in `focalize`.") in

    match E.whnf env typ with
    | Some (typ, coercion) ->
        let (Cf cf as coercer, typ) = focalize_whnf typ in
        ( (match coercion with
          | Some coercion -> TyperSigs.Cf (fun v -> cf {pos; v = Cast (v, coercion)})
          | None -> coercer)
        , typ )
    | None -> failwith "unreachable: `whnf` failed in `focalize`."

and focalize_locator locator = function
    | Pi _ ->
        (match locator with
        | PiL _ -> locator
        | Hole -> PiL (Vector.of_list [], Impure, Hole)
        | _ -> failwith "unreachable: `Pi` locator")
    | Record _ ->
        (match locator with
        | RecordL _ -> locator
        | Hole -> RecordL (Vector.of_list [])
        | _ -> failwith "unreachable: `Record` locator")
    | Type _ ->
        (match locator with
        | TypeL _ -> locator
        | Hole -> TypeL (Prim Int) (* HACK *)
        | _ -> failwith "unreachable: `Type` locator")
    | _ -> locator (* HACK? *)

(* # Subtyping *)

and sub_eff pos eff eff' = match (eff, eff') with
    | (Pure, Pure) -> ()
    | (Pure, Impure) -> ()
    | (Impure, Pure) -> raise (TypeError (pos, SubEffect (eff, eff')))
    | (Impure, Impure) -> ()

and coercion pos env (typ : FcType.typ) ((existentials, super_locator, super) : ov Vector.t * locator * typ)
        : coercer matching =
    match Vector1.of_vector existentials with
    | Some existentials ->
        let axiom_bindings = Vector1.map (fun (((name, _), _) as param) ->
            (Name.fresh (), param, Env.uv env name)
        ) existentials in
        let env = Env.push_axioms env axiom_bindings in
        let {coercion = Cf coerce; residual} = subtype pos env typ super_locator super in

        let axioms = Vector1.map (fun (axname, (((_, kind), _) as ov), impl) -> match kind with
            | ArrowK (domain, _) ->
                let args = Vector1.mapi (fun sibli _ -> Bv {depth = 0; sibli}) domain in
                ( axname, Vector1.to_vector domain
                , FcType.App (Ov ov, args), FcType.App (Uv impl, args) )
            | TypeK -> (axname, Vector.of_list [], Ov ov, Uv impl)
        ) axiom_bindings in
        { coercion = Cf (fun v -> {pos; v = Axiom (axioms, coerce v)})
        ; residual = Option.map (fun residual -> Residual.Axioms (axiom_bindings, residual)) residual }
    | None -> subtype pos env typ super_locator super

and subtype_abs pos env (typ : abs) locator (super : abs) : coercer matching =
    let Exists (sub_kinds, sub_locator, typ) = typ in
    let (env, skolems, _, typ) = Env.push_abs_skolems env (sub_kinds, sub_locator, typ) in
    let Exists (existentials, super_locator, super) = super in
    let (uvs, super_locator, super) =
        Env.instantiate_abs env (existentials, super_locator, super) in
    match Vector1.of_vector skolems with
    | Some skolems ->
        (match Vector1.of_vector uvs with
        | Some uvs ->
            let {coercion = Cf coerce; residual} = subtype pos env typ super_locator super in

            let name = Name.fresh () in
            let impl = {name; typ} in
            let uvs = Vector1.map (fun uv -> Uv uv) uvs in
            let body = {Ast.pos; v = Pack (uvs, coerce {Ast.pos; v = Use name})} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized skolems residual }
        | None ->
            let {coercion = Cf coerce; residual} = subtype pos env typ locator super in

            let name = Name.fresh () in 
            let impl = {name; typ} in
            let body = coerce {Ast.pos; v = Use name} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized skolems residual })

    | None ->
        (match Vector1.of_vector uvs with
        | Some uvs ->
            let {coercion = Cf coerce; residual} = subtype pos env typ super_locator super in

            let uvs = Vector1.map (fun uv -> Uv uv) uvs in
            {coercion = Cf (fun v -> {pos; v = Pack (uvs, coerce v)}); residual}
        | None -> subtype pos env typ locator super)

(* FIXME: Reinstate `occ` plumbing. ATM won't create cycle but will try to create infinite tree. *)
and subtype pos env typ locator super : coercer matching =
    let empty = ResidualMonoid.empty in
    let combine = ResidualMonoid.combine in

    let articulate pos uv_typ template = match uv_typ with
        | Uv uv ->
            (match uv with
            | {contents = Unassigned (_, level)} ->
                let (uv, typ) = match template with
                    | Uv uv' ->
                        (match !uv' with
                        | Unassigned (_, level') ->
                            if level' <= level
                            then (uv, template)
                            else (uv', uv_typ)
                        | Assigned _ -> failwith "unreachable: Assigned as template of `articulate`")

                    | Ov ((_, level') as ov) ->
                        if level' <= level
                        then (uv, Ov ov)
                        else raise (TypeError (pos, Escape ov))

                    | Pi _ ->
                        (uv, Pi (Vector.of_list [], Hole, Uv (sibling uv), Impure, (to_abs (Uv (sibling uv)))))
                    | Type _ -> (uv, Type (to_abs (Uv (sibling uv))))
                    | App (_, args) ->
                        (uv, FcType.App (Uv (sibling uv), Vector1.map (fun _ -> Uv (sibling uv)) args))
                    | Prim pt -> (uv, Prim pt)

                    | Record _ -> raise (TypeError (pos, RecordArticulation template)) (* no can do without row typing *)
                    | Fn _ -> failwith "unreachable: `Fn` as template of `articulate`"
                    | Bv _ -> failwith "unreachable: `Bv` as template of `articulate`"
                    | Use _ -> failwith "unreachable: `Use` as template of `articulate`" in
                uv := Assigned typ;
                typ
            | {contents = Assigned _} -> failwith "unreachable: `articulate` on assigned uv")
        | _ -> failwith "unreachable: `articulate` on non-uv" in

    let subtype_whnf typ locator super : coercer matching = match (typ, super) with
        | (Uv uv, Uv uv') when uv = uv' -> {coercion = Cf Fun.id; residual = None}
        | (Uv uv, _) ->
            (match !uv with
            | Unassigned _ -> subtype pos env (articulate pos typ super) locator super
            | Assigned _ -> failwith "unreachable: Assigned `typ` in `subtype_whnf`")
        | (_, Uv uv) ->
            (match !uv with
            | Unassigned _ -> subtype pos env typ locator (articulate pos super typ)
            | Assigned _ -> failwith "unreachable: Assigned `super` in `subtype_whnf`")

        | (Pi (universals, domain_locator, domain, eff, codomain), _) -> (match super with
            | Pi (universals', _, domain', eff', codomain') ->
                let codomain_locator = match locator with
                    | PiL (_, _, codomain_locator) -> codomain_locator
                    | _ -> failwith "unreachable: function locator" in
                let (env, universals', domain', eff', codomain_locator, codomain') =
                    Env.push_arrow_skolems env universals' domain' eff' codomain_locator codomain' in
                let (uvs, domain_locator, domain, eff, codomain) =
                    Env.instantiate_arrow env universals domain_locator domain eff codomain in

                let {coercion = Cf coerce_domain; residual = domain_residual} =
                    subtype pos env domain' domain_locator domain in
                sub_eff pos eff eff';
                let {coercion = Cf coerce_codomain; residual = codomain_residual} =
                    subtype_abs pos env codomain codomain_locator codomain' in

                let name = Name.fresh () in
                let param = {name; typ = domain'} in
                let arg = coerce_domain {pos; v = Use name} in
                let arrows_residual = combine domain_residual codomain_residual in
                { coercion =
                    Cf (fun v ->
                            let body = coerce_codomain {pos; v = App (v, Vector.map (fun uv -> Uv uv) uvs, arg)} in
                            {pos; v = Fn (universals', param, body)})
                ; residual =
                    (match Vector1.of_vector universals' with
                    | Some skolems -> ResidualMonoid.skolemized skolems arrows_residual
                    | None -> arrows_residual) }
            | _ -> raise (TypeError (pos, SubType (typ, super))))

        | (FcType.Record fields, _) -> (match super with
            | FcType.Record super_fields ->
                let locator_fields = match locator with
                    | RecordL fields -> fields
                    | _ -> failwith "unreachable: record locator" in
                let name = Name.fresh () in
                let selectee = {name; typ = typ} in
                let (fields, residual) = Vector.fold_left (fun (fields', residual) {label; typ = super} ->
                    match Vector.find_opt (fun {label = label'; typ = _} -> label' = label) fields with
                    | Some {label = _; typ} ->
                        let locator =
                            match Vector.find_opt (fun {label = label'; typ = _} -> label' = label) locator_fields with
                            | Some {label = _; typ = locator} -> locator
                            | None -> Hole in
                        let {coercion = Cf coerce; residual = field_residual} = subtype pos env typ locator super in
                        ( {label; expr = coerce {pos; v = Select ({pos; v = Use name}, label)}} :: fields'
                        , combine residual field_residual )
                    | None -> raise (TypeError (pos, MissingField (typ, label)))
                ) ([], empty) super_fields in
                let fields = Vector.of_list (List.rev fields) in (* OPTIMIZE *)
                { coercion =
                    Cf (fun v -> {pos; v = Letrec (Vector1.singleton (pos, selectee, v), {pos; v = Record fields})})
                ; residual }
            | _ -> raise (TypeError (pos, SubType (typ, super))))

        | (Type (Exists (existentials, _, carrie) as abs_carrie), _) -> (match super with
            | Type abs_carrie' ->
                (match locator with
                | TypeL (App (callee, args)) ->
                    (match E.whnf env callee with
                    | Some (Uv ({contents = Unassigned (_, level)} as uv), _) ->
                        if Vector.length existentials = 0 then begin
                            let (_, substitution) = Vector1.fold_left (fun (i, substitution) arg ->
                                match arg with
                                | Ov ((name, _), _) -> (i + 1, Name.Map.add name i substitution)
                                | _ -> failwith "unreachable: non-ov path arg in path locator"
                            ) (0, Name.Map.empty) args in
                            let impl = FcType.Fn (close substitution carrie) in
                            let max_uv_level = match Vector1.get args 0 with
                                | Ov (_, level') -> level' - 1
                                | _ -> failwith "unreachable: non-ov path arg in path locator" in
                            check_uv_assignee pos env uv level max_uv_level impl;
                            uv := Assigned impl;
                            { coercion = TyperSigs.Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                            ; residual = empty }
                        end else raise (TypeError (pos, Polytype abs_carrie))

                    | _ -> (* TODO: Use unification (?) *)
                        let {coercion = _; residual} =
                            subtype_abs pos env abs_carrie Hole abs_carrie' in
                        let {coercion = _; residual = residual'} =
                            subtype_abs pos env abs_carrie' Hole abs_carrie in
                        { coercion = Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                        ; residual = combine residual residual' })

                | TypeL _ -> (* TODO: Use unification (?) *)
                    let {coercion = _; residual} =
                        subtype_abs pos env abs_carrie Hole abs_carrie' in
                    let {coercion = _; residual = residual'} =
                        subtype_abs pos env abs_carrie' Hole abs_carrie in
                    { coercion = Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                    ; residual = combine residual residual' }

                | _ -> failwith "unreachable: `Type` locator")
            | _ -> raise (TypeError (pos, SubType (typ, super))))

        | (App _, _) -> (match super with
            | App _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion =
                    (match coercion with
                    | Some co -> Cf (fun v -> {pos; v = Cast (v, co)})
                    | None -> Cf Fun.id)
                ; residual }
            | _ -> raise (TypeError (pos, SubType (typ, super))))

        | (Ov _, _) -> (match super with
            | Ov _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion =
                    (match coercion with
                    | Some co -> Cf (fun v -> {pos; v = Cast (v, co)})
                    | None -> Cf Fun.id)
                ; residual }
            | _ -> raise (TypeError (pos, SubType (typ, super))))

        | (Prim pt, _) -> (match super with
            | Prim pt' when Prim.eq pt pt' -> {coercion = Cf Fun.id; residual = empty}
            | _ -> raise (TypeError (pos, SubType (typ, super))))

        | (Fn _, _) -> failwith "unreachable: Fn in subtype_whnf"
        | (Bv _, _) -> failwith "unreachable: Bv in subtype_whnf"
        | (Use _, _) -> failwith "unreachable: Use in subtype_whnf" in

    let (>>=) = Option.bind in
    let res =
        E.whnf env typ >>= fun (typ', co) ->
        E.whnf env super |> Option.map (fun (super', co') ->
            let locator = focalize_locator locator super' in
            let {coercion = Cf coerce; residual} = subtype_whnf typ' locator super' in
            { coercion =
                (match (co, co') with
                | (Some co, Some co') ->
                    TyperSigs.Cf (fun v -> {pos; v = Cast (coerce {pos; v = Cast (v, co)}, Symm co')})
                | (Some co, None) -> Cf (fun v -> coerce {pos; v = Cast (v, co)})
                | (None, Some co') -> Cf (fun v -> {pos; v = Cast (coerce v, Symm co')})
                | (None, None) -> Cf coerce)
            ; residual }) in
    match res with
    | Some res -> res
    | None ->
        let patchable = ref {Ast.pos; v = Const (Int 0)} in
        { coercion = Cf (fun v ->
            patchable := v;
            {pos; v = Patchable patchable})
        ; residual = Some (Sub (typ, locator, super, patchable)) }

(* # Unification *)

and unify_abs pos env (Exists (existentials, locator, body)) (Exists (existentials', locator', body')) =
    if Vector.length existentials = 0 && Vector.length existentials' = 0
    then unify pos env body body'
    else failwith "todo"

and unify pos env typ typ' : coercion option matching =
    let (>>=) = Option.bind in
    let res =
        E.whnf env typ >>= fun (typ, co) ->
        E.whnf env typ' |> Option.map (fun (typ', co'') ->
        let {coercion = co'; residual} = unify_whnf pos env typ typ' in
        { coercion =
            (match (co, co', co'') with
            | (Some co, Some co', Some co'') -> Some (Trans (Trans (co, co'), Symm co''))
            | (Some co, Some co', None) -> Some (Trans (co, co'))
            | (Some co, None, Some co'') -> Some (Trans (co, Symm co''))
            | (Some co, None, None) -> Some co
            | (None, Some co', Some co'') -> Some (Trans (co', Symm co''))
            | (None, Some co', None) -> Some co'
            | (None, None, Some co'') -> Some (Symm co'')
            | (None, None, None) -> None)
        ; residual }) in
    match res with
    | Some res -> res
    | None ->
        let patchable = ref (Refl typ') in
        { coercion = Some (FcType.Patchable patchable)
        ; residual = Some (Unify (typ, typ', patchable)) }

and unify_whnf pos env (typ : typ) (typ' : typ) : coercion option matching =
    let open ResidualMonoid in
    match (typ, typ') with
    | (Uv uv, typ') | (typ', Uv uv) ->
        (match !uv with
        | Unassigned (_, level) ->
            check_uv_assignee pos env uv level Int.max_int typ';
            uv := Assigned typ';
            {coercion = None; residual = empty}
        | Assigned _ -> failwith "unreachable: Assigned `typ` in `unify_whnf`")

    | (Type carrie, _) -> (match typ' with
        | Type carrie' -> 
            let {coercion; residual} = unify_abs pos env carrie carrie' in
            { coercion =
                (match coercion with
                | Some co -> Some (TypeCo co)
                | None -> None)
            ; residual }
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (FcType.App (callee, args), _) -> (match typ' with
        | FcType.App (callee', args') ->
            let {coercion = callee_co; residual} = unify_whnf pos env callee callee' in
            let matchings = Vector1.map2 (unify pos env) args args' in
            { coercion = (match callee_co with
                | Some callee_co ->
                    Some (Comp (callee_co, Vector1.map2 (fun {coercion; _} arg' -> match coercion with
                        | Some coercion -> coercion
                        | None -> Refl arg'
                    ) matchings args'))
                | None ->
                    if Vector1.exists (fun {coercion; _} -> Option.is_some coercion) matchings
                    then Some (Comp (Refl callee', Vector1.map2 (fun {coercion; _} arg' -> match coercion with
                        | Some coercion -> coercion
                        | None -> Refl arg'
                    ) matchings args'))
                    else None)
            ; residual = Vector1.fold_left (fun residual {coercion = _; residual = residual'} ->
                    combine residual residual'
                ) residual matchings }
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (Ov ov, _) -> (match typ' with
        | Ov ov'->
            if ov = ov'
            then {coercion = None; residual = empty}
            else raise (TypeError (pos, Unify (typ, typ')))
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (Prim pt, _) -> (match typ' with
        | Prim pt' when Prim.eq pt pt'-> {coercion = None; residual = empty}
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (Fn _, _) -> failwith "unreachable: Fn in unify_whnf"
    | (Bv _, _) -> failwith "unreachable: Bv in unify_whnf"
    | (Use _, _) -> failwith "unreachable: Use in unify_whnf"

(* Monotype check, occurs check, ov escape check, HKT capturability check and uv level updates.
   Complected for speed. *)
and check_uv_assignee pos env uv level max_uv_level typ =
    let rec check_abs (Exists (existentials, _, body) as typ) =
        if Vector.length existentials = 0
        then check body
        else raise (TypeError (pos, Polytype typ))

    and check = function
        | Pi (universals, _, domain, _, codomain) ->
            if Vector.length universals = 0
            then (check domain; check_abs codomain)
            else raise (TypeError (pos, Polytype (to_abs typ)))
        | Record fields -> Vector.iter (fun {label = _; typ} -> check typ) fields
        | Type carrie -> check_abs carrie
        | Fn body -> check body
        | App (callee, args) -> check callee; Vector1.iter check args
        | Ov ((_, level') as ov) ->
            (match Env.get_implementation env ov with
            | Some (_, _, uv') -> check (Uv uv')
            | None ->
                if level' <= level
                then ()
                else raise (TypeError (pos, Escape ov)))
        | Uv uv' ->
            (match !uv' with
            | Unassigned (name, level') ->
                if uv = uv'
                then raise (TypeError (pos, Occurs (uv, typ)))
                else if level' <= level
                then ()
                else if level' <= max_uv_level
                then uv' := Unassigned (name, level) (* hoist *)
                else raise (TypeError (pos, IncompleteImpl (uv, uv')))
            | Assigned typ -> check typ)
        | Bv _ | Use _ | Prim _ -> () in
    check typ

(* # Constraint Solving *)

and solve pos env residual =
    let rec solve env = function
        | Axioms (axiom_bindings, residual) ->
            let env = Env.push_axioms env axiom_bindings in
            solve env residual

        | Skolems (skolems, residual) ->
            let env = Env.push_skolems env skolems in
            solve env residual

        | Residuals (residual, residual') ->
            ResidualMonoid.combine (solve env residual) (solve env residual')

        | Sub (typ, locator, super, patchable) ->
            let {coercion = Cf coerce; residual} = subtype pos env typ locator super in
            patchable := coerce (!patchable);
            residual

        | Unify (typ, typ', patchable) ->
            let {coercion; residual} = unify pos env typ typ' in
            Option.iter (fun coercion -> patchable := coercion) coercion;
            residual
    in
    (match Option.bind residual (solve env) with
    | None -> ()
    | Some residual -> raise (TypeError (pos, Unsolvable residual)))

(* Public API *)

let solving_coercion pos env typ super =
    let {coercion; residual} = coercion pos env typ super in
    solve pos env residual;
    coercion

let solving_subtype pos env typ locator super =
    let {coercion; residual} = subtype pos env typ locator super in
    solve pos env residual;
    coercion

let solving_unify pos env typ super =
    let {coercion; residual} = unify pos env typ super in
    solve pos env residual;
    coercion

end

