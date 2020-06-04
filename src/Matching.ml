type 'a with_pos = 'a Ast.with_pos

module ResidualMonoid = struct
    include Monoid.OfSemigroup(Residual)

    let skolemized skolems m = Option.map (fun r -> Residual.Skolems (skolems, r)) m
end

module Make (C : TyperSigs.CHECKING) : TyperSigs.MATCHING = struct

open Residual
open FcType
open Effect
open FcTerm
open TypeError

type coercer = TyperSigs.coercer
type 'a matching = 'a TyperSigs.matching

(* # Articulation *)

let rec articulate pos = function
    | Uv uv as uv_typ -> fun template ->
        (match uv with
        | {contents = Assigned _} -> failwith "unreachable: `articulate` on assigned uv"
        | {contents = Unassigned (_, level)} ->
            (match template with
            | Pi _ ->
                let typ = Pi (Vector.of_list [], Hole, Uv (sibling uv), Impure, (NoE (Uv (sibling uv)))) in
                uv := Assigned typ;
                typ
            | Type _ ->
                let typ = Type (NoE (Uv (sibling uv))) in
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
            | Record _ -> raise (TypeError (pos, RecordArticulation template)) (* no can do without row typing *)
            | Use _ -> failwith "unreachable: `Use` as template of `articulate`"))
    | _ -> failwith "unreachable: `articulate` on non-uv"

and articulate_template pos = function
    | Uv uv -> fun template ->
        (match uv with
        | {contents = Assigned _} -> failwith "unreachable: `articulate` on assigned uv"
        | {contents = Unassigned _} ->
            (match template with
            | PiL (_, Impure, _) ->
                let typ = Pi (Vector.of_list [], Hole, Uv (sibling uv), Impure, (NoE (Uv (sibling uv)))) in
                uv := Assigned typ;
                typ
            | TypeL (UseP _) ->
                let typ = Type (NoE (Uv (sibling uv))) in
                uv := Assigned typ;
                typ
            | RecordL _ -> raise (TypeError (pos, RecordArticulationL template)))) (* no can do without row typing *)
    | _ -> failwith "unreachable: `articulate` on non-uv"

(* # Focalization *)

and focalize pos env typ (template : FcType.template) : coercer * typ = match (typ, template) with
    | (Uv uv, _) ->
        (match !uv with
        | Assigned typ -> focalize pos env typ template
        | Unassigned _ -> (Cf (fun v -> v), articulate_template pos typ template))
    | (Pi _, PiL _) | (Type _, TypeL _) -> (Cf (fun v -> v), typ)
    | (FcType.Record fields, RecordL req_fields) ->
        let {label; typ = _} = Vector.get req_fields 0 in
        (match Vector.find_opt (fun {label = label'; typ = _} -> label' = label) fields with
        | Some {label = _; typ = field_typ} -> (Cf (fun v -> v), Record (Vector.singleton {label; typ = field_typ}))
        | None -> raise (TypeError (pos, MissingField (typ, label))))

(* # Subtyping *)

and sub_eff pos eff eff' = match (eff, eff') with
    | (Pure, Pure) -> ()
    | (Pure, Impure) -> ()
    | (Impure, Pure) -> raise (TypeError (pos, SubEffect (eff, eff')))
    | (Impure, Impure) -> ()

and coercion pos (occ : bool) env (typ : FcType.typ) ((existentials, super_locator, super) : ov Vector.t * locator * typ)
        : coercer matching =
    match Vector1.of_vector existentials with
    | Some existentials ->
        let axiom_bindings = Vector1.map (fun (((name, _), _) as param) ->
            (Name.fresh (), param, Env.uv env name)
        ) existentials in
        let env = Env.push_axioms env axiom_bindings in
        let {coercion = Cf coerce; residual} = subtype pos occ env typ super_locator super in

        let axioms = Vector1.map (fun (axname, ((_, kind) as binding, _), impl) ->
            let rec axiomatize l r = function
                | ArrowK (domain, codomain) ->
                    let def = (Name.fresh (), domain) in
                    let l = FcType.App (l, Use def) in
                    let r = FcType.App (r, Use def) in
                    let (universals, l, r) = axiomatize l r codomain in
                    (def :: universals, l, r)
                | TypeK -> ([], l, r) in
            let (universals, l, r) = axiomatize (Use binding) (Uv impl) kind in
            (axname, Vector.of_list universals, l, r)
        ) axiom_bindings in
        { coercion = Cf (fun v -> {pos; v = Axiom (axioms, coerce v)})
        ; residual = Option.map (fun residual -> Residual.Axioms (axiom_bindings, residual)) residual }
    | None -> subtype pos occ env typ super_locator super

and subtype_abs pos (occ : bool) env (typ : abs) locator (super : abs) : coercer matching = match typ with
    | Exists (skolems, sub_locator, typ) ->
        let (env, skolems, _, typ) = Env.push_abs_skolems env (skolems, sub_locator, typ) in
        (match super with
        | Exists (existentials, super_locator, super) ->
            let (uvs, super_locator, super) =
                C.instantiate_abs env (existentials, super_locator, super) in

            let {coercion = Cf coerce; residual} =
                subtype pos occ env typ super_locator super in

            let impl = {name = Name.fresh (); typ} in
            let body = {Ast.pos; v = Pack ( Vector1.map (fun uv -> Uv uv) uvs
                                          , coerce {Ast.pos; v = Use impl} )} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized skolems residual }
        | NoE super ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ locator super in

            let impl = {name = Name.fresh (); typ} in
            let body = coerce {Ast.pos; v = Use impl} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized skolems residual })

    | NoE typ ->
        (match super with
        | Exists (existentials, super_locator, super) ->
            let (uvs, super_locator, super) =
                C.instantiate_abs env (existentials, super_locator, super) in

            let {coercion = Cf coerce; residual} = subtype pos occ env typ super_locator super in

            let uvs = Vector1.map (fun uv -> Uv uv) uvs in
            {coercion = Cf (fun v -> {pos; v = Pack (uvs, coerce v)}); residual}
        | NoE super -> subtype pos occ env typ locator super)

and subtype pos occ env typ locator super : coercer matching =
    let empty = ResidualMonoid.empty in
    let combine = ResidualMonoid.combine in

    let rec resolve_path typ path = match path with
        | AppP (path, arg) ->
            (match arg with
            | OvP ((param, _), _) -> resolve_path (FcType.Fn (param, typ)) path
            | _ -> failwith "unreachable: uv path in locator with non-ov arg")
        | UvP uv ->
            (match !uv with
            | Assigned _ -> ()
            | Unassigned (_, level) ->
                check_uv_assignee pos uv level typ;
                uv := Assigned typ)
        | OvP ov ->
            (match Env.get_implementation env ov with
            | Some (_, _, uv) -> resolve_path typ (UvP uv)
            | None -> ())
        | UseP _ -> failwith "unreachable: UseP in `resolve_path`" in

    let subtype_whnf typ locator super : coercer matching = match (typ, super) with
        | (Uv uv, _) ->
            (match !uv with
            | Assigned typ -> subtype pos occ env typ locator super
            | Unassigned _ -> subtype pos false env (articulate pos typ super) locator super)
        | (_, Uv uv) ->
            (match !uv with
            | Assigned super -> subtype pos occ env typ locator super
            | Unassigned _ -> subtype pos false env typ locator (articulate pos super typ))

        | ( Pi (universals, domain_locator, domain, eff, codomain)
          , Pi (universals', _, domain', eff', codomain') ) ->
            let q_codomain_locator = match locator with
                | PiL (locator_universals, _, codomain_locator) ->
                    (locator_universals, codomain_locator)
                | Hole -> (Vector.of_list [], Hole)
                | _ -> failwith "unreachable: function locator" in
            let (env, (_, codomain_locator), (universals', domain', eff', codomain')) =
                Env.push_arrow_skolems env q_codomain_locator (universals', domain', eff', codomain') in
            let (uvs, domain_locator, domain, eff, codomain) =
                C.instantiate_arrow env (universals, domain_locator, domain, eff, codomain) in

            let {coercion = Cf coerce_domain; residual = domain_residual} =
                subtype pos occ env domain' domain_locator domain in
            sub_eff pos eff eff';
            let {coercion = Cf coerce_codomain; residual = codomain_residual} =
                subtype_abs pos occ env codomain codomain_locator codomain' in

            let param = {name = Name.fresh (); typ = domain'} in
            let arg = coerce_domain {pos; v = Use param} in
            let arrows_residual = combine domain_residual codomain_residual in
            { coercion =
                Cf (fun v ->
                        let body = coerce_codomain {pos; v = App (v, Vector.map (fun uv -> Uv uv) uvs, arg)} in
                        {pos; v = Fn (universals', param, body)})
            ; residual =
                (match Vector1.of_vector universals' with
                | Some skolems -> ResidualMonoid.skolemized skolems arrows_residual
                | None -> arrows_residual) }

        | (FcType.Record fields, FcType.Record super_fields) ->
            let locator_fields = match locator with
                | RecordL fields -> fields
                | Hole -> Vector.of_list []
                | _ -> failwith "unreachable: record locator" in
            let selectee = {name = Name.fresh (); typ = typ} in
            let (fields, residual) = Vector.fold_left (fun (fields', residual) {label; typ = super} ->
                match Vector.find_opt (fun {label = label'; typ = _} -> label' = label) fields with
                | Some {label = _; typ} ->
                    let locator =
                        match Vector.find_opt (fun {label = label'; typ = _} -> label' = label) locator_fields with
                        | Some {label = _; typ = locator} -> locator
                        | None -> Hole in
                    let {coercion = Cf coerce; residual = field_residual} = subtype pos occ env typ locator super in
                    ( {label; expr = coerce {pos; v = Select ({pos; v = Use selectee}, label)}} :: fields'
                    , combine residual field_residual )
                | None -> raise (TypeError (pos, MissingField (typ, label)))
            ) ([], empty) super_fields in
            let fields = Vector.of_list (List.rev fields) in (* OPTIMIZE *)
            { coercion =
                Cf (fun v -> {pos; v = Letrec (Vector1.singleton (pos, selectee, v), {pos; v = Record fields})})
            ; residual }

        | (Type carrie, Type carrie') ->
            (match locator with
            | TypeL path ->
                (match carrie with
                | NoE impl ->
                    let (decidable, impl, _) = C.whnf env impl in
                    if decidable then begin
                        resolve_path impl path;
                        {coercion = Cf (fun _ -> {v = Proxy carrie'; pos}); residual = empty}
                    end else failwith "todo"
                | Exists _ -> raise (TypeError (pos, Polytype carrie)))
            | Hole -> (* TODO: Use unification (?) *)
                let {Env.coercion = _; residual} = subtype_abs pos occ env carrie Hole carrie' in
                let {Env.coercion = _; residual = residual'} = subtype_abs pos occ env carrie Hole carrie' in
                { coercion = Cf (fun _ -> {v = Proxy carrie'; pos})
                ; residual = combine residual residual' }
            | _ -> failwith "unreachable: type proxy locator")

        | (App _, App _) | (Ov _, Ov _) ->
            let {Env.coercion; residual} = unify_whnf pos env typ super in
            { coercion =
                (match coercion with
                | Some co -> Cf (fun v -> {pos; v = Cast (v, co)})
                | None -> Cf Fun.id)
            ; residual }

        | (Int, Int) | (Bool, Bool) -> {coercion = Cf Fun.id; residual = empty}

        | (Fn _, _) | (_, Fn _) -> failwith "unreachable: Fn in subtype_whnf"
        | (Use _, _) | (_, Use _) -> failwith "unreachable: Use in subtype_whnf"
        | _ -> raise (TypeError (pos, SubType (typ, super))) in

    let (decidable, typ', co) = C.whnf env typ in
    let (decidable', super', co') = C.whnf env super in
    if decidable && decidable' then begin
        let {coercion = Cf coerce; residual} = subtype_whnf typ' locator super' in
        { coercion =
            (match (co, co') with
            | (Some co, Some co') ->
                Cf (fun v -> {pos; v = Cast (coerce {pos; v = Cast (v, co)}, Symm co')})
            | (Some co, None) -> Cf (fun v -> coerce {pos; v = Cast (v, co)})
            | (None, Some co') -> Cf (fun v -> {pos; v = Cast (coerce v, Symm co')})
            | (None, None) -> Cf coerce)
        ; residual }
    end else begin
        let patchable = ref {Ast.pos; v = Const (Int 0)} in
        { coercion = Cf (fun v ->
            patchable := v;
            {pos; v = Patchable patchable})
        ; residual = Some (Sub (occ, typ, locator, super, patchable)) }
    end

(* # Unification *)

and unify_abs pos env typ typ' : coercion option matching = match (typ, typ') with
    | (NoE typ, NoE typ') -> unify pos env typ typ'

and unify pos env typ typ' : coercion option matching =
    let (decidable, typ, co) = C.whnf env typ in
    let (decidable', typ', co'') = C.whnf env typ' in
    if decidable && decidable' then begin
        let {Env.coercion = co'; residual} = unify_whnf pos env typ typ' in
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
        ; residual }
    end else begin
        let patchable = ref (Refl typ') in
        { coercion = Some (FcType.Patchable patchable)
        ; residual = Some (Unify (typ, typ', patchable)) }
    end

and unify_whnf pos env (typ : typ) (typ' : typ) : coercion option matching =
    let open ResidualMonoid in
    match (typ, typ') with
    | (Uv uv, _) ->
        (match !uv with
        | Assigned typ -> unify_whnf pos env typ typ'
        | Unassigned (_, level) ->
            check_uv_assignee pos uv level typ';
            uv := Assigned typ';
            {coercion = None; residual = empty})
    | (_, Uv uv) ->
        (match !uv with
        | Assigned typ' -> unify_whnf pos env typ typ'
        | Unassigned (_, level) ->
            check_uv_assignee pos uv level typ;
            uv := Assigned typ;
            {coercion = None; residual = empty})
    | (Type carrie, Type carrie') ->
        let {Env.coercion; residual} = unify_abs pos env carrie carrie' in
        { coercion =
            (match coercion with
            | Some co -> Some (TypeCo co)
            | None -> None)
        ; residual }
    | (FcType.App (callee, arg), FcType.App (callee', arg')) ->
        let {Env.coercion = callee_co; residual} = unify_whnf pos env callee callee' in
        let {Env.coercion = arg_co; residual = residual'} = unify pos env arg arg' in
        { coercion =
            (match (callee_co, arg_co) with
            | (Some callee_co, Some arg_co) -> Some (Comp (callee_co, arg_co))
            | (Some callee_co, None) -> Some (Comp (callee_co, Refl arg'))
            | (None, Some arg_co) -> Some (Comp (Refl callee', arg_co))
            | (None, None) -> None)
        ; residual = combine residual residual' }
    | (Ov ov, Ov ov')->
        if ov = ov'
        then {coercion = None; residual = empty}
        else raise (TypeError (pos, Unify (typ, typ')))
    | (Int, Int) | (Bool, Bool) -> {coercion = None; residual = empty}
    | (Fn _, _) | (_, Fn _) -> failwith "unreachable: Fn in unify_whnf"

and check_uv_assignee_abs pos uv level : FcTerm.abs -> unit = function
    | NoE typ -> check_uv_assignee pos uv level typ
    | Exists _ as typ -> raise (TypeError (pos, Polytype typ)) (* not a monotype *)

(* FIXME: need to use `whnf` like subtype and unify do: *)
(* Monotype check, occurs check, ov escape check and uv level updates. Complected for speed. *)
and check_uv_assignee pos uv level typ =
    let check = function
        | Uv uv' ->
            if uv = uv'
            then raise (TypeError (pos, Occurs (uv, typ))) (* occurs *)
            else
                (match !uv' with
                | Assigned typ -> check_uv_assignee pos uv level typ
                | Unassigned (name, level') ->
                    if level' <= level
                    then ()
                    else uv' := Unassigned (name, level)) (* hoist *)
        | Ov ((_, level') as ov) -> (* FIXME: need to try and get impl!: *)
            if level' <= level
            then ()
            else raise (TypeError (pos, Escape ov)) (* ov would escape *)
        | Fn (param, body) -> ()
            (* FIXME: check_uv_assignee pos uv level body *)
        | Pi (universals, _, domain, _, codomain) ->
            if Vector.length universals = 0
            then begin
                check_uv_assignee pos uv level domain;
                check_uv_assignee_abs pos uv level codomain
            end
            else raise (TypeError (pos, Polytype (NoE typ))) (* not a monotype *)
        | Record fields ->
            Vector.iter (fun {label = _; typ} -> check_uv_assignee pos uv level typ) fields
        | Type carrie -> check_uv_assignee_abs pos uv level carrie
        | App (callee, arg) ->
            check_uv_assignee pos uv level callee;
            check_uv_assignee pos uv level arg
        | Int | Bool -> ()
        | Use _ -> failwith "unreachable: `Use` in `check_uv_assignee`"
    in check typ

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

        | Sub (occ, typ, locator, super, patchable) ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ locator super in
            patchable := coerce (!patchable);
            residual

        | Unify (typ, typ', patchable) ->
            let {Env.coercion; residual} = unify pos env typ typ' in
            Option.iter (fun coercion -> patchable := coercion) coercion;
            residual
    in
    (match Option.bind residual (solve env) with
    | None -> ()
    | Some residual -> raise (TypeError (pos, Unsolvable residual)))
end

