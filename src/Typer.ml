let (^/^) = PPrint.(^/^)

open FcType
open Effect
open FcTerm

type abs = FcType.abs
type typ = FcType.t
type locator = FcType.locator
type ov = FcType.ov
type uv = FcType.uv
type effect = FcType.Effect.t
type 'a with_pos = 'a Ast.with_pos

type 'a typing = {term : 'a; typ : FcType.typ; eff : effect}

(* Newtype to allow ignoring subtyping coercions without partial application warning: *)
(* TODO: triv_expr with_pos -> expr with_pos to avoid bugs that would delay side effects
         or that duplicate large/nontrivial terms: *)
type coercer = Cf of (expr with_pos -> expr with_pos)

module Residual = Residual(struct type t = expr end)

type residual = Residual.t

module ResidualMonoid = struct
    include Monoid.OfSemigroup(Residual)

    let skolemized skolems m = Option.map (fun r -> Skolems (skolems, r)) m
end

type 'a matching = {coercion : 'a; residual : residual option}

type error =
    | Unbound of Name.t
    | MissingField of typ * string
    | SubEffect of effect * effect
    | SubType of typ * typ
    | Unify of typ * typ
    | ImpureType of Ast.Term.expr
    | Escape of ov
    | Occurs of uv * typ
    | Polytype of abs
    | PolytypeInference of abs
    | RecordArticulation of typ
    | RecordArticulationL of locator

exception TypeError of span * error

let type_error_to_doc (({pos_fname; _}, _) as span : Ast.span) err =
    PPrint.prefix 4 1 (PPrint.string "Type error in" ^/^ PPrint.string pos_fname ^/^ PPrint.string "at"
        ^/^ PPrint.string (Ast.span_to_string span) ^/^ PPrint.colon)
    (match err with
    | Unbound name -> PPrint.string "unbound name" ^/^ Name.to_doc name
    | MissingField (typ, label) -> FcType.to_doc typ ^/^ PPrint.string "is missing field" ^/^ PPrint.string label
    | SubEffect (eff, eff') -> Ast.Effect.to_doc eff ^/^ PPrint.string "is not a subeffect of" ^/^ Ast.Effect.to_doc eff'
    | SubType (typ, super) -> FcType.to_doc typ ^/^ PPrint.string "is not a subtype of" ^/^ FcType.to_doc super
    | Unify (typ, typ') -> FcType.to_doc typ ^/^ PPrint.string "does no unify with" ^/^ FcType.to_doc typ'
    | ImpureType expr -> PPrint.string "impure type expression" ^/^ Ast.Term.expr_to_doc expr
    | Escape ((name, _), _) -> Name.to_doc name ^/^ PPrint.string "would escape"
    | Occurs (uv, typ) -> FcType.to_doc (Uv uv) ^/^ PPrint.string "occurs in" ^/^ FcType.to_doc typ
    | Polytype typ -> FcType.abs_to_doc typ ^/^ PPrint.string "is not a monotype"
    | PolytypeInference typ -> PPrint.string "tried to infer polytype" ^/^ FcType.abs_to_doc typ
    | RecordArticulation typ ->
        PPrint.string "tried to articulate record type" ^/^ FcType.to_doc typ
    | RecordArticulationL typ ->
        PPrint.string "tried to articulate record type" ^/^ FcType.locator_to_doc typ)

module Env = struct
    type val_binder =
        | WhiteDecl of Ast.Type.decl
        | GreyDecl of Ast.Type.decl
        | BlackDecl of lvalue * locator
        | WhiteDef of Ast.Term.lvalue * Ast.Term.expr with_pos
        | GreyDef of Ast.Term.lvalue * Ast.Term.expr with_pos
        | BlackAnn of lvalue * Ast.Term.expr with_pos * ov Vector.t * locator * coercion option
        | BlackUnn of lvalue * expr with_pos * effect

    type scope
        = Repl of (Name.t, val_binder ref) Hashtbl.t
        | Existential of binding list ref * level
        | Universal of ov Vector.t
        | Axiom of (Name.t * ov * uv) Name.Map.t
        | Fn of val_binder ref
        | Sig of val_binder ref Name.Map.t
        | Struct of val_binder ref Name.Map.t

    type t = {scopes : scope list; current_level : level}

    let initial_level = 1

    let interactive () =
        { scopes = [Repl (Hashtbl.create 0); Existential (ref [], initial_level)]
        ; current_level = initial_level }

    let repl_define env ({name; _} as binding) =
        let rec define scopes =
            match scopes with
            | Repl kvs :: _ -> Hashtbl.replace kvs name (ref (BlackDecl (binding, Hole)))
            | _ :: scopes' -> define scopes'
            | [] -> failwith "Typer.Env.repl_define: non-interactive type environment"
        in define env.scopes

    let with_incremented_level ({current_level; _} as env) body =
        body {env with current_level = current_level + 1}

    let with_existential ({scopes; current_level} as env) f =
        with_incremented_level env (fun ({current_level; _} as env) ->
            let bindings = ref [] in
            f {env with scopes = Existential (bindings, current_level) :: scopes} bindings
        )

    let generate env binding =
        let rec generate = function
            | Existential (bindings, level) :: _ ->
                bindings := binding :: !bindings;
                (binding, level)
            | _ :: scopes' -> generate scopes'
            | [] -> failwith "Typer.Env.generate: missing root Existential scope"
        in generate env.scopes

    let skolemizing_domain ({scopes; current_level} as env) domain f = match domain with
        | Exists (existentials, locator, domain) ->
            with_incremented_level env (fun ({current_level = level; _} as env) ->
                let skolems = Vector.map (fun binding -> (binding, level)) (Vector1.to_vector existentials) in
                let substitution = Vector.fold_left (fun substitution (((name, _), _) as skolem) ->
                    Name.Map.add name (OvP skolem) substitution
                ) Name.Map.empty skolems in
                f {env with scopes = Universal skolems :: scopes}
                  (skolems, substitute_locator substitution locator, substitute substitution domain)
            )
        | NoE domain -> f env (Vector.of_list [], Hole, domain)

    let skolemizing_abs ({scopes; current_level} as env) (existentials, locator, body) f =
        with_incremented_level env (fun ({current_level = level; _} as env) ->
            let existentials' = Vector1.map FcType.freshen existentials in
            let skolems = Vector1.map (fun binding -> (binding, level)) existentials' in
            let substitution = Vector1.fold_left (fun substitution (((name, _), _) as skolem) ->
                Name.Map.add name (OvP skolem) substitution
            ) Name.Map.empty skolems in
            f {env with scopes = Existential (ref (Vector1.to_list existentials'), level) :: scopes}
              (existentials', substitute_locator substitution locator, substitute substitution body)
        )

    let skolemizing_arrow ({scopes; current_level} as env) (universals, domain, eff, codomain) f =
        with_incremented_level env (fun ({current_level = level; _} as env) ->
            let universals' = Vector.map FcType.freshen universals in
            let skolems = Vector.map (fun binding -> (binding, level)) universals' in
            let substitution = Vector.fold_left2 (fun substitution (name, _) skolem ->
                Name.Map.add name (OvP skolem) substitution
            ) Name.Map.empty universals skolems in
            f {env with scopes = Universal skolems :: scopes}
              (universals', substitute substitution domain, eff, substitute_abs substitution codomain)
        )

    let skolemizing_located_arrow ({scopes; current_level} as env)
            (locator_universals, codomain_locator) (universals, domain, eff, codomain) f =
        with_incremented_level env (fun ({current_level = level; _} as env) ->
            let universals' = Vector.map FcType.freshen universals in
            let skolems = Vector.map (fun binding -> (binding, level)) universals' in
            let substitution = Vector.fold_left2 (fun substitution (name, _) skolem ->
                Name.Map.add name (OvP skolem) substitution
            ) Name.Map.empty universals skolems in
            let locator_substitution = Vector.fold_left2 (fun substitution (name, _) skolem ->
                Name.Map.add name (OvP skolem) substitution
            ) Name.Map.empty locator_universals skolems in
            f {env with scopes = Universal skolems :: scopes}
              (universals', substitute_locator locator_substitution codomain_locator)
              (universals', substitute substitution domain, eff, substitute_abs substitution codomain)
        )

    let preskolemized ({scopes; current_level} as env) universals f =
        with_incremented_level env (fun ({current_level = level; _} as env) ->
            let bindings = Vector.map (fun (FcType.Use binding) -> binding) universals in
            let skolems = Vector.map (fun binding -> (binding, level)) bindings in
            f {env with scopes = Universal skolems :: scopes} bindings
        )

    let uv {current_level = level; _} binding =
        ref (Unassigned (binding, level))

    let push_domain env binding locator =
        {env with scopes = Fn (ref (BlackDecl (binding, locator))) :: env.scopes}

    let push_sig env bindings =
        let bindings = Vector.fold_left (fun bindings ({name; _} as binding : Ast.Type.decl) ->
            Name.Map.add name (ref (WhiteDecl binding)) bindings
        ) Name.Map.empty bindings in
        {env with scopes = Sig bindings :: env.scopes}

    let push_struct env bindings =
        let bindings = Vector.fold_left (fun bindings ({Ast.Term.pat = name; _} as binding, expr) ->
            Name.Map.add name (ref (WhiteDef (binding, expr))) bindings
        ) Name.Map.empty bindings in
        {env with scopes = Struct bindings :: env.scopes}

    let push_axioms env axioms =
        let bindings = Vector1.fold_left (fun bindings ((_, ((k, _), _), _) as v) ->
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
            | [] -> raise (TypeError (pos, Unbound name))
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
        Env.skolemizing_domain env domain (fun env (universals, domain_locator, domain) ->
            let env = Env.push_domain env {name; typ = domain} domain_locator in
            Env.with_existential env (fun env existentials ->
                let {term = body; typ = codomain; eff} = typeof env body in

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
            )
        )

    | Ast.Term.App (callee, arg) -> (* TODO: Support "dynamic" sealing of `if`-arg? *)
        let {term = callee_expr; typ = callee_typ; eff = callee_eff} = typeof env callee in
        let callee = {name = Name.fresh (); typ = callee_typ} in
        (match focalize callee_expr.pos env callee_typ (PiL (Vector.of_list [], Impure, Hole)) with
        | (coerce, Pi (universals, locator, domain, app_eff, codomain)) ->
            let (uvs, domain_locator, domain, app_eff, codomain) =
                instantiate_arrow env (universals, locator, domain, app_eff, codomain) in
            
            let {term = arg; typ = _; eff = arg_eff} = check env (NoE domain) arg in

            let term =
                { Ast.pos = callee_expr.pos
                ; v = Letrec ( Vector1.singleton (callee_expr.pos, callee, callee_expr)
                             , {expr with v = App ( coerce {expr with v = Use callee}
                                                  , Vector.map (fun uv -> Uv uv) uvs, arg )} ) } in
            let eff = join_effs (join_effs callee_eff arg_eff) app_eff in
            (match codomain with
            | Exists (existentials, codomain_locator, concr_codo) ->
                Env.skolemizing_abs env (existentials, codomain_locator, concr_codo)
                    (fun env (existentials, codomain_locator, concr_codo) ->
                        let (_, _, res_typ) as typ = reabstract env codomain in
                        let {coercion = Cf coerce; residual} = coercion expr.pos true env concr_codo typ in

                        let def = {name = Name.fresh (); typ = concr_codo} in
                        { term = {term with v = Unpack (existentials, def, term, coerce {expr with v = Use def})}
                        ; typ = res_typ
                        ; eff = Impure }
                    )
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
        let {term = record; typ = record_typ; eff} = typeof env record in
        let label = Name.to_string label in
        let shape = FcType.RecordL (Vector.singleton {label; typ = Hole}) in
        (match focalize record.pos env record_typ shape with
        | (coerce, Record fields) ->
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
        let {term = (pos, ({name; _} as lvalue), _) as def; typ; eff = field_eff} = deftype env field in
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
        let {term = cond; eff = cond_eff} = check env (NoE Bool) cond in
        let {term = conseq; eff = conseq_eff} = implement env typ conseq in
        let {term = alt; eff = alt_eff} = implement env typ alt in
        { term = {expr with v = If (cond, conseq, alt)}
        ; typ = body
        ; eff = join_effs cond_eff (join_effs conseq_eff alt_eff) }
    | _ ->
        let {term; typ = expr_typ; eff} = typeof env expr in
        let lvalue = {name = Name.fresh (); typ = expr_typ} in
        let {coercion = Cf coerce; residual} = coercion expr.pos true env expr_typ typ in
        { term = {expr with v = Letrec ( Vector1.singleton (expr.pos, lvalue, term)
                                       , coerce {expr with v = Use lvalue} )}
        ; typ = body; eff}

(* # Definitions and Statements *)

and deftype env (pos, {Ast.Term.pat = name; _}, _) = (* FIXME: When GreyDecl has been encountered *)
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
            Env.skolemizing_domain env domain (fun env (universals, domain_locator, domain) ->
                let name = match name with
                    | Some name -> name
                    | None -> Name.fresh () in
                let env = Env.push_domain env {name; typ = domain} domain_locator in

                let universals = Vector.map fst universals in
                match (eff, kindcheck env codomain) with
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
                    , Pi (universals, domain_locator, domain, eff, codomain) )
            )
        | Ast.Type.Sig decls ->
            let env = Env.push_sig env decls in
            let (locators, decls) = Vector.split (Vector.map (elaborate_decl env) decls) in
            (RecordL locators, Record decls)
        | Ast.Type.Path expr ->
            (match typeof env {typ with v = expr} with
            | {term = _; typ = proxy_typ; eff = Pure} ->
                (match focalize typ.pos env proxy_typ (TypeL (UseP (Name.fresh (), TypeK))) with
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
        ({label; typ = locator}, {label; typ})
    in
    Env.with_existential env (fun env params ->
        let (locator, typ) = elaborate env typ in
        match Vector1.of_list (!params) with
        | Some params -> Exists (params, locator, typ)
        | None -> NoE typ
    )

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
        | (Pi _ | IPi _ | Record _ | Type _ | Int | Bool) as typ -> (true, typ, None)
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
                let _ = unify pos env typ typ' in
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
                let {coercion = co; residual} = unify pos env typ typ' in
                binding := Env.BlackAnn (lvalue, expr, existentials, locator, co);
                (Hole, lvalue)
            | _ -> raise (TypeError (pos, PolytypeInference typ)))
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
            let {coercion = Cf coerce; residual} = subtype expr.pos true env typ Hole typ' in
            binding := Env.BlackUnn (lvalue, coerce expr, eff); (* FIXME: Coercing nontrivial `expr` *)
            (Hole, lvalue)
        | _ -> failwith "unreachable: non-unn from unn `lookup`")
    | (env, ({contents = Env.GreyDef ({pat = name; ann = _}, expr)} as binding)) ->
        let lvalue = {name; typ = Uv (Env.uv env (Name.fresh ()))} in (* FIXME: uv level is wrong *)
        binding := Env.BlackAnn (lvalue, expr, Vector.of_list [], Hole, None);
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
        | {contents = Unassigned (_, level)} ->
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

and focalize pos env typ (template : FcType.template) = match (typ, template) with
    | (Uv uv, _) ->
        (match !uv with
        | Assigned typ -> focalize pos env typ template
        | Unassigned _ -> ((fun v -> v), articulate_template pos typ template))
    | (Pi _, PiL _) | (Type _, TypeL _) -> ((fun v -> v), typ)
    | (FcType.Record fields, RecordL req_fields) ->
        let {label; typ = _} = Vector.get req_fields 0 in
        (match Vector.find_opt (fun {label = label'; typ = _} -> label' = label) fields with
        | Some {label = _; typ = field_typ} -> ((fun v -> v), Record (Vector.singleton {label; typ = field_typ}))
        | None -> raise (TypeError (pos, MissingField (typ, label))))

(* # Subtyping *)

and sub_eff pos eff eff' = match (eff, eff') with
    | (Pure, Pure) -> ()
    | (Pure, Impure) -> ()
    | (Impure, Pure) -> raise (TypeError (pos, SubEffect (eff, eff')))
    | (Impure, Impure) -> ()

and coercion pos (occ : bool) env (typ : FcType.typ) ((existentials, super_locator, super) : ov Vector.t * locator * typ) =
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
        {coercion = Cf (fun v -> {pos; v = Axiom (axioms, coerce v)}); residual}
    | None -> subtype pos occ env typ super_locator super

and subtype_abs pos (occ : bool) env (typ : abs) locator (super : abs) : coercer matching = match typ with
    | Exists (skolems, sub_locator, typ) ->
        Env.skolemizing_abs env (skolems, sub_locator, typ)
            (fun env (skolems, _, typ) ->
                match super with
                | Exists (existentials, super_locator, super) ->
                    let (uvs, super_locator, super) =
                        instantiate_abs env (existentials, super_locator, super) in

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
                    ; residual = ResidualMonoid.skolemized skolems residual }
            )
    | NoE typ ->
        (match super with
        | Exists (existentials, super_locator, super) ->
            let (uvs, super_locator, super) =
                instantiate_abs env (existentials, super_locator, super) in

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
        | UseP _ -> () in

    let rec subtype_whnf typ locator super : coercer matching = match (typ, super) with
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
            Env.skolemizing_located_arrow env q_codomain_locator (universals', domain', eff', codomain')
                (fun env (locator_universals, codomain_locator) (universals', domain', eff', codomain') ->
                    let (uvs, domain_locator, domain, eff, codomain) =
                        instantiate_arrow env (universals, domain_locator, domain, eff, codomain) in

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
                )

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
                    let (decidable, impl, _) = whnf pos env impl in
                    if decidable then begin
                        resolve_path impl path;
                        {coercion = Cf (fun _ -> {v = Proxy carrie'; pos}); residual = empty}
                    end else failwith "todo"
                | Exists _ -> raise (TypeError (pos, Polytype carrie)))
            | Hole -> (* TODO: Use unification (?) *)
                let {coercion = _; residual} = subtype_abs pos occ env carrie Hole carrie' in
                let {coercion = _; residual = residual'} = subtype_abs pos occ env carrie Hole carrie' in
                { coercion = Cf (fun _ -> {v = Proxy carrie'; pos})
                ; residual = combine residual residual' }
            | _ -> failwith "unreachable: type proxy locator")

        | (App _, App _) | (Ov _, Ov _) ->
            let {coercion; residual} = unify_whnf pos env typ super in
            { coercion =
                (match coercion with
                | Some co -> Cf (fun v -> {pos; v = Cast (v, co)})
                | None -> Cf Fun.id)
            ; residual }

        | (Int, Int) | (Bool, Bool) -> {coercion = Cf Fun.id; residual = empty}

        | (Fn _, _) | (_, Fn _) -> failwith "unreachable: Fn in subtype_whnf"
        | (Use _, _) | (_, Use _) -> failwith "unreachable: Use in subtype_whnf"
        | _ -> raise (TypeError (pos, SubType (typ, super))) in

    let (decidable, typ, co) = whnf pos env typ in
    let (decidable', super, co') = whnf pos env super in
    if decidable && decidable' then begin
        let {coercion = Cf coerce; residual} = subtype_whnf typ locator super in
        { coercion =
            (match (co, co') with
            | (Some co, Some co') ->
                Cf (fun v -> {pos; v = Cast (coerce {pos; v = Cast (v, co)}, Symm co')})
            | (Some co, None) -> Cf (fun v -> coerce {pos; v = Cast (v, co)})
            | (None, Some co') -> Cf (fun v -> {pos; v = Cast (coerce v, Symm co')})
            | (None, None) -> Cf coerce)
        ; residual }
    end else failwith "todo"

and unify_abs pos env typ typ' : coercion option matching = match (typ, typ') with
    | (NoE typ, NoE typ') -> unify pos env typ typ'

and unify pos env typ typ' : coercion option matching =
    let (decidable, typ, co) = whnf pos env typ in
    let (decidable', typ', co'') = whnf pos env typ' in
    if decidable && decidable' then begin
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
        ; residual }
    end else failwith "todo"

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
        let {coercion; residual} = unify_abs pos env carrie carrie' in
        { coercion =
            (match coercion with
            | Some co -> Some (TypeCo co)
            | None -> None)
        ; residual }
    | (FcType.App (callee, arg), FcType.App (callee', arg')) ->
        let {coercion = callee_co; residual} = unify_whnf pos env callee callee' in
        let {coercion = arg_co; residual = residual'} = unify pos env arg arg' in
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

(* Monotype check, occurs check, ov escape check and uv level updates. Complected for speed. *)
and check_uv_assignee pos uv level typ =
    let rec check = function
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
        | Ov ((_, level') as ov) ->
            if level' <= level
            then ()
            else raise (TypeError (pos, Escape ov)) (* ov would escape *)
        | Fn (param, body) -> ()
            (* FIXME: check_uv_assignee pos uv level body *)
        | Pi (universals, domain_locator, domain, _, codomain) ->
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

(* # REPL support *)

let check_interaction env : Ast.Term.stmt -> stmt typing = function
    | Ast.Term.Def ((_, ({pat = name; _} as lvalue), expr) as def) ->
        let env = Env.push_struct env (Vector.singleton (lvalue, expr)) in
        let {term; typ; eff} = deftype env def in
        Env.repl_define env {name; typ};
        {term = Def term; typ; eff}
    | Ast.Term.Expr expr ->
        let {term; typ; eff} = typeof env expr in
        {term = Expr term; typ; eff}

