open FcType
open FcTerm
open TypeError

(* HACK: Declaring these typer util types here: *)
type 'a with_pos = 'a Ast.with_pos

type 'a typing = {term : 'a; typ : FcType.typ; eff : Effect.t}

(* Newtype to allow ignoring subtyping coercions without partial application warning: *)
(* TODO: triv_expr with_pos -> expr with_pos to avoid bugs that would delay side effects
         or that duplicate large/nontrivial terms: *)
type coercer = Cf of (FcTerm.expr with_pos -> FcTerm.expr with_pos)

type 'a matching = {coercion : 'a; residual : Residual.t option}
(* /HACK *)

type val_binder =
    | WhiteDecl of Name.t Ast.Type.decl
    | GreyDecl of Name.t Ast.Type.decl
    | BlackDecl of lvalue * locator
    | WhiteDef of Ast.Term.lvalue * Ast.Term.expr with_pos
    | GreyDef of Ast.Term.lvalue * Ast.Term.expr with_pos
    | BlackAnn of lvalue * Ast.Term.expr with_pos * ov Vector.t * locator * coercion option
    | BlackUnn of lvalue * expr with_pos * Effect.t

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

let push_existential {scopes; current_level} =
    let bindings = ref [] in
    let current_level = current_level + 1 in
    ( {scopes = Existential (bindings, current_level) :: scopes; current_level}
    , bindings )

let generate env binding =
    let rec generate = function
        | Existential (bindings, level) :: _ ->
            bindings := binding :: !bindings;
            (binding, level)
        | _ :: scopes' -> generate scopes'
        | [] -> failwith "Typer.Env.generate: missing root Existential scope"
    in generate env.scopes

let push_domain_skolems ({scopes; current_level} as env) = function
    | Exists (existentials, locator, domain) ->
        let level = current_level + 1 in
        let skolems = Vector1.map (fun kind -> ((Name.fresh (), kind), level)) existentials in
        let substitution = Vector1.map (fun ov -> OvP ov) skolems in
        let skolems = Vector1.to_vector skolems in
        ( {scopes = Universal skolems :: scopes; current_level = level}
        , skolems, expose_locator substitution locator, expose substitution domain )
    | NoE domain -> (env, Vector.of_list [], Hole, domain)

let push_abs_skolems {scopes; current_level} (existentials, locator, body) =
    let level = current_level + 1 in
    let ebs = Vector1.map (fun kind -> (Name.fresh (), kind)) existentials in
    let skolems = Vector1.map (fun binding -> (binding, level)) ebs in
    let substitution = Vector1.map (fun ov -> OvP ov) skolems in
    ( { scopes = Universal (Vector1.to_vector skolems) :: scopes (* HACK: Universal *)
      ; current_level = level }
    , ebs, expose_locator substitution locator, expose substitution body )

let push_arrow_skolems {scopes; current_level} universals codomain_locator (domain, eff, codomain) =
    let level = current_level + 1 in
    let ubs = Vector1.map (fun kind -> (Name.fresh (), kind)) universals in
    let skolems = Vector1.map (fun binding -> (binding, level)) ubs in
    let substitution = Vector1.map (fun ov -> OvP ov) skolems in
    ( {scopes = Universal (Vector1.to_vector skolems) :: scopes; current_level = level}
    , Vector1.to_vector ubs
    , expose_locator substitution codomain_locator
    , (expose substitution domain, eff, expose_abs substitution codomain) )

let push_skolems {scopes; current_level} bindings =
    let level = current_level + 1 in
    let skolems = Vector.map (fun binding -> (binding, level)) (Vector1.to_vector bindings) in
    {scopes = Universal skolems :: scopes; current_level = level}

let uv {current_level = level; _} binding =
    ref (Unassigned (binding, level))

let push_domain env binding locator =
    {env with scopes = Fn (ref (BlackDecl (binding, locator))) :: env.scopes}

let push_sig env bindings =
    let bindings = Vector.fold_left (fun bindings ({name; _} as binding : Name.t Ast.Type.decl) ->
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

