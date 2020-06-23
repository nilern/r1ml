open FcType
open FcTerm
open TypeError

type 'a with_pos = 'a Ast.with_pos

type val_binder =
    | WhiteDecl of Name.t * Ast.Type.t with_pos
    | GreyDecl of Name.t * Ast.Type.t with_pos
    | BlackDecl of lvalue * ov Vector.t * locator
    | WhiteDef of Name.t * Ast.Term.expr with_pos
    | GreyDef of Name.t * Ast.Term.expr with_pos
    | BlackDef of lvalue * Effect.t * expr with_pos

type scope
    = Repl of (Name.t, val_binder ref) Hashtbl.t
    | Hoisting of binding list ref * level
    | Rigid of ov Vector.t
    | Axiom of (Name.t * ov * uv) Name.Map.t
    | Fn of val_binder ref
    | Rec of val_binder ref Name.Map.t

type t = {scopes : scope list; current_level : level}

let initial_level = 1

let interactive () =
    { scopes = [Repl (Hashtbl.create 0); Hoisting (ref [], initial_level)]
    ; current_level = initial_level }

let repl_define env ({name; typ = _} as lvalue) =
    let rec define scopes =
        match scopes with
        | Repl kvs :: _ -> Hashtbl.replace kvs name (ref (BlackDecl (lvalue, Vector.of_list [], Hole)))
        | _ :: scopes' -> define scopes'
        | [] -> failwith "Typer.Env.repl_define: non-interactive type environment"
    in define env.scopes

let push_existential {scopes; current_level} =
    let bindings = ref [] in
    let current_level = current_level + 1 in
    ( {scopes = Hoisting (bindings, current_level) :: scopes; current_level}
    , bindings )

let generate env binding =
    let rec generate = function
        | Hoisting (bindings, level) :: _ ->
            bindings := binding :: !bindings;
            (binding, level)
        | _ :: scopes' -> generate scopes'
        | [] -> failwith "Typer.Env.generate: missing root Hoisting scope"
    in generate env.scopes

let reabstract env (Exists (params, locator, body)) =
    let params' = Vector.map (fun kind -> generate env (Name.fresh (), kind)) params in
    let substitution = Vector.map (fun ov -> Ov ov) params' in
    (params', expose_locator substitution locator, expose substitution body)

let push_domain_skolems {scopes; current_level} (Exists (existentials, locator, domain)) =
    let level = current_level + 1 in
    let skolems = Vector.map (fun kind -> ((Name.fresh (), kind), level)) existentials in
    let substitution = Vector.map (fun ov -> Ov ov) skolems in
    ( {scopes = Rigid skolems :: scopes; current_level = level}
    , skolems, expose_locator substitution locator, expose substitution domain )

let push_abs_skolems {scopes; current_level} (existentials, locator, body) =
    let level = current_level + 1 in
    let ebs = Vector.map (fun kind -> (Name.fresh (), kind)) existentials in
    let skolems = Vector.map (fun binding -> (binding, level)) ebs in
    let substitution = Vector.map (fun ov -> Ov ov) skolems in
    ( { scopes = Rigid skolems :: scopes
      ; current_level = level }
    , ebs, expose_locator substitution locator, expose substitution body )

let push_arrow_skolems {scopes; current_level} universals domain eff codomain_locator codomain =
    let level = current_level + 1 in
    let ubs = Vector.map (fun kind -> (Name.fresh (), kind)) universals in
    let skolems = Vector.map (fun binding -> (binding, level)) ubs in
    let substitution = Vector.map (fun ov -> Ov ov) skolems in
    ( {scopes = Rigid skolems :: scopes; current_level = level}
    , ubs, expose substitution domain, eff
    , expose_locator substitution codomain_locator, expose_abs substitution codomain )

let push_skolems {scopes; current_level} bindings =
    let level = current_level + 1 in
    let skolems = Vector.map (fun binding -> (binding, level)) (Vector1.to_vector bindings) in
    {scopes = Rigid skolems :: scopes; current_level = level}

let uv {current_level = level; _} binding =
    ref (Unassigned (binding, level))

let instantiate_abs env (existentials, locator, body) =
    let uvs = Vector.map (fun _ -> uv env (Name.fresh ())) existentials in
    let substitution = Vector.map (fun uv -> Uv uv) uvs in
    (uvs, expose_locator substitution locator, expose substitution body)

let instantiate_arrow env universals domain_locator domain eff codomain =
    let uvs = Vector.map (fun _ -> uv env (Name.fresh())) universals in
    let substitution = Vector.map (fun uv -> Uv uv) uvs in
    ( uvs, expose_locator substitution domain_locator, expose substitution domain, eff
    , expose_abs substitution codomain )

let push_domain env lvalue locator =
    {env with scopes = Fn (ref (BlackDecl (lvalue, Vector.of_list [], locator))) :: env.scopes}

let push_sig env bindings =
    let bindings = Vector.fold_left (fun bindings {Ast.Type.name; typ} ->
        Name.Map.add name (ref (WhiteDecl (name, typ))) bindings
    ) Name.Map.empty bindings in
    {env with scopes = Rec bindings :: env.scopes}

let push_struct env bindings =
    let bindings = Vector.fold_left (fun bindings -> function
        | ({Ast.Term.pat = name; ann = Some typ}, _) ->
            Name.Map.add name (ref (WhiteDecl (name, typ))) bindings
        | ({Ast.Term.pat = name; ann = None}, expr) ->
            Name.Map.add name (ref (WhiteDef (name, expr))) bindings
    ) Name.Map.empty bindings in
    {env with scopes = Rec bindings :: env.scopes}

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
        | Fn ({contents = BlackDecl ({name = name'; typ = _}, _, _)} as def) :: scopes' ->
            if name' = name
            then ({env with scopes}, def)
            else get scopes'
        | Fn _ :: _ -> failwith "unreachable: Fn scope with non-BlackDecl in `Env.get`"
        | Rec kvs :: scopes' ->
            (match Name.Map.find_opt name kvs with
            | Some def -> ({env with scopes}, def)
            | None -> get scopes')
        | (Hoisting _ | Rigid _ | Axiom _) :: scopes' -> get scopes'
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

