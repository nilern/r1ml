type kind
    = ArrowK of kind * kind
    | TypeK

type effect = Ast.effect

type level = int

type binding = Name.t * kind

type ov = binding * level

type uvv =
    | Unassigned of Name.t * level
    | Assigned of typ

and uv = uvv ref

and abs = binding list * locator * t

and t =
    | Pi of binding list * locator * t * effect * abs
    | IPi of t list * t * effect * abs
    | Record of t field list
    | Fn of Name.t * t
    | App of t * t
    | Type of abs
    | Use of binding
    | Ov of ov
    | Uv of uv
    | Int
    | Bool

and locator =
    | PiL of binding list * effect * locator
    | RecordL of locator field list
    | TypeL of path
    | Hole

and 'a field = {label : string; typ : 'a}

and path =
    | AppP of path * path
    | OvP of ov
    | UvP of uv
    | UseP of binding

and coercion =
    | Refl of typ
    | Symm of coercion
    | Trans of coercion * coercion
    | Comp of coercion * coercion
    | Inst of coercion * typ
    | AUse of Name.t
    | TypeCo of coercion

and typ = t
and template = t

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec kind_to_doc = function
    | ArrowK (domain, codomain) ->
        PPrint.prefix 4 1 (domain_kind_to_doc domain)
            (PPrint.string "->" ^^ PPrint.blank 1 ^^ kind_to_doc codomain)
    | TypeK -> PPrint.star

and domain_kind_to_doc domain = match domain with
    | ArrowK _ -> PPrint.parens (kind_to_doc domain)
    | _ -> kind_to_doc domain

let rec abs_to_doc : abs -> PPrint.document = function
    | ([], Hole, body) -> to_doc body
    | (params, locator, body) ->
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "exists" ^/^ bindings_to_doc params))
            (PPrint.dot ^^ PPrint.blank 1
                ^^ PPrint.parens (locator_to_doc locator ^^ PPrint.comma ^/^ to_doc body))

and to_doc = function
    | Pi ([], Hole, domain, eff, codomain) ->
        PPrint.prefix 4 1 (domain_to_doc domain) 
            (Ast.effect_arrow eff ^^ PPrint.blank 1 ^^ abs_to_doc codomain)
    | Pi (universals, locator, domain, eff, codomain) ->
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ bindings_to_doc universals))
            (PPrint.dot ^^ PPrint.blank 1
             ^^ PPrint.prefix 4 1 (PPrint.parens (locator_to_doc locator ^^ PPrint.comma ^/^ to_doc domain))
                    (Ast.effect_arrow eff ^^ PPrint.blank 1 ^^ abs_to_doc codomain))
    | Record fields ->
        PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc fields
    | Fn (param, body) ->
        PPrint.prefix 4 1
            (PPrint.string "fun" ^^ PPrint.blank 1 ^^ Name.to_doc param
                 ^^ PPrint.blank 1 ^^ PPrint.dot)
            (to_doc body)
    | App (callee, arg) -> PPrint.group (callee_to_doc callee ^/^ arg_to_doc arg)
    | Type typ -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ abs_to_doc typ)
    | Use (name, _) -> Name.to_doc name
    | Ov ((name, _), _) -> Name.to_doc name
    | Uv uv -> uv_to_doc uv
    | Int -> PPrint.string "__int"
    | Bool -> PPrint.string "__bool"

and domain_to_doc = function
    | (Pi _ | Fn _) as domain -> PPrint.parens (to_doc domain)
    | Uv uv ->
        (match !uv with
        | Assigned typ -> domain_to_doc typ
        | Unassigned _ -> uv_to_doc uv)
    | domain -> to_doc domain

and callee_to_doc = function
    | (Pi _ | Fn _) as callee -> PPrint.parens (to_doc callee)
    | Uv uv ->
        (match !uv with
        | Assigned typ -> callee_to_doc typ
        | Unassigned _ -> uv_to_doc uv)
    | callee -> to_doc callee

and arg_to_doc = function
    | (Pi _ | Fn _ | App _) as arg -> PPrint.parens (to_doc arg)
    | Uv uv ->
        (match !uv with
        | Assigned typ -> arg_to_doc typ
        | Unassigned _ -> uv_to_doc uv)
    | arg -> to_doc arg

and field_to_doc {label; typ} =
    PPrint.string label ^/^ PPrint.colon ^/^ to_doc typ

and locator_to_doc = function
    | Hole -> PPrint.underscore

and binding_to_doc (name, kind) =
    PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc kind)

and bindings_to_doc bindings = PPrint.separate_map (PPrint.break 1) binding_to_doc bindings

and universal_to_doc universals body =
    PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ bindings_to_doc universals))
        (PPrint.dot ^^ PPrint.blank 1 ^^ to_doc body)

and uv_to_doc uv = match !uv with
    | Unassigned (name, _) -> PPrint.qmark ^^ Name.to_doc name
    | Assigned t -> to_doc t

let rec coercion_to_doc = function
    | Refl typ -> to_doc typ
    | Symm co -> PPrint.string "symm" ^^ PPrint.blank 1 ^^ coercion_to_doc co
    | Trans (co, co') ->
        PPrint.infix 4 1 (PPrint.bquotes (PPrint.string "o"))
            (coercion_to_doc co) (andco_to_doc co')
    | Comp (ctor_co, arg_co) -> PPrint.prefix 4 1 (ctorco_to_doc ctor_co) (argco_to_doc arg_co)
    | Inst (co, arg) -> PPrint.infix 4 1 PPrint.at (instantiee_to_doc co) (to_doc arg)
    | AUse name -> Name.to_doc name
    | TypeCo co -> PPrint.brackets (PPrint.equals ^^ PPrint.break 1 ^^ (coercion_to_doc co))

and andco_to_doc = function
    | Trans _ as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

and ctorco_to_doc = function
    | (Symm _ | Trans _ | Inst _) as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

and argco_to_doc = function
    | (Trans _ | Inst _ | Comp _) as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

and instantiee_to_doc = function
    | (Symm _ | Trans _) as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

let rec from_path = function
    | AppP (callee, arg) -> App (from_path callee, from_path arg)
    | UvP ov -> Uv ov
    | OvP ov -> Ov ov
    | UseP binding -> Use binding

let freshen (name, kind) = (Name.freshen name, kind)

let sibling = function
    | {contents = Unassigned (_, level)} -> ref (Unassigned (Name.fresh (), level))
    | {contents = Assigned _} -> failwith "unreachable"

(* NOTE: On scope entry hygienic substitution requires that:
    1. Shadowing be honoured, e.g. [b/a](forall a . a) = forall a . a (_not_ forall a . b)
       Effectively need to ensure that the domain of the substitution does not intersect
       with the params.
    2. introduced reference capture be avoided, e.g. [b/a](forall b . a) = forall c . b
       (_not_ forall b . b). Effectively need to ensure that the codomain of the substitution
       does not contain references to the params.
    The first one could be achieved by removing the params from the substitution. For the
    second one, binders need to be renamed, which also achieves the first one. The required
    renaming can be incorporated into the substitution. *)

let rec substitute_abs substitution (params, locator, body) =
    let params' = List.map (fun (name, kind) -> (Name.freshen name, kind)) params in
    let substitution =
        List.fold_left2 (fun substitution (name, _) param' ->
                            Name.Map.add name (UseP param') substitution)
                        substitution params params' in
    (params', substitute_locator substitution locator, substitute substitution body)

and substitute substitution = function
    | Pi (params, locator, domain, eff, codomain) ->
        let params' = List.map (fun (name, kind) -> (Name.freshen name, kind)) params in
        let substitution =
            List.fold_left2 (fun substitution (name, _) param' ->
                                Name.Map.add name (UseP param') substitution)
                            substitution params params' in
        Pi ( params', substitute_locator substitution locator, substitute substitution domain
           , eff, substitute_abs substitution codomain )
    | Record fields ->
        Record (List.map (fun {label; typ} -> {label; typ = substitute substitution typ}) fields)
    | Fn (param, body) ->
        (* NOTE: Here we intentionally permit introduced reference capture but still implement
                 shadowing by using Map.remove instead of Name.freshen + Map.add: *)
        let substitution = Name.Map.remove param substitution in
        Fn (param, substitute substitution body)
    | App (callee, arg) -> App (substitute substitution callee, substitute substitution arg)
    | Type typ -> Type (substitute_abs substitution typ)
    | (Use (name, _) | Ov ((name, _), _)) as typ ->
        (match Name.Map.find_opt name substitution with
        | Some path -> from_path path (* OPTIMIZE *)
        | None -> typ)
    | Uv {contents = Assigned typ} -> substitute substitution typ
    | (Uv {contents = Unassigned _} | Int | Bool) as typ -> typ

and substitute_locator substitution : locator -> locator = function
    | RecordL fields ->
        RecordL (List.map (fun {label; typ} -> {label; typ = substitute_locator substitution typ})
                          fields)
    | TypeL path -> TypeL (substitute_path substitution path)
    | Hole -> Hole

and substitute_path substitution = function
    | AppP (callee, arg) ->
        AppP (substitute_path substitution callee, substitute_path substitution arg)
    | (UseP (name, _) | OvP ((name, _), _)) as path ->
        (match Name.Map.find_opt name substitution with
        | Some path -> path
        | None -> path)
    | UvP _ as path -> path

