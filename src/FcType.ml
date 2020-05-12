type kind
    = ArrowK of kind * kind
    | TypeK

type effect = Ast.effect

type level = int

type binding = Name.t * kind

type ov = binding * level

type uvv =
    | Unassigned of Name.t * level
    | Assigned of t

and uv = uvv ref

and abs = binding list * t

and t =
    | Pi of binding list * t * effect * abs
    | Record of field list
    | Fn of binding * t
    | App of t * t
    | Type of abs
    | Use of binding
    | Ov of ov
    | Uv of uv
    | Int
    | Bool

and field = {label : string; typ : t}

and coercion =
    | Refl of t
    | Symm of coercion
    | Trans of coercion * coercion
    | Comp of coercion * coercion
    | Inst of coercion * t
    | AUse of Name.t
    | TypeCo of coercion

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

let rec abs_to_doc = function
    | ([], body) -> to_doc body
    | (params, body) ->
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "exists" ^/^ bindings_to_doc params))
            (PPrint.dot ^^ PPrint.blank 1 ^^ to_doc body)

and to_doc = function
    | Pi ([], domain, eff, codomain) ->
        PPrint.prefix 4 1 (domain_to_doc domain) 
            (Ast.effect_arrow eff ^^ PPrint.blank 1 ^^ abs_to_doc codomain)
    | Pi (universals, domain, eff, codomain) ->
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ bindings_to_doc universals))
            (PPrint.dot ^^ PPrint.blank 1
             ^^ PPrint.prefix 4 1 (domain_to_doc domain) 
                    (Ast.effect_arrow eff ^^ PPrint.blank 1 ^^ abs_to_doc codomain))
    | Record fields ->
        PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc fields
    | App (callee, arg) -> PPrint.group (callee_to_doc callee ^/^ arg_to_doc arg)
    | Type typ -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ abs_to_doc typ)
    | Use (name, _) -> Name.to_doc name
    | Ov ((name, _), _) -> Name.to_doc name
    | Uv uv -> uv_to_doc uv
    | Int -> PPrint.string "__int"
    | Bool -> PPrint.string "__bool"

and domain_to_doc domain = match domain with
    | Pi _ -> PPrint.parens (to_doc domain)
    | _ -> to_doc domain

and callee_to_doc callee = match callee with
    | Pi _ -> PPrint.parens (to_doc callee)
    | _ -> to_doc callee

and arg_to_doc callee = match callee with
    | (Pi _ | App _) -> PPrint.parens (to_doc callee)
    | _ -> to_doc callee

and field_to_doc {label; typ} =
    PPrint.string label ^/^ PPrint.colon ^/^ to_doc typ

and binding_to_doc (name, kind) =
    PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc kind)

and bindings_to_doc bindings = PPrint.separate_map (PPrint.break 1) binding_to_doc bindings

and uv_to_doc uv = match !uv with
    | Unassigned (name, _) -> PPrint.qmark ^^ Name.to_doc name
    | Assigned t -> to_doc t

let rec coercion_to_doc = function
    | Refl typ -> to_doc typ
    | Symm co -> PPrint.string "symm" ^^ PPrint.blank 1 ^^ coercion_to_doc co
    | Trans (co, co') ->
        PPrint.infix 4 1 (PPrint.bquotes (PPrint.string "o"))
            (coercion_to_doc co) (andco_to_doc co')
    | AUse name -> Name.to_doc name
    | TypeCo co -> PPrint.brackets (PPrint.equals ^^ PPrint.break 1 ^^ (coercion_to_doc co))

and andco_to_doc = function
    | Trans _ as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

let freshen (name, kind) = (Name.freshen name, kind)

let sibling uv = match uv with
    | {contents = Unassigned (_, level)} ->
        ref (Unassigned (Name.fresh (), level))
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

let rec substitute_abs substitution (params, body) =
    let params' = List.map (fun (name, kind) -> (Name.freshen name, kind)) params in
    let substitution =
        List.fold_left2 (fun substitution (name, _) param' ->
                            Name.Map.add name (Use param') substitution)
                        substitution params params' in
    (params', substitute substitution body)

and substitute substitution = function
    | Pi (params, domain, eff, codomain) ->
        let params' = List.map (fun (name, kind) -> (Name.freshen name, kind)) params in
        let substitution =
            List.fold_left2 (fun substitution (name, _) param' ->
                                Name.Map.add name (Use param') substitution)
                            substitution params params' in
        Pi (params', substitute substitution domain, eff, substitute_abs substitution codomain)
    | Record fields ->
        Record (List.map (fun {label; typ} -> {label; typ = substitute substitution typ}) fields)
    | App (callee, arg) -> App (substitute substitution callee, substitute substitution arg)
    | Type typ -> Type (substitute_abs substitution typ)
    | (Use (name, _) | Ov ((name, _), _)) as typ ->
        Option.value (Name.Map.find_opt name substitution) ~default: typ
    | Uv {contents = Assigned typ} -> substitute substitution typ
    | (Uv {contents = Unassigned _} | Int | Bool) as typ -> typ

