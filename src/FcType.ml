type kind
    = ArrowK of kind * kind
    | TypeK

type effect = Ast.effect

type level = int

type binding = Name.t * kind

type ov = binding * level

type uvv
    = Unassigned of binding * level
    | Assigned of t

and uv = uvv ref

and t
    = Fn of binding list * t * effect * abs
    | Record of field list
    | Type of abs
    | Use of binding
    | Ov of ov
    | Uv of uv
    | Int
    | Bool

and field = {label : string; typ : t}

and abs = binding list * t

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec kind_to_doc = function
    | ArrowK (domain, codomain) ->
        kind_to_doc domain ^/^ PPrint.string "->" ^/^ kind_to_doc codomain
    | TypeK -> PPrint.star

let rec to_doc = function
    | Fn (tparams, domain, eff, codomain) ->
        let params_doc = match tparams with
            | _ :: _ ->
                PPrint.string "forall" ^/^ bindings_to_doc tparams ^/^ PPrint.dot ^^ PPrint.break 1
            | [] -> PPrint.empty in
        params_doc ^^ domain_to_doc domain ^/^ Ast.effect_arrow eff ^/^ abs_to_doc codomain
    | Record fields ->
        PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc fields
    | Type typ -> PPrint.brackets (PPrint.equals ^/^ abs_to_doc typ)
    | Use (name, _) -> Name.to_doc name
    | Ov ((name, _), _) -> Name.to_doc name
    | Uv uv -> uv_to_doc uv
    | Int -> PPrint.string "__int"
    | Bool -> PPrint.string "__bool"

and abs_to_doc = function
    | ([], body) -> to_doc body
    | (params, body) ->
        PPrint.string "exists" ^/^ bindings_to_doc params ^/^ PPrint.dot ^/^ to_doc body

and domain_to_doc = function
    | Fn _ as domain -> PPrint.parens (to_doc domain)
    | domain -> to_doc domain

and field_to_doc {label; typ} =
    PPrint.string label ^/^ PPrint.colon ^/^ to_doc typ

and binding_to_doc (name, kind) =
    PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc kind)

and bindings_to_doc bindings = PPrint.separate_map (PPrint.break 1) binding_to_doc bindings

and uv_to_doc uv = match !uv with
    | Unassigned ((name, _), _) -> PPrint.qmark ^^ Name.to_doc name
    | Assigned t -> to_doc t

let freshen (name, kind) = (Name.freshen name, kind)

