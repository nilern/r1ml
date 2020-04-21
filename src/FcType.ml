type kind
    = ArrowK of kind * kind
    | TypeK

type param = {name : Name.t; kind : kind}

type t
    = Record of field list
    | Type of abs
    | Int
    | Bool

and field = {label : string; typ : t}

and abs = param list * t

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec kind_to_doc = function
    | ArrowK (domain, codomain) ->
        kind_to_doc domain ^/^ PPrint.string "->" ^/^ kind_to_doc codomain
    | TypeK -> PPrint.star

let rec to_doc = function
    | Record fields ->
        PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc fields
    | Type typ -> PPrint.brackets (PPrint.equals ^/^ abs_to_doc typ)
    | Int -> PPrint.string "__int"
    | Bool -> PPrint.string "__bool"

and param_to_doc {name; kind} =
    PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc kind)

and field_to_doc {label; typ} =
    PPrint.string label ^/^ PPrint.colon ^/^ to_doc typ

and abs_to_doc (params, body) =
    PPrint.string "exists"
        ^/^ PPrint.separate_map (PPrint.break 1) param_to_doc params
        ^/^ PPrint.string "." ^/^ to_doc body

