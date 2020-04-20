type t
    = Record of field list
    | Type of t
    | Int

and field = {label : string; typ : t}

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec to_doc = function
    | Record fields ->
        PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc fields
    | Type typ -> PPrint.brackets (PPrint.equals ^/^ to_doc typ)
    | Int -> PPrint.string "__int"

and field_to_doc {label; typ} =
    PPrint.string label ^/^ PPrint.colon ^/^ to_doc typ

