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

val kind_to_doc : kind -> PPrint.document
val to_doc : t -> PPrint.document
val abs_to_doc : abs -> PPrint.document

