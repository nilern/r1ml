type kind
    = ArrowK of kind * kind
    | TypeK

type t
    = Record of field list
    | Type of t
    | Int

and field = {label : string; typ : t}

val kind_to_doc : kind -> PPrint.document
val to_doc : t -> PPrint.document

