type t
    = Record of field list
    | Type of t
    | Int

and field = {label : string; typ : t}

val to_doc : t -> PPrint.document

