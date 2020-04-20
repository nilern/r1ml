type typ
    = Record of field list
    | Type of typ
    | Int

and field = {label : string; typ : typ}

val to_doc : typ -> PPrint.document

