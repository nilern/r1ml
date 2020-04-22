type t

val of_string : string -> t
val fresh : unit -> t
val freshen : t -> t
val to_doc : t -> PPrint.document

