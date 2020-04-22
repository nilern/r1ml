type kind
    = ArrowK of kind * kind
    | TypeK

type effect = Ast.effect

(* The level of a type variable is the number of skolem-binding scopes in the
   typing environment at its creation site. Kind of like syntactic closures, but
   type inference is (scoping-wise) much simpler than hygienic macroexpansion so
   the required information can be compressed to this one small integer. *)
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

val kind_to_doc : kind -> PPrint.document
val to_doc : t -> PPrint.document
val abs_to_doc : abs -> PPrint.document

val freshen : binding -> binding

