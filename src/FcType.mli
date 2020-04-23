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

type uvv =
    | Unassigned of binding * level
    | Assigned of unq

and uv = uvv ref

(* Existential (or just `t`) *)
and abs = binding list * t

(* Universal (or just `unq`) *)
and t = binding list * unq

(* Top-level unquantified (i.e. does not start with a quantifier) *)
and unq =
    | Arrow of t * effect * abs
    | Record of field list
    | App of t * t
    | Type of abs
    | Use of binding
    | Ov of ov
    | Uv of uv
    | Int
    | Bool

and field = {label : string; typ : t}

val kind_to_doc : kind -> PPrint.document
val abs_to_doc : abs -> PPrint.document
val to_doc : t -> PPrint.document
val unq_to_doc : unq -> PPrint.document

val freshen : binding -> binding

val substitute_abs : unq Name.Map.t -> abs -> abs
val substitute : unq Name.Map.t -> t -> t
val substitute_unq : unq Name.Map.t -> unq -> unq

