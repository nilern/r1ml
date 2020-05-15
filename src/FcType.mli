type partial
type complete

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
    | Unassigned of Name.t * level
    | Assigned of complete t

and uv = uvv ref

(* Existential (or just `t`) *)
and 'a abs = binding list * 'a t

and _ t =
    | Pi : binding list * 'a t * effect * 'a abs -> 'a t
    | Record : 'a field list -> 'a t
    | Fn : Name.t * 'a t -> 'a t
    | App : 'a t * 'a t -> 'a t
    | Type : 'a abs -> 'a t
    | Use : binding -> 'a t
    | Ov : ov -> 'a t
    | Uv : uv -> 'a t
    | Int : 'a t
    | Bool : 'a t
    | Hole : partial t

and 'a field = {label : string; typ : 'a t}

and coercion =
    | Refl of typ
    | Symm of coercion
    | Trans of coercion * coercion
    | Comp of coercion * coercion
    | Inst of coercion * typ
    | AUse of Name.t
    | TypeCo of coercion

and typ = complete t
and template = partial t

val kind_to_doc : kind -> PPrint.document
val binding_to_doc : binding -> PPrint.document
val abs_to_doc : 'a abs -> PPrint.document
val universal_to_doc : binding list -> 'a t -> PPrint.document
val to_doc : 'a t -> PPrint.document
val coercion_to_doc : coercion -> PPrint.document

val freshen : binding -> binding
val sibling : uv -> uv

val substitute_abs : typ Name.Map.t -> complete abs -> complete abs
val substitute : typ Name.Map.t -> typ -> typ

