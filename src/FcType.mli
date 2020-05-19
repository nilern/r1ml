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
    | Assigned of typ

and uv = uvv ref

(* Existential (or just `t`) *)
and abs = binding list * locator * t

and t =
    | Pi of binding list * locator * t * effect * abs
    | IPi of t list * t * effect * abs
    | Record of t field list
    | Fn of Name.t * t
    | App of t * t
    | Type of abs
    | Use of binding
    | Ov of ov
    | Uv of uv
    | Int
    | Bool

and locator =
    | PiL of binding list * effect * locator
    | RecordL of locator field list
    | TypeL of path
    | Hole

and 'a field = {label : string; typ : 'a}

and path =
    | AppP of path * path
    | OvP of ov
    | UvP of uv
    | UseP of binding

and coercion =
    | Refl of typ
    | Symm of coercion
    | Trans of coercion * coercion
    | Comp of coercion * coercion
    | Inst of coercion * typ
    | AUse of Name.t
    | TypeCo of coercion

and typ = t
and template = locator

val kind_to_doc : kind -> PPrint.document
val binding_to_doc : binding -> PPrint.document
val abs_to_doc : abs -> PPrint.document
val universal_to_doc : binding list -> t -> PPrint.document
val to_doc : t -> PPrint.document
val coercion_to_doc : coercion -> PPrint.document

val freshen : binding -> binding
val sibling : uv -> uv

val substitute_abs : path Name.Map.t -> abs -> abs
val substitute : path Name.Map.t -> t -> t
val substitute_locator : path Name.Map.t -> locator -> locator

