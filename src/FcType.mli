module Effect = Ast.Effect

type kind
    = ArrowK of kind * kind
    | TypeK

type bv = {depth : int; sibli : int}

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

(* TODO: Union-Find: *)
and uv = uvv ref

and abs = Exists of kind Vector.t * locator * t

and t =
    | Pi of kind Vector.t * locator * t * Effect.t * abs
    | Record of t field Vector.t
    | Fn of t
    | App of t * t
    | Type of abs
    | Use of binding
    | Bv of bv
    | Ov of ov
    | Uv of uv
    | Prim of Prim.t

and locator =
    | PiL of kind Vector.t * Effect.t * locator
    | RecordL of locator field Vector.t
    | TypeL of path
    | Hole

and 'a field = {label : string; typ : 'a}

and path =
    | AppP of path * path
    | BvP of bv
    | OvP of ov
    | UvP of uv

and coercion =
    | Refl of typ
    | Symm of coercion
    | Trans of coercion * coercion
    | Comp of coercion * coercion
    | Inst of coercion * typ
    | AUse of Name.t
    | TypeCo of coercion
    | Patchable of coercion ref

and typ = t
and template = locator

val kind_to_doc : kind -> PPrint.document
val binding_to_doc : binding -> PPrint.document
val abs_to_doc : abs -> PPrint.document
val universal_to_doc : binding Vector.t -> PPrint.document -> PPrint.document
val to_doc : t -> PPrint.document
val coercion_to_doc : coercion -> PPrint.document
val locator_to_doc : locator -> PPrint.document
val path_to_doc : path -> PPrint.document

val to_abs : t -> abs

val freshen : binding -> binding
val sibling : uv -> uv

val expose_abs : path Vector.t -> abs -> abs
val expose : path Vector.t -> t -> t
val expose_locator : path Vector.t -> locator -> locator

val close_abs : int Name.Map.t -> abs -> abs
val close : int Name.Map.t -> t -> t
val close_locator : int Name.Map.t -> locator -> locator

