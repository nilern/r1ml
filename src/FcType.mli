module Effect = Ast.Effect

type kind
    = ArrowK of kind * kind
    | TypeK

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
and abs =
    | Exists of binding Vector1.t * locator * t
    | NoE of t

and t =
    | Pi of binding Vector.t * locator * t * Effect.t * abs
    | Record of t field Vector.t
    | Fn of Name.t * t
    | App of t * t
    | Type of abs
    | Use of binding
    | Ov of ov
    | Uv of uv
    | Int
    | Bool

and locator =
    | PiL of binding Vector.t * Effect.t * locator
    | RecordL of locator field Vector.t
    | TypeL of path
    | Hole

and 'a field = {label : string; typ : 'a}

and path =
    | AppP of path * path
    | OvP of ov
    | UvP of uv
    | UseP of binding

and 'e residual =
    | Sub of bool * t * locator * t * 'e ref
    | Unify of t * t * coercion ref
    | Residuals of 'e residual * 'e residual
    | Skolems of binding Vector1.t * 'e residual
    | Axioms of (Name.t * ov * uv) Vector1.t * 'e residual

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

module Residual : functor (E : sig type t end) -> Semigroup.S with type t = E.t residual (* HACK *)

val kind_to_doc : kind -> PPrint.document
val binding_to_doc : binding -> PPrint.document
val abs_to_doc : abs -> PPrint.document
val universal_to_doc : binding Vector.t -> PPrint.document -> PPrint.document
val to_doc : t -> PPrint.document
val coercion_to_doc : coercion -> PPrint.document
val locator_to_doc : locator -> PPrint.document

val freshen : binding -> binding
val sibling : uv -> uv

val substitute_abs : path Name.Map.t -> abs -> abs
val substitute : path Name.Map.t -> t -> t
val substitute_any : t Name.Map.t -> t -> t
val substitute_locator : path Name.Map.t -> locator -> locator

