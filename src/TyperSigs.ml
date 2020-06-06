(* Predeclare types and signatures for typer internal modules so that they can be separated: *)

open FcType

type span = Ast.span
type 'a with_pos = 'a Ast.with_pos
type 'a typing = 'a Env.typing
type coercer = Env.coercer
type 'a matching = 'a Env.matching

module type CHECKING = sig
    val instantiate_abs : Env.t -> kind Vector.t * locator * typ -> uv Vector.t * locator * typ
    val instantiate_arrow : Env.t -> kind Vector.t * locator * typ * Effect.t * abs
        -> uv Vector.t * locator * typ * Effect.t * abs
    val whnf : Env.t -> typ -> (typ * coercion option) option
    val typeof : Env.t -> Ast.Term.expr with_pos -> FcTerm.expr with_pos typing
    val deftype : Env.t -> Ast.Term.def -> FcTerm.def typing
end

module type MATCHING = sig
    val focalize : span -> Env.t -> typ -> locator -> coercer * typ
    val coercion : span -> Env.t -> typ -> ov Vector.t * locator * typ -> coercer matching
    val subtype : span -> Env.t -> typ -> locator -> typ -> coercer matching
    val unify : span -> Env.t -> typ -> typ -> coercion option matching
    val solve : span -> Env.t -> Residual.t option -> unit
end

