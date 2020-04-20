type typing = {expr : FcTerm.expr; typ : FcType.t; eff : Ast.effect}

module Env : sig
    type t
end

val kindof : Env.t -> Ast.typ -> FcType.t
val typeof : Env.t -> Ast.expr -> typing

