type 'a typing = {term : 'a; typ : FcType.t; eff : Ast.effect}

module Env : sig
    type t

    val interactive : unit -> t
end

val kindcheck : Env.t -> Ast.typ Ast.with_pos -> FcType.t
val typeof : Env.t -> Ast.expr Ast.with_pos -> FcTerm.expr Ast.with_pos typing
val check_interaction : Env.t -> Ast.stmt -> FcTerm.stmt typing

