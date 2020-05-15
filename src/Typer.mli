exception TypeError of Ast.span

val type_error_to_string : Ast.span -> string

type 'a typing = {term : 'a; typ : FcType.typ; eff : Ast.effect}

module Env : sig
    type t

    val interactive : unit -> t
end

val kindcheck : Env.t -> Ast.typ Ast.with_pos -> FcTerm.abs
val typeof : Env.t -> Ast.expr Ast.with_pos -> FcTerm.expr Ast.with_pos typing
val check_interaction : Env.t -> Ast.stmt -> FcTerm.stmt typing

