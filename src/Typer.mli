type abs = FcType.abs
type typ = FcType.t
type locator = FcType.locator
type ov = FcType.ov
type uv = FcType.uv
type effect = FcType.Effect.t

type 'a typing = {term : 'a; typ : FcType.typ; eff : effect}

module Env : sig
    type t

    val interactive : unit -> t
end

val kindcheck : Env.t -> Ast.Type.t Ast.with_pos -> FcTerm.abs
val typeof : Env.t -> Ast.Term.expr Ast.with_pos -> FcTerm.expr Ast.with_pos typing
val check_interaction : Env.t -> Ast.Term.stmt -> FcTerm.stmt typing

