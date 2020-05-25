type abs = FcType.abs
type typ = FcType.t
type locator = FcType.locator
type ov = FcType.ov
type uv = FcType.uv
type effect = FcType.Effect.t

type error =
    | Unbound of Name.t
    | MissingField of typ * string
    | SubEffect of effect * effect
    | SubType of typ * typ
    | Unify of typ * typ
    | ImpureType of Ast.Term.expr
    | Escape of ov
    | Occurs of uv * typ
    | Polytype of abs
    | PolytypeInference of abs
    | RecordArticulation of typ
    | RecordArticulationL of locator

exception TypeError of Ast.span * error

val type_error_to_doc : Ast.span -> error -> PPrint.document

type 'a typing = {term : 'a; typ : FcType.typ; eff : effect}

module Env : sig
    type t

    val interactive : unit -> t
end

val kindcheck : Env.t -> Ast.Type.t Ast.with_pos -> FcTerm.abs
val typeof : Env.t -> Ast.Term.expr Ast.with_pos -> FcTerm.expr Ast.with_pos typing
val check_interaction : Env.t -> Ast.Term.stmt -> FcTerm.stmt typing

