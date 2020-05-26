type effect = FcType.Effect.t
type typ = FcType.t
type abs = FcType.abs

type error =
    | Unbound of Name.t
    | MissingField of typ * string
    | SubEffect of effect * effect
    | SubType of typ * typ
    | Unify of typ * typ
    | Unsolvable of FcTerm.expr Ast.with_pos FcType.residual
    | ImpureType of Ast.Term.expr
    | Escape of FcType.ov
    | Occurs of FcType.uv * typ
    | Polytype of abs
    | PolytypeInference of abs
    | RecordArticulation of typ
    | RecordArticulationL of FcType.locator

exception TypeError of Ast.span * error

val to_doc : Ast.span -> error -> PPrint.document

