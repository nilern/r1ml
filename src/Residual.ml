open FcType

type t =
    | Sub of FcType.t * locator * FcType.t * FcTerm.expr Ast.with_pos ref
    | Unify of FcType.t * FcType.t * coercion ref
    | Residuals of t * t
    | Skolems of binding Vector1.t * t
    | Axioms of (Name.t * ov * uv) Vector1.t * t

let combine r r' = Residuals (r, r')

