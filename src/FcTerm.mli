type span = Ast.span
type 'a with_pos = 'a Ast.with_pos
type typ = FcType.t
type abs = FcType.abs
type ov = FcType.ov
type coercion = FcType.coercion

type lvalue = {name : Name.t; typ : typ}

type expr
    = Fn of FcType.binding list * lvalue * expr with_pos
    | App of expr with_pos * typ list * expr with_pos
    | Letrec of def list * expr with_pos
    | Axiom of (Name.t * ov * typ) list * expr with_pos
    | Cast of expr with_pos * coercion
    | Pack of typ list * expr with_pos
    | Unpack of FcType.binding list * lvalue * expr with_pos * expr with_pos
    | If of expr with_pos * expr with_pos * expr with_pos
    | Record of field list
    | Select of expr with_pos * string
    | Proxy of abs 
    | Use of lvalue
    | Const of Const.t

and def = span * lvalue * expr with_pos

and field = {label : string; expr : expr with_pos}

type stmt
    = Def of def
    | Expr of expr with_pos

val letrec : def list -> expr with_pos -> expr

val lvalue_to_doc : lvalue -> PPrint.document
val expr_to_doc : expr -> PPrint.document
val def_to_doc : def -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

