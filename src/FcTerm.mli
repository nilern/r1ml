type span = Ast.span
type 'a with_pos = 'a Ast.with_pos
type typ = FcType.t

type lvalue = {name : Name.t; typ : typ}

type expr
    = Fn of lvalue * expr with_pos
    | App of expr with_pos * expr with_pos
    | Proxy of typ
    | Use of lvalue
    | Const of int

type def = span * lvalue * expr with_pos

type stmt
    = Def of def
    | Expr of expr with_pos

val lvalue_to_doc : lvalue -> PPrint.document
val expr_to_doc : expr -> PPrint.document
val def_to_doc : def -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

