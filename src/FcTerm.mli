type span = Ast.span
type 'a with_pos = 'a Ast.with_pos
type typ = FcType.typ

type def = {name : Name.t; typ : typ}

type expr
    = Proxy of typ
    | Use of def
    | Const of int

type stmt
    = Val of span * def * expr with_pos
    | Expr of expr with_pos

val def_to_doc : def -> PPrint.document
val expr_to_doc : expr -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

