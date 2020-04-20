type pos = Lexing.position

type expr
    = Use of Name.t
    | Const of int

and pos_expr = {expr: expr; pos: pos * pos}

and stmt
    = Expr of pos_expr

val expr_to_doc : expr -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

