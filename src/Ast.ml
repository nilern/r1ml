type pos = Lexing.position

type expr
    = Const of int

and pos_expr = {expr: expr; pos: pos}

and stmt
    = Expr of pos_expr

