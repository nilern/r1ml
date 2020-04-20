type pos = Lexing.position

type expr
    = Use of Name.t
    | Const of int

and pos_expr = {expr: expr; pos: pos * pos}

and stmt
    = Expr of pos_expr

let expr_to_doc = function
    | Use name -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

let stmt_to_doc = function
    | Expr {expr; _} -> expr_to_doc expr

