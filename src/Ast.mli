type pos = Lexing.position
type span = pos * pos

type def = {pat : Name.t; ann: typ option}

and typ
    = Record of decl list
    | Path of pos_expr
    | Int

and decl = {name : Name.t; typ: typ}

and expr
    = Type of typ
    | Use of Name.t
    | Const of int

and pos_expr = {expr : expr; pos : span}

and stmt
    = Val of span * def * pos_expr
    | Expr of pos_expr

val def_to_doc : def -> PPrint.document
val typ_to_doc : typ -> PPrint.document
val decl_to_doc : decl -> PPrint.document
val expr_to_doc : expr -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

