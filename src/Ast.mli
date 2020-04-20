type span = Lexing.position * Lexing.position

type 'a with_pos = {v : 'a; pos: span}

type def = {pat : Name.t; ann: typ with_pos option}

and typ
    = Record of decl list
    | Path of expr
    | Int

and decl = {name : Name.t; typ : typ with_pos}

and expr
    = Type of typ with_pos
    | Use of Name.t
    | Const of int

and stmt
    = Val of span * def * expr with_pos
    | Expr of expr with_pos

val def_to_doc : def -> PPrint.document
val typ_to_doc : typ -> PPrint.document
val decl_to_doc : decl -> PPrint.document
val expr_to_doc : expr -> PPrint.document
val stmt_to_doc : stmt -> PPrint.document

