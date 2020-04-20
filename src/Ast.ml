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

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec typ_to_doc = function
    | Record decls ->
        PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
            decl_to_doc decls
    | Path {expr; _} -> expr_to_doc expr
    | Int -> PPrint.string "__int"

and decl_to_doc {name; typ} =
    PPrint.string "val" ^/^ Name.to_doc name ^/^ PPrint.colon ^/^ typ_to_doc typ

and def_to_doc = function
    | {pat; ann = Some ann} -> Name.to_doc pat ^/^ PPrint.colon ^/^ typ_to_doc ann
    | {pat; ann = None} -> Name.to_doc pat

and expr_to_doc = function
    | Type typ -> PPrint.string "type" ^/^ typ_to_doc typ
    | Use name -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

let stmt_to_doc = function
    | Val (_, def, {expr; _}) ->
        PPrint.string "val" ^/^ def_to_doc def ^/^ PPrint.equals ^/^ expr_to_doc expr
    | Expr {expr; _} -> expr_to_doc expr

