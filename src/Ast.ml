type span = Lexing.position * Lexing.position

type 'a with_pos = {v : 'a; pos: span}

type def = {pat : Name.t; ann: typ with_pos option}

and effect = Pure | Impure

and typ
    = Sig of decl list
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

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec typ_to_doc = function
    | Sig decls ->
        PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
            decl_to_doc decls
    | Path expr -> expr_to_doc expr
    | Int -> PPrint.string "__int"

and decl_to_doc {name; typ = {v = typ; _}} =
    PPrint.string "val" ^/^ Name.to_doc name ^/^ PPrint.colon ^/^ typ_to_doc typ

and def_to_doc = function
    | {pat; ann = Some {v = ann; _}} -> Name.to_doc pat ^/^ PPrint.colon ^/^ typ_to_doc ann
    | {pat; ann = None} -> Name.to_doc pat

and expr_to_doc = function
    | Type {v = typ; _} -> PPrint.string "type" ^/^ typ_to_doc typ
    | Use name -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

let stmt_to_doc = function
    | Val (_, def, {v = expr; _}) ->
        PPrint.string "val" ^/^ def_to_doc def ^/^ PPrint.equals ^/^ expr_to_doc expr
    | Expr {v = expr; _} -> expr_to_doc expr

