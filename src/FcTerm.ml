type span = Ast.span
type 'a with_pos = 'a Ast.with_pos

module Type = FcType
type typ = FcType.t

type def = {name : Name.t; typ : typ}

type expr
    = Proxy of typ
    | Use of def
    | Const of int

type stmt
    = Val of span * def * expr with_pos
    | Expr of expr with_pos

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let def_to_doc {name; typ} = Name.to_doc name ^/^ PPrint.colon ^/^ Type.to_doc typ

let expr_to_doc = function
    | Proxy typ -> PPrint.brackets (Type.to_doc typ)
    | Use {name; _} -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

let stmt_to_doc = function
    | Val (_, def, {v = expr; _}) ->
        PPrint.string "val" ^/^ def_to_doc def ^/^ PPrint.equals ^/^ expr_to_doc expr
    | Expr {v = expr; _} -> expr_to_doc expr

