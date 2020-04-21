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

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module Type = FcType

let lvalue_to_doc {name; typ} = Name.to_doc name ^/^ PPrint.colon ^/^ Type.to_doc typ

let expr_to_doc = function
    | Proxy typ -> PPrint.brackets (Type.to_doc typ)
    | Use {name; _} -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

let def_to_doc ((_, lvalue, {v = expr; _}) : def) =
    PPrint.group (lvalue_to_doc lvalue ^/^ PPrint.equals ^/^ expr_to_doc expr)

let stmt_to_doc = function
    | Def def -> def_to_doc def
    | Expr {v = expr; _} -> expr_to_doc expr

