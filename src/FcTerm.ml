type span = Ast.span
type 'a with_pos = 'a Ast.with_pos
type abs = FcType.abs
type typ = FcType.t
type unq = FcType.unq

type lvalue = {name : Name.t; typ : typ}

type expr
    = Fn of lvalue * expr with_pos
    | If of expr with_pos * expr with_pos * expr with_pos
    | App of expr with_pos * expr with_pos
    | TApp of expr with_pos * unq with_pos
    | Proxy of abs
    | Use of lvalue
    | Const of int

type def = span * lvalue * expr with_pos

type stmt
    = Def of def
    | Expr of expr with_pos

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module Type = FcType

let lvalue_to_doc {name; typ} =
    PPrint.infix 4 1 PPrint.colon (Name.to_doc name) (Type.to_doc typ)

let rec expr_to_doc = function
    | Fn (param, body) -> PPrint.infix 4 1 (PPrint.string "=>")
        (PPrint.group (PPrint.string "fun" ^/^ lvalue_to_doc param)) (expr_to_doc body.v)
    | If (cond, conseq, alt) ->
        PPrint.string "if" ^/^ expr_to_doc cond.v
            ^/^ PPrint.string "then" ^/^ expr_to_doc conseq.v
            ^/^ PPrint.string "else" ^/^ expr_to_doc alt.v
    | App (callee, arg) -> PPrint.align (callee_to_doc callee.v ^/^ arg_to_doc arg.v)
    | TApp (callee, arg) -> PPrint.align (callee_to_doc callee.v ^/^ FcType.unq_to_doc arg.v)
    | Proxy typ -> PPrint.brackets (Type.abs_to_doc typ)
    | Use {name; _} -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

and callee_to_doc = function
    | Fn _ as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and arg_to_doc = function
    | (Fn _ | App _ | TApp _) as arg -> PPrint.parens (expr_to_doc arg)
    | arg -> expr_to_doc arg

let def_to_doc ((_, lvalue, {v = expr; _}) : def) =
    PPrint.infix 4 1 PPrint.equals (lvalue_to_doc lvalue) (expr_to_doc expr)

let stmt_to_doc = function
    | Def def -> def_to_doc def
    | Expr {v = expr; _} -> expr_to_doc expr

