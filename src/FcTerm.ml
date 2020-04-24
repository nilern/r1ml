type span = Ast.span
type 'a with_pos = 'a Ast.with_pos
type abs = FcType.abs
type typ = FcType.t

type lvalue = {name : Name.t; typ : typ}

type expr
    = Fn of FcType.binding list * lvalue * expr with_pos
    | If of expr with_pos * expr with_pos * expr with_pos
    | App of expr with_pos * typ list * expr with_pos
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
    | Fn (universals, param, body) ->
        PPrint.prefix 4 1
            (PPrint.string "fun"
                 ^^ (PPrint.surround_separate_map 4 0 PPrint.empty
                         (PPrint.blank 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                         FcType.binding_to_doc universals
                     ^^ PPrint.blank 1 ^^ PPrint.parens (lvalue_to_doc param))
                 ^^ PPrint.blank 1 ^^ PPrint.string "=>")
            (expr_to_doc body.v)
    | If (cond, conseq, alt) ->
        PPrint.string "if" ^/^ expr_to_doc cond.v
            ^/^ PPrint.string "then" ^/^ expr_to_doc conseq.v
            ^/^ PPrint.string "else" ^/^ expr_to_doc alt.v
    | App (callee, targs, arg) ->
        PPrint.align (callee_to_doc callee.v
                      ^^ PPrint.surround_separate_map 4 0 PPrint.empty
                            (PPrint.break 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                            FcType.to_doc targs
                      ^/^ arg_to_doc arg.v)
    | Proxy typ -> PPrint.brackets (Type.abs_to_doc typ)
    | Use {name; _} -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

and callee_to_doc = function
    | Fn _ as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and arg_to_doc = function
    | (Fn _ | App _) as arg -> PPrint.parens (expr_to_doc arg)
    | arg -> expr_to_doc arg

let def_to_doc ((_, lvalue, {v = expr; _}) : def) =
    PPrint.infix 4 1 PPrint.equals (lvalue_to_doc lvalue) (expr_to_doc expr)

let stmt_to_doc = function
    | Def def -> def_to_doc def
    | Expr {v = expr; _} -> expr_to_doc expr
