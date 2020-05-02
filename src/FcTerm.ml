type span = Ast.span
type 'a with_pos = 'a Ast.with_pos
type abs = FcType.abs
type typ = FcType.t
type ov = FcType.ov
type coercion = FcType.coercion

type lvalue = {name : Name.t; typ : typ}

type expr
    = Fn of FcType.binding list * lvalue * expr with_pos
    | App of expr with_pos * typ list * expr with_pos
    | Letrec of def list * expr with_pos
    | Axiom of (Name.t * ov * typ) list * expr with_pos
    | Cast of expr with_pos * coercion
    | If of expr with_pos * expr with_pos * expr with_pos
    | Record of field list
    | Proxy of abs 
    | Use of lvalue
    | Const of int

and def = span * lvalue * expr with_pos

and field = {label : string; expr : expr with_pos}

type stmt
    = Def of def
    | Expr of expr with_pos

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module Type = FcType
let coercion_to_doc = Type.coercion_to_doc

let letrec defs (body : expr with_pos) = match defs with
    | [] -> body.v
    | _ :: _ -> Letrec (defs, body)

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
    | Letrec (defs, body) ->
        PPrint.group(
            PPrint.surround 4 1 (PPrint.string "letrec")
                (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) def_to_doc defs))
                (PPrint.string "in")
            ^/^ expr_to_doc body.v)
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
    | Axiom (axioms, body) ->
        PPrint.group(
            PPrint.surround 4 1 (PPrint.string "axiom")
                (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) axiom_to_doc axioms))
                (PPrint.string "in")
            ^/^ expr_to_doc body.v)
    | Cast ({v = expr; _}, coercion) ->
        PPrint.infix 4 1 (PPrint.string "|>") (castee_to_doc expr) (coercion_to_doc coercion)
    | Record defs ->
        PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc defs
    | Proxy typ -> PPrint.brackets (Type.abs_to_doc typ)
    | Use {name; _} -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

and callee_to_doc = function
    | (Fn _ | Cast _ | Letrec _ | Axiom _) as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and arg_to_doc = function
    | (Fn _ | Cast _ | Letrec _ | Axiom _ | App _) as arg -> PPrint.parens (expr_to_doc arg)
    | arg -> expr_to_doc arg

and axiom_to_doc (name, ((ov_name, _), _), typ) =
    PPrint.infix 4 1 PPrint.colon (Name.to_doc name)
        (PPrint.infix 4 1 PPrint.tilde (Name.to_doc ov_name) (Type.to_doc typ))

and castee_to_doc = function
    | Fn _ as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and def_to_doc ((_, lvalue, {v = expr; _}) : def) =
    PPrint.infix 4 1 PPrint.equals (lvalue_to_doc lvalue) (expr_to_doc expr)

and field_to_doc {label; expr} =
    PPrint.infix 4 1 PPrint.equals (PPrint.string label) (expr_to_doc expr.v)

let stmt_to_doc = function
    | Def def -> def_to_doc def
    | Expr {v = expr; _} -> expr_to_doc expr

