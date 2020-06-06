%{
open Ast
open Term
open Type
open Effect

let unpath typ =
    {typ with v = match typ.v with
                  | Path expr -> expr
                  | _ -> Proxy typ }
%}

%token
    IF "if" THEN "then" ELSE "else" FUN "fun" TYPE "type"
    ARROW "->" DARROW "=>" DOT "." COLON ":" SEAL ":>" EQ "=" SEMI ";"
    LPAREN "(" RPAREN ")"
    LBRACKET "[" RBRACKET "]"
    LBRACE "{" RBRACE "}"
    EOF
%token <string> ID
%token <Const.t> CONST

%start <Ast.Term.stmt list> stmts

%%

(* # Expressions *)

expr
    : "fun" param=param "=>" body=expr { {v = Fn (param, body); pos = $sloc} }
    | seal_expr { $1 }

seal_expr
    : expr=seal_expr ":>" ann=typ { {v = Seal (expr, ann); pos = $sloc} }
    | simple_expr { $1 }

simple_expr
    : "if" expr "then" simple_expr "else" simple_expr {
        {v = If ($2, $4, $6); pos = $sloc}
    }
    | app { $1 }

app
    : app select { {v = App ($1, $2); pos = $sloc} }
    | select { $1 }

select
    : record=select "." label=ID { {v = Select (record, Name.of_string label); pos = $sloc} }
    | expr_nestable { $1 }

expr_nestable : expr_nestable_impl { {v = $1; pos = $sloc} }

expr_nestable_impl
    : "{" defs=separated_list(";", def) "}" { Struct (Vector.of_list defs) }
    | "(" expr ")" { $2.v }
    | common_nestable { $1 }

common_nestable
    : "[" typ "]" { Proxy $2 }
    | atom { $1 }

atom
    : ID {
        if $1.[0] = '_' && $1.[1] = '_' then
            match $1 with
            | "__int" -> Proxy {v = Prim Int; pos = $sloc}
            | "__bool" -> Proxy {v = Prim Bool; pos = $sloc}
            | _ -> failwith ("nonexistent intrinsic " ^ $1)
        else Use (Name.of_string $1)
    }
    | CONST { Const $1 }

param
    : ID { {pat = Name.of_string $1; ann = None} }
    | "(" pat=ID ":" ann=typ ")" { {pat = Name.of_string pat; ann = Some ann} }

(* # Statements *)

stmts : separated_list(";", stmt) EOF { $1 }

stmt
    : def { Def $1 }
    | expr { Expr $1 }

def 
    : pat=ID ann=ann "=" expr=expr { ($sloc, {pat = Name.of_string pat; ann}, expr) }
    | "type" pat=ID "=" typ=typ {
        ($sloc, {pat = Name.of_string pat; ann = None}, {v = Proxy typ; pos = $loc(typ)})
    }

(* # Types *)

typ
    : domain=domain "=>" codomain=typ { {v = Pi (domain, Pure, codomain); pos = $sloc} }
    | domain=domain "->" codomain=typ { {v = Pi (domain, Impure, codomain); pos = $sloc} }
    | simple_typ { $1 }

domain
    : simple_typ { {name = None; typ = $1} }
    | "(" name=ID ":" typ=typ ")" { {name = Some (Name.of_string name); typ} }

simple_typ
    : "if" expr "then" simple_typ "else" simple_typ {
        {v = Path (If ($2, unpath $4, unpath $6)); pos = $sloc}
    }
    | app_typ { $1 }

app_typ
    : app_typ select_typ { {v = Path (App (unpath $1, unpath $2)); pos = $sloc} }
    | select_typ { $1 }

select_typ
    : record=select_typ "." label=ID {
        {v = Path (Select (unpath record, Name.of_string label)); pos = $sloc}
    }
    | typ_nestable { $1 }

typ_nestable : typ_nestable_impl { {v = $1; pos = $sloc} }

typ_nestable_impl
    : "{" decls=separated_list(";", decl) "}" { Sig (Vector.of_list decls) }
    | "type" { Type }
    | "(" typ ")" { $2.v }
    | common_nestable { Path $1 }

ann
    : ":" typ=typ { Some typ }
    | { None }

(* ## Declarations *)

decl
    : name=ID ":" typ=typ { {name = Name.of_string name; typ} }
    | "type" name=ID "=" typ=typ {
        {name = Name.of_string name; typ = {v = Singleton {v = Proxy typ; pos = $loc(typ)}; pos = $sloc}}
    }
    | "type" name=ID { {name = Name.of_string name; typ = {v = Type; pos = $loc(name)}} }

