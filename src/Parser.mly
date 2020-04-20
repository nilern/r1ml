%{ open Ast %}

%token
    VAL "val"
    COLON ":" EQ "=" SEMI ";"
    LBRACE "{" RBRACE "}"
    EOF
%token <string> ID
%token <int> CONST

%start <Ast.stmt list> stmts

%%

stmts : separated_list(";", stmt) EOF { $1 }

stmt
    : "val" pat=ID ann=ann "=" expr=expr {
        Val (($symbolstartpos, $endpos), {pat = Name.of_string pat; ann}, expr)
    }
    | expr { Expr $1 }

expr : atom { {v = $1; pos = ($symbolstartpos, $endpos)} }

atom
    : ID {
        if $1.[0] = '_' && $1.[1] = '_' then
            match $1 with
            | "__int" -> Type {v = Int; pos = ($symbolstartpos, $endpos)}
            | _ -> failwith ("nonexistent intrinsic " ^ $1)
        else Use (Name.of_string $1)
    }
    | CONST { Const $1 }

ann
    : ":" typ=typ { Some typ }
    | { None }

decl : "val" name=ID ":" typ=typ { {name = Name.of_string name; typ} }

typ
    : "{" decls=decl* "}" { {v = Sig decls; pos = ($symbolstartpos, $endpos)} }
    | expr { {$1 with v = Path $1.v} }

