%{ open Ast %}

%token
    SEMI ";"
    EOF
%token <int> CONST

%start <Ast.stmt list> stmts

%%

stmts : separated_list(";", stmt) EOF { $1 }

stmt : expr { Expr $1 }

expr : atom { {pos = ($symbolstartpos, $endpos); expr = $1} }

atom : CONST { Const $1 }

