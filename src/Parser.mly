%token
    SEMI ";"
    EOF
%token <int> CONST

%start <unit list> stmts

%%

stmts : separated_list(";", stmt) EOF { List.rev $1 }

stmt : expr { $1 }

expr : atom { $1 }

atom : CONST { () }

