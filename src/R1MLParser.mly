%token
    SEMI ";"
    CONST

%start <unit list> stmts

%%

stmts : separated_list(";", stmt) { List.rev $1 }

stmt : expr { $1 }

expr : atom { $1 }

atom : CONST { () }

