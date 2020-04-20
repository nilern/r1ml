open SedlexMenhir

open Parser

let digit = [%sedlex.regexp? '0' .. '9']

let integer = [%sedlex.regexp? Plus digit]

let rec token ({stream; _} as lexbuf) =
    match%sedlex stream with
    | ';' -> update lexbuf; SEMI

    | integer -> update lexbuf; CONST (int_of_string (lexeme lexbuf))

    | Plus (Chars " \t\r") -> update lexbuf; token lexbuf 
    | '\n' -> update lexbuf; new_line lexbuf; token lexbuf
    | eof -> update lexbuf; EOF

    | _ -> raise_ParseError lexbuf

