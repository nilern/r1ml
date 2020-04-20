open Parser

let integer = [%sedlex.regexp? '0' .. '9']

let token lexbuf =
    match%sedlex lexbuf with
    | ';' -> SEMI
    | _ -> failwith "unimplemented"

