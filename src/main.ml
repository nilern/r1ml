let prompt = "R1ML> "

let rec repl () =
    match LNoise.linenoise prompt with
    | None -> ()
    | Some input ->
        let _ = LNoise.history_add input in
        let lexbuf = SedlexMenhir.create_lexbuf (Sedlexing.Utf8.from_string input) in
        (try
            let stmts = SedlexMenhir.sedlex_with_menhir Lexer.token Parser.stmts lexbuf in
            print_endline input;
        with
            | SedlexMenhir.ParseError err ->
                prerr_endline (SedlexMenhir.string_of_ParseError err));
        repl ()

let () =
    print_endline "R1ML prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.";
    repl ()

