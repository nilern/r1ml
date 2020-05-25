let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let prompt = "R1ML> "

(* TODO: Allow mutual recursion? *)
let ep env stmts =
    let step stmt =
        let {term; typ; eff} : FcTerm.stmt Typer.typing = Typer.check_interaction env stmt in
        PPrint.ToChannel.pretty 1.0 80 stdout (PPrint.hardline ^^ PPrint.hardline ^^ FcTerm.stmt_to_doc term);
        let doc = PPrint.group (PPrint.group (PPrint.colon ^/^ FcType.to_doc typ)
            ^/^ PPrint.group (PPrint.bang ^/^ Ast.Effect.to_doc eff)) in
        PPrint.ToChannel.pretty 1.0 80 stdout (PPrint.hardline ^^ doc) in
    List.iter step stmts

let rec repl env =
    match LNoise.linenoise prompt with
    | None -> ()
    | Some input ->
        let _ = LNoise.history_add input in
        let lexbuf = SedlexMenhir.create_lexbuf ~file: "<REPL input>" (Sedlexing.Utf8.from_string input) in
        (try
            let stmts = SedlexMenhir.sedlex_with_menhir Lexer.token Parser.stmts lexbuf in
            let doc = PPrint.group (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) Ast.Term.stmt_to_doc stmts) in
            PPrint.ToChannel.pretty 1.0 80 stdout doc;
            ep env stmts;
            print_newline ()
        with
            | SedlexMenhir.ParseError err ->
                flush stdout;
                prerr_endline (SedlexMenhir.string_of_ParseError err)
            | Typer.TypeError (pos, err) ->
                flush stdout;
                PPrint.ToChannel.pretty 1.0 80 stderr (PPrint.hardline ^^ Typer.type_error_to_doc pos err ^^ PPrint.hardline);
                flush stderr);
        repl env

let () =
    Hashtbl.randomize ();
    print_endline "R1ML prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.";
    repl (Typer.Env.interactive ())

