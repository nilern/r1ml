let prompt = "R1ML> "

let rec repl () =
    match LNoise.linenoise prompt with
    | None -> ()
    | Some input ->
        let _ = LNoise.history_add input in
        print_endline input;
        repl ()

let () =
    print_endline "R1ML prototype REPL. Press Ctrl+D (on *nix, Ctrl+Z on Windows) to quit.";
    repl ()

