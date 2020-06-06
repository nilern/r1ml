open FcType
open FcTerm

module Env = Env

type 'a typing = 'a TyperSigs.typing

module rec E : TyperSigs.ELABORATION = Elaboration.Make(C)(M)
and C : TyperSigs.CHECKING = Checking.Make(E)(M)
and M : TyperSigs.MATCHING = Matching.Make(E)

(* # REPL support *)

let check_interaction env : Ast.Term.stmt -> stmt typing = function
    | Ast.Term.Def ((_, ({pat = name; _} as lvalue), expr) as def) ->
        let env = Env.push_struct env (Vector.singleton (lvalue, expr)) in
        let {TyperSigs.term; typ; eff} = C.deftype env def in
        Env.repl_define env {name; typ};
        {term = Def term; typ; eff}
    | Ast.Term.Expr expr ->
        let {TyperSigs.term; typ; eff} = C.typeof env expr in
        {term = Expr term; typ; eff}

