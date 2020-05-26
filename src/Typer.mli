(* Typechecking Facade *)

type 'a typing = 'a TyperSigs.typing

module Env : sig
    type t

    val interactive : unit -> t
end

val check_interaction : Env.t -> Ast.Term.stmt -> FcTerm.stmt typing

