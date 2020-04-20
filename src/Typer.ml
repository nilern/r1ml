open FcType
open FcTerm

type typing = {expr : expr; typ : FcType.t; eff : Ast.effect}

exception TypeError

module Env = struct
    type scope
        = Fn of def

    type t = scope list

    let rec get env name = match env with
        | Fn ({name = name'; _} as def) :: env' -> if name' = name then def else get env' name
        | [] -> raise TypeError
end

let rec kindof env = function
    | Ast.Path expr ->
        (match typeof env expr with
        | {expr = _; typ = Type typ; eff = Pure} -> typ
        | _ -> raise TypeError)
    | Ast.Int -> Int

and typeof env = function
    | Ast.Type {v = typ; _} ->
        let typ = kindof env typ in
        {expr = Proxy typ; typ = Type typ; eff = Pure}
    | Ast.Use name ->
        let ({typ; _} as def) : def = Env.get env name in
        {expr = Use def; typ; eff = Pure}
    | Ast.Const c -> {expr = Const c; typ = Int; eff = Pure}

