open FcType
open FcTerm

type 'a typing = {term : 'a; typ : FcType.t; eff : Ast.effect}

exception TypeError

module Env = struct
    type scope
        = Repl of (Name.t, lvalue) Hashtbl.t
        | Fn of lvalue 

    type t = scope list

    let interactive () = [Repl (Hashtbl.create 0)]

    let repl_define env ({name; _} as binding) = match env with
        | Repl kvs :: _ -> Hashtbl.replace kvs name binding
        | _ -> failwith "Typer.Env.repl_define: non-interactive type environment"

    let rec get env name = match env with
        | Repl kvs :: env' -> begin match Hashtbl.find_opt kvs name with
            | Some def -> def
            | None -> get env' name
        end
        | Fn ({name = name'; _} as def) :: env' -> if name' = name then def else get env' name
        | [] -> raise TypeError
end

let rec kindcheck env (typ : Ast.typ Ast.with_pos) = match typ.v with
    | Ast.Path expr ->
        (match typeof env {Ast.v = expr; pos = typ.pos} with
        | {term = _; typ = Type typ; eff = Pure} -> typ
        | _ -> raise TypeError)
    | Ast.Int -> Int

and typeof env (expr : Ast.expr Ast.with_pos) = match expr.v with
    | Ast.Proxy typ ->
        let typ = kindcheck env typ in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Pure}
    | Ast.Use name ->
        let ({typ; _} as def) : lvalue = Env.get env name in
        {term = {expr with v = Use def}; typ; eff = Pure}
    | Ast.Const c -> {term = {expr with v = Const c}; typ = Int; eff = Pure}

and check env (typ : FcType.t) (expr : Ast.expr Ast.with_pos) = match expr.v with
    | _ ->
        let {term; typ = expr_typ; eff} = typeof env expr in
        let coerce = subtype expr.pos true env expr_typ typ in
        {term = {expr with v = App ({v = coerce; pos = expr.pos}, term)}; typ; eff}

and deftype env : Ast.def -> def typing = function
    | (pos, {Ast.pat = name; ann = Some ann}, expr) ->
        let typ = kindcheck env ann in
        let {term = expr; eff} = check env typ expr in
        {term = (pos, {name; typ}, expr); typ; eff}
    | (pos, {Ast.pat = name; ann = None}, expr) ->
        let {term = expr; typ; eff} = typeof env expr in
        {term = (pos, {name; typ}, expr); typ; eff}

and subtype pos (occ : bool) env (typ : FcType.t) (super : FcType.t) = match (typ, super) with
    | (Int, Int) ->
        let lvalue = {name = Name.fresh (); typ} in
        Fn (lvalue, {v = Use lvalue; pos})

let check_interaction env : Ast.stmt -> stmt typing = function
    | Ast.Def ((_, {pat = name; _}, _) as def) ->
        let {term; typ; eff} = deftype env def in
        Env.repl_define env {name; typ};
        {term = Def term; typ; eff}
    | Ast.Expr expr ->
        let {term; typ; eff} = typeof env expr in
        {term = Expr term; typ; eff}

