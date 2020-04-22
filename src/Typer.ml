open FcType
open FcTerm

type 'a typing = {term : 'a; typ : FcType.t; eff : Ast.effect}

exception TypeError

module Env = struct
    type scope
        = Repl of (Name.t, lvalue) Hashtbl.t
        | Existential of binding list ref * level
        | Fn of lvalue 

    type t = {scopes : scope list; current_level : level ref}

    let initial_level = 1

    let interactive () =
        { scopes = [Repl (Hashtbl.create 0); Existential (ref [], initial_level)]
        ; current_level = ref initial_level }

    let repl_define env ({name; _} as binding) =
        let rec define scopes =
            match scopes with
            | Repl kvs :: _ -> Hashtbl.replace kvs name binding
            | _ :: scopes' -> define scopes'
            | [] -> failwith "Typer.Env.repl_define: non-interactive type environment"
        in define env.scopes

    let with_incremented_level {current_level; _} body =
        current_level := !current_level + 1;
        Fun.protect body
            ~finally:(fun () -> current_level := !current_level - 1)

    let with_existential ({scopes; current_level} as env) f =
        with_incremented_level env (fun () ->
            let bindings = ref [] in
            f {env with scopes = Existential (bindings, !current_level) :: scopes} bindings
        )

    let generate env binding =
        let rec generate = function
            | Existential (bindings, level) :: _ ->
                bindings := binding :: !bindings;
                (binding, level)
            | _ :: scopes' -> generate scopes'
            | [] -> failwith "Typer.Env.generate: missing root Existential scope"
        in generate env.scopes

    let get env name =
        let rec get scopes name =
            match scopes with
            | Repl kvs :: scopes' ->
                (match Hashtbl.find_opt kvs name with
                | Some def -> def
                | None -> get scopes' name)
            | Fn ({name = name'; _} as def) :: scopes' ->
                if name' = name then def else get scopes' name
            | Existential _ :: scopes' -> get scopes' name
            | [] -> raise TypeError
        in get env.scopes name
end

(* # Effects *)

let join_effs eff eff' = match (eff, eff') with
    | (Ast.Pure, Ast.Pure) -> Ast.Pure
    | _ -> Impure

(* # Expressions *)

let rec typeof env (expr : Ast.expr Ast.with_pos) = match expr.v with
    | Ast.Proxy typ ->
        let typ = kindcheck env typ in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Pure}
    | Ast.Use name ->
        let ({typ; _} as def) : lvalue = Env.get env name in
        {term = {expr with v = Use def}; typ; eff = Pure}
    | Ast.Const c -> {term = {expr with v = Const c}; typ = Int; eff = Pure}

and check env ((params, _) as typ : FcType.abs) (expr : Ast.expr Ast.with_pos) =
    let check_concrete_unconditional env (typ : FcType.t) (expr : Ast.expr Ast.with_pos) =
        let {term; typ = expr_typ; eff} = typeof env expr in
        let coerce = subtype expr.pos true env expr_typ typ in
        {term = {expr with v = App ({v = coerce; pos = expr.pos}, term)}; typ; eff}
    in
    let rec implement env ((params, body) as typ : FcType.abs) (expr : Ast.expr Ast.with_pos) =
        match expr.v with
        | Ast.If (cond, conseq, alt) ->
            let {term = cond; eff = cond_eff} = check env ([], Bool) cond in
            let {term = conseq; eff = conseq_eff} = implement env typ conseq in
            let {term = alt; eff = alt_eff} = implement env typ alt in
            { term = {expr with v = If (cond, conseq, alt)}
            ; typ = body
            ; eff = join_effs cond_eff (join_effs conseq_eff alt_eff) }
        | _ ->
            (match params with
            | _ :: _ -> failwith "todo: create axioms"
            | [] -> ());
            check_concrete_unconditional env body expr
    in
    (match params with
    | _ :: _ -> failwith "todo: hoist abstract types"
    | [] -> ());
    implement env typ expr

(* # Definitions and Statements *)

and deftype env : Ast.def -> def typing = function
    | (pos, {Ast.pat = name; ann = Some ann}, expr) ->
        let abs_typ = kindcheck env ann in
        let {term = expr; typ; eff} = check env abs_typ expr in
        {term = (pos, {name; typ}, expr); typ; eff}
    | (pos, {Ast.pat = name; ann = None}, expr) ->
        let {term = expr; typ; eff} = typeof env expr in
        {term = (pos, {name; typ}, expr); typ; eff}

(* # Type Elaboration *)

and kindcheck env (typ : Ast.typ Ast.with_pos) =
    let rec elaborate env (typ : Ast.typ Ast.with_pos) =
        match typ.v with
        | Ast.Path expr ->
            (match typeof env {typ with v = expr} with
            | {term = _; typ = Type (params, typ); eff = Pure} ->
                (* FIXME: capture-avoiding substitution: *)
                List.iter (fun param -> ignore (Env.generate env param)) params;
                typ
            | _ -> raise TypeError)
        | Ast.Singleton expr ->
            (match typeof env expr with
            | {term = _; typ; eff = Pure} -> typ
            | _ -> raise TypeError)
        | Ast.Type ->
            let binding = (Name.fresh (), TypeK) in
            let ov = Env.generate env binding in
            Type ([], Ov ov)
        | Ast.Int -> Int
        | Ast.Bool -> Bool
    in
    Env.with_existential env (fun env params ->
        let typ = elaborate env typ in
        (!params, typ)
    )

(* # Subtyping *)

and subtype pos (occ : bool) env (typ : FcType.t) (super : FcType.t) = match (typ, super) with
    | (Int, Int) ->
        let lvalue = {name = Name.fresh (); typ} in
        Fn (lvalue, {v = Use lvalue; pos})

(* # REPL support *)

let check_interaction env : Ast.stmt -> stmt typing = function
    | Ast.Def ((_, {pat = name; _}, _) as def) ->
        let {term; typ; eff} = deftype env def in
        Env.repl_define env {name; typ};
        {term = Def term; typ; eff}
    | Ast.Expr expr ->
        let {term; typ; eff} = typeof env expr in
        {term = Expr term; typ; eff}

