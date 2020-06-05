module IntMap = Map.Make(Int) (* HACK *)

module Effect = Ast.Effect

type kind
    = ArrowK of kind * kind
    | TypeK

type effect = Effect.t

type bv = {depth : int; sibli : int}

type level = int

type binding = Name.t * kind

type ov = binding * level

type uvv =
    | Unassigned of Name.t * level
    | Assigned of typ

and uv = uvv ref

and abs =
    | Exists of kind Vector1.t * locator * t
    | NoE of t

and t =
    | Pi of kind Vector.t * locator * t * effect * abs
    | Record of t field Vector.t
    | Fn of Name.t * t
    | App of t * t
    | Type of abs
    | Use of binding
    | Bv of bv
    | Ov of ov
    | Uv of uv
    | Int
    | Bool

and locator =
    | PiL of kind Vector.t * effect * locator
    | RecordL of locator field Vector.t
    | TypeL of path
    | Hole

and 'a field = {label : string; typ : 'a}

and path =
    | AppP of path * path
    | BvP of bv
    | OvP of ov
    | UvP of uv

and coercion =
    | Refl of typ
    | Symm of coercion
    | Trans of coercion * coercion
    | Comp of coercion * coercion
    | Inst of coercion * typ
    | AUse of Name.t
    | TypeCo of coercion
    | Patchable of coercion ref

and typ = t
and template = locator

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec kind_to_doc = function
    | ArrowK (domain, codomain) ->
        PPrint.prefix 4 1 (domain_kind_to_doc domain)
            (PPrint.string "->" ^^ PPrint.blank 1 ^^ kind_to_doc codomain)
    | TypeK -> PPrint.star

and domain_kind_to_doc domain = match domain with
    | ArrowK _ -> PPrint.parens (kind_to_doc domain)
    | _ -> kind_to_doc domain

let kinds_to_doc kinds = PPrint.separate_map (PPrint.break 1) kind_to_doc kinds

let rec abs_to_doc : abs -> PPrint.document = function
    | Exists (params, locator, body) ->
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "exists" ^/^ kinds_to_doc (Vector1.to_list params)))
            (PPrint.dot ^^ PPrint.blank 1
                ^^ PPrint.parens (locator_to_doc locator ^^ PPrint.comma ^/^ to_doc body))
    | NoE typ -> to_doc typ

and to_doc = function
    | Pi (universals, locator, domain, eff, codomain) ->
        if Vector.length universals > 0
        then PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ kinds_to_doc (Vector.to_list universals)))
                 (PPrint.dot ^^ PPrint.blank 1
                  ^^ PPrint.prefix 4 1 (PPrint.parens (locator_to_doc locator ^^ PPrint.comma ^/^ to_doc domain))
                         (Ast.Effect.arrow eff ^^ PPrint.blank 1 ^^ abs_to_doc codomain))
        else PPrint.prefix 4 1 (domain_to_doc domain) 
                 (Ast.Effect.arrow eff ^^ PPrint.blank 1 ^^ abs_to_doc codomain)
    | Record fields ->
        PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc (Vector.to_list fields)
    | Fn (param, body) ->
        PPrint.prefix 4 1
            (PPrint.string "fun" ^^ PPrint.blank 1 ^^ Name.to_doc param
                 ^^ PPrint.blank 1 ^^ PPrint.dot)
            (to_doc body)
    | App (callee, arg) -> PPrint.group (callee_to_doc callee ^/^ arg_to_doc arg)
    | Type typ -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ abs_to_doc typ)
    | Use (name, _) -> Name.to_doc name
    | Bv {depth; sibli} ->
        PPrint.caret ^^ PPrint.string (Int.to_string depth) ^^ PPrint.slash
            ^^ PPrint.string (Int.to_string sibli)
    | Ov ((name, _), _) -> Name.to_doc name
    | Uv uv -> uv_to_doc uv
    | Int -> PPrint.string "__int"
    | Bool -> PPrint.string "__bool"

and domain_to_doc = function
    | (Pi _ | Fn _) as domain -> PPrint.parens (to_doc domain)
    | Uv uv ->
        (match !uv with
        | Assigned typ -> domain_to_doc typ
        | Unassigned _ -> uv_to_doc uv)
    | domain -> to_doc domain

and callee_to_doc = function
    | (Pi _ | Fn _) as callee -> PPrint.parens (to_doc callee)
    | Uv uv ->
        (match !uv with
        | Assigned typ -> callee_to_doc typ
        | Unassigned _ -> uv_to_doc uv)
    | callee -> to_doc callee

and arg_to_doc = function
    | (Pi _ | Fn _ | App _) as arg -> PPrint.parens (to_doc arg)
    | Uv uv ->
        (match !uv with
        | Assigned typ -> arg_to_doc typ
        | Unassigned _ -> uv_to_doc uv)
    | arg -> to_doc arg

and field_to_doc {label; typ} =
    PPrint.string label ^/^ PPrint.colon ^/^ to_doc typ

and locator_to_doc = function
    | PiL (universals, eff, codomain) ->
        if Vector.length universals > 0
        then PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ kinds_to_doc (Vector.to_list universals)))
                 (PPrint.dot ^^ PPrint.blank 1
                  ^^ (PPrint.infix 4 1 (Ast.Effect.arrow eff) PPrint.underscore (locator_to_doc codomain)))
        else (PPrint.infix 4 1 (Ast.Effect.arrow eff) PPrint.underscore (locator_to_doc codomain))
    | RecordL fields ->
        PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            (fun {label; typ} -> PPrint.string label ^/^ PPrint.colon ^/^ locator_to_doc typ)
            (Vector.to_list fields)
    | TypeL path -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ path_to_doc path)
    | Hole -> PPrint.underscore

and binding_to_doc (name, kind) =
    PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc kind)

and bindings_to_doc bindings = PPrint.separate_map (PPrint.break 1) binding_to_doc bindings

and universal_to_doc universals body =
    PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ bindings_to_doc (Vector.to_list universals)))
        (PPrint.dot ^^ PPrint.blank 1 ^^ body)

and path_to_doc path = to_doc (of_path path)

and uv_to_doc uv = match !uv with
    | Unassigned (name, _) -> PPrint.qmark ^^ Name.to_doc name
    | Assigned t -> to_doc t

and of_path = function
    | AppP (callee, arg) -> App (of_path callee, of_path arg)
    | BvP bv -> Bv bv
    | UvP uv ->
        (match !uv with
        | Assigned typ -> typ
        | Unassigned _ -> Uv uv)
    | OvP ov -> Ov ov

let rec coercion_to_doc = function
    | Refl typ -> to_doc typ
    | Symm co -> PPrint.string "symm" ^^ PPrint.blank 1 ^^ coercion_to_doc co
    | Trans (co, co') ->
        PPrint.infix 4 1 (PPrint.bquotes (PPrint.string "o"))
            (coercion_to_doc co) (andco_to_doc co')
    | Comp (ctor_co, arg_co) -> PPrint.prefix 4 1 (ctorco_to_doc ctor_co) (argco_to_doc arg_co)
    | Inst (co, arg) -> PPrint.infix 4 1 PPrint.at (instantiee_to_doc co) (to_doc arg)
    | AUse name -> Name.to_doc name
    | TypeCo co -> PPrint.brackets (PPrint.equals ^^ PPrint.break 1 ^^ (coercion_to_doc co))
    | Patchable {contents} -> coercion_to_doc contents

and andco_to_doc = function
    | Trans _ as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

and ctorco_to_doc = function
    | (Symm _ | Trans _ | Inst _) as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

and argco_to_doc = function
    | (Trans _ | Inst _ | Comp _) as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

and instantiee_to_doc = function
    | (Symm _ | Trans _) as co -> PPrint.parens (coercion_to_doc co)
    | co -> coercion_to_doc co

let freshen (name, kind) = (Name.freshen name, kind)

let sibling = function
    | {contents = Unassigned (_, level)} -> ref (Unassigned (Name.fresh (), level))
    | {contents = Assigned _} -> failwith "unreachable"

let rec expose_path' depth substitution = function
    | AppP (callee, arg) ->
        AppP (expose_path' depth substitution callee, expose_path' depth substitution arg)
    | BvP {depth = depth'; sibli} as path ->
        if depth' = depth
        then Vector1.get substitution sibli
        else path
    | (OvP _ | UvP _) as path -> path

let rec expose_locator' depth substitution = function
    | PiL (params, eff, codomain) ->
        let depth = if Vector.length params > 0 then depth + 1 else depth in
        PiL (params, eff, expose_locator' depth substitution codomain)
    | RecordL fields ->
        RecordL (Vector.map (fun {label; typ} ->
                                {label; typ = expose_locator' depth substitution typ}) fields)
    | TypeL path -> TypeL (expose_path' depth substitution path)
    | Hole -> Hole

let rec expose_abs' depth substitution = function
    | Exists (params, locator, body) ->
        Exists (params, expose_locator' depth substitution locator, expose' depth substitution body)
    | NoE typ -> NoE (expose' depth substitution typ)

and expose' depth substitution = function
    | Pi (params, locator, domain, eff, codomain) ->
        let depth = if Vector.length params > 0 then depth + 1 else depth in
        Pi ( params, expose_locator' depth substitution locator, expose' depth substitution domain
           , eff, expose_abs' depth substitution codomain )
    | Record fields ->
        Record (Vector.map (fun {label; typ} ->
                                {label; typ = expose' depth substitution typ}) fields)
    | Type typ -> Type (expose_abs' depth substitution typ)
    | Fn (param, body) -> Fn (param, expose' (depth + 1) substitution body)
    | App (callee, arg) -> App (expose' depth substitution callee, expose' depth substitution arg)
    | Bv {depth = depth'; sibli} as path ->
        if depth' = depth
        then of_path (Vector1.get substitution sibli) (* OPTIMIZE *)
        else path
    | Uv {contents = Assigned typ} -> expose' depth substitution typ
    | (Use _ | Ov _ | Uv {contents = Unassigned _} | Int | Bool) as typ -> typ

let expose_abs = expose_abs' 0
let expose = expose' 0
let expose_locator = expose_locator' 0

let rec close_path' depth substitution = function
    | AppP (callee, arg) ->
        AppP (close_path' depth substitution callee, close_path' depth substitution arg)
    | OvP ((name, _), _) as path ->
        Name.Map.find_opt name substitution
            |> Option.fold ~some: (fun sibli -> BvP {depth; sibli}) ~none: path
    | (BvP _ | UvP _) as path -> path

let rec close_locator' depth substitution = function
    | PiL (params, eff, codomain) ->
        let depth = if Vector.length params > 0 then depth + 1 else depth in
        PiL (params, eff, close_locator' depth substitution codomain)
    | RecordL fields ->
        RecordL (Vector.map (fun {label; typ} ->
                                {label; typ = close_locator' depth substitution typ}) fields)
    | TypeL path -> TypeL (close_path' depth substitution path)
    | Hole -> Hole

let rec close_abs' depth substitution = function
    | Exists (params, locator, body) ->
        Exists (params, close_locator' depth substitution locator, close' depth substitution body)
    | NoE typ -> NoE (close' depth substitution typ)

and close' depth substitution = function
    | Pi (params, locator, domain, eff, codomain) ->
        let depth = if Vector.length params > 0 then depth + 1 else depth in
        Pi ( params, close_locator' depth substitution locator, close' depth substitution domain
           , eff, close_abs' depth substitution codomain )
    | Record fields ->
        Record (Vector.map (fun {label; typ} ->
                                {label; typ = close' depth substitution typ}) fields)
    | Type typ -> Type (close_abs' depth substitution typ)
    | Fn (param, body) -> Fn (param, close' (depth + 1) substitution body)
    | App (callee, arg) -> App (close' depth substitution callee, close' depth substitution arg)
    | Ov ((name, _), _) as typ ->
        Name.Map.find_opt name substitution
            |> Option.fold ~some: (fun sibli -> Bv {depth; sibli}) ~none: typ
    | Uv {contents = Assigned typ} -> close' depth substitution typ
    | (Use _ | Bv _ | Uv {contents = Unassigned _} | Int | Bool) as typ -> typ

let close = close' 0
let close_locator = close_locator' 0
let close_abs = close_abs' 0

