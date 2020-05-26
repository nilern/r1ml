open FcType

type effect = Effect.t
type typ = t
type abs = FcType.abs

type error =
    | Unbound of Name.t
    | MissingField of typ * string
    | SubEffect of effect * effect
    | SubType of typ * typ
    | Unify of typ * typ
    | Unsolvable of FcTerm.expr Ast.with_pos FcType.residual
    | ImpureType of Ast.Term.expr
    | Escape of FcType.ov
    | Occurs of FcType.uv * typ
    | Polytype of abs
    | PolytypeInference of abs
    | RecordArticulation of typ
    | RecordArticulationL of FcType.locator

exception TypeError of Ast.span * error

let (^/^) = PPrint.(^/^)

let rec cause_to_doc = function
    | Unbound name -> PPrint.string "unbound name" ^/^ Name.to_doc name
    | MissingField (typ, label) -> FcType.to_doc typ ^/^ PPrint.string "is missing field" ^/^ PPrint.string label
    | SubEffect (eff, eff') -> Ast.Effect.to_doc eff ^/^ PPrint.string "is not a subeffect of" ^/^ Ast.Effect.to_doc eff'
    | SubType (typ, super) -> FcType.to_doc typ ^/^ PPrint.string "is not a subtype of" ^/^ FcType.to_doc super
    | Unify (typ, typ') -> FcType.to_doc typ ^/^ PPrint.string "does no unify with" ^/^ FcType.to_doc typ'
    | Unsolvable residual ->
        let rec to_doc = function
            | Axioms (_, residual) | Skolems (_, residual) -> to_doc residual
            | Residuals (residual, residual') ->
                to_doc residual ^/^ PPrint.string "and" ^/^ to_doc residual'
            | Sub (_, typ, _, super, _) -> cause_to_doc (SubType (typ, super))
            | Unify (typ, typ', _) -> cause_to_doc (Unify (typ, typ'))
        in to_doc residual
    | ImpureType expr -> PPrint.string "impure type expression" ^/^ Ast.Term.expr_to_doc expr
    | Escape ((name, _), _) -> Name.to_doc name ^/^ PPrint.string "would escape"
    | Occurs (uv, typ) -> FcType.to_doc (Uv uv) ^/^ PPrint.string "occurs in" ^/^ FcType.to_doc typ
    | Polytype typ -> FcType.abs_to_doc typ ^/^ PPrint.string "is not a monotype"
    | PolytypeInference typ -> PPrint.string "tried to infer polytype" ^/^ FcType.abs_to_doc typ
    | RecordArticulation typ ->
        PPrint.string "tried to articulate record type" ^/^ FcType.to_doc typ
    | RecordArticulationL typ ->
        PPrint.string "tried to articulate record type" ^/^ FcType.locator_to_doc typ

let to_doc (({pos_fname; _}, _) as span : Ast.span) err =
    PPrint.prefix 4 1 (PPrint.string "Type error in" ^/^ PPrint.string pos_fname ^/^ PPrint.string "at"
        ^/^ PPrint.string (Ast.span_to_string span) ^/^ PPrint.colon)
        (cause_to_doc err)

