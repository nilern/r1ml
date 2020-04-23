type t
    = String of string
    | Fresh of int
    | Fring of string * int

let counter = ref 0

let fresh () = 
    let i = !counter in
    counter := i + 1;
    Fresh i

let freshen name =
    let i = !counter in
    counter := i + 1;
    match name with
    | String s -> Fring (s, i)
    | Fresh _ -> Fresh i
    | Fring (s, _) -> Fring (s, i)

let of_string str = String str

let compare = compare

let to_doc = function
    | String s -> PPrint.string s
    | Fresh n -> PPrint.string ("__" ^ Int.to_string n)
    | Fring (s, n) -> PPrint.string (s ^ "__" ^ Int.to_string n)

type name = t

module Map = Map.Make(struct
    type t = name
    let compare = compare
end)

