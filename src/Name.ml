type t
    = String of string

let of_string str = String str

let to_doc = function
    | String s -> PPrint.string s

