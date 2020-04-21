type t
    = String of string
    | Fresh of int

let fresh =
    let counter = ref 0 in
    fun () ->
        let i = !counter in
        counter := i + 1;
        Fresh i

let of_string str = String str

let to_doc = function
    | String s -> PPrint.string s
    | Fresh n -> PPrint.string ("$" ^ Int.to_string n)

