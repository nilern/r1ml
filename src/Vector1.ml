type 'a t = 'a Vector.t

let singleton = Vector.singleton

let of_vector vec =
    if Vector.length vec > 0
    then Some vec
    else None

let to_vector = Fun.id

let of_list = function
    | (_ :: _) as ls -> Some (Vector.of_list ls)
    | [] -> None

let to_list = Vector.to_list

let fold_left = Vector.fold_left
let map = Vector.map

let fold_left2 = Vector.fold_left2

