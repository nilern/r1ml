type 'a t

val singleton : 'a -> 'a t

val to_vector : 'a t -> 'a Vector.t
val of_vector : 'a Vector.t -> 'a t option
val of_list : 'a list -> 'a t option
val to_list : 'a t -> 'a list

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val map : ('a -> 'b) -> 'a t -> 'b t

val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a

