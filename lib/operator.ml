type 'a t =
  | Not of 'a  (** [!t] *)
  | Xor of ('a * 'a)  (** [t1 ^ t2] *)
  | And of ('a * 'a)  (** [t1 & t2] *)
  | Or of ('a * 'a)  (** [t1 | t2] *)

let iter f = function
  | Not a -> f a
  | Xor (a, b) | And (a, b) | Or (a, b) ->
      f a;
      f b
