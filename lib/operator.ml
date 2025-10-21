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

let pp pp format = function
  | Not term -> Format.fprintf format "! %a" pp term
  | And (lhs, rhs) -> Format.fprintf format "(%a & %a)" pp lhs pp rhs
  | Xor (lhs, rhs) -> Format.fprintf format "(%a ^ %a)" pp lhs pp rhs
  | Or (lhs, rhs) -> Format.fprintf format "(%a | %a)" pp lhs pp rhs
