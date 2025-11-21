type 'a t =
  | Not of 'a  (** [!t] *)
  | Xor of ('a * 'a)  (** [t1 ^ t2] *)
  | And of ('a * 'a)  (** [t1 & t2] *)
  | Or of ('a * 'a)  (** [t1 | t2] *)

let map f = function
  | Not t -> Not (f t)
  | And (lhs, rhs) -> And (f lhs, f rhs)
  | Or (lhs, rhs) -> Or (f lhs, f rhs)
  | Xor (lhs, rhs) -> Xor (f lhs, f rhs)

let pp pp format = function
  | Not term -> Format.fprintf format "! %a" pp term
  | And (lhs, rhs) -> Format.fprintf format "(%a & %a)" pp lhs pp rhs
  | Xor (lhs, rhs) -> Format.fprintf format "(%a ^ %a)" pp lhs pp rhs
  | Or (lhs, rhs) -> Format.fprintf format "(%a | %a)" pp lhs pp rhs

let traverse f s = function
  | Not t ->
      let s, v = f s t in
      (s, Not v)
  | Xor (lhs, rhs) ->
      let s, lhs = f s lhs in
      let s, rhs = f s rhs in
      (s, Xor (lhs, rhs))
  | And (lhs, rhs) ->
      let s, lhs = f s lhs in
      let s, rhs = f s rhs in
      (s, And (lhs, rhs))
  | Or (lhs, rhs) ->
      let s, lhs = f s lhs in
      let s, rhs = f s rhs in
      (s, Or (lhs, rhs))

let iter f t = ignore (traverse (fun _ x -> ((), f x)) () t)
