type 'a t =
  | Not of 'a  (** [!t] *)
  | Xor of ('a * 'a)  (** [t1 ^ t2] *)
  | And of ('a * 'a)  (** [t1 & t2] *)
  | Or of ('a * 'a)  (** [t1 | t2] *)

val iter : ('a -> unit) -> 'a t -> unit
val traverse : ('a -> 'i -> 'a * 'o) -> 'a -> 'i t -> 'a * 'o t
val map : ('a -> 'b) -> 'a t -> 'b t
val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
