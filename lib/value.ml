module type Boolean = sig
  type t

  val true' : t
  val false' : t
  val lnot : t -> t
  val ( land ) : t -> t -> t
  val ( lor ) : t -> t -> t
  val ( lxor ) : t -> t -> t
  val pp : Format.formatter -> t -> unit
end

module Bool : Boolean with type t = bool = struct
  type t = bool

  let true' = true
  let false' = false
  let lnot = not
  let ( land ) = ( && )
  let ( lor ) = ( || )
  let ( lxor ) = ( <> )
  let pp = Format.pp_print_bool
end

module Symbolical = struct
  type t = Bool of bool | Var of Ident.TermIdent.t | Op of t Operator.t

  let true' = Bool true
  let false' = Bool false
  let lnot e = Op (Operator.Not e)
  let ( land ) lhs rhs = Op (Operator.And (lhs, rhs))
  let ( lor ) lhs rhs = Op (Operator.Or (lhs, rhs))
  let ( lxor ) lhs rhs = Op (Operator.Xor (lhs, rhs))

  let rec pp format = function
    | Bool b -> Format.pp_print_bool format b
    | Var v -> Ident.TermIdent.pp format v
    | Op o -> Operator.pp pp format o
end

module Make (B : Boolean) = struct
  type t =
    | Bool of B.t
    | Array of t Array.t
    | Function of { origin : string; value : t list -> t }

  let rec pp format = function
    | Bool elt -> Format.fprintf format "%a" B.pp elt
    | Array array ->
        let pp_sep format () = Format.pp_print_string format ", " in
        Format.fprintf format "[%a]" (Format.pp_print_array ~pp_sep pp) array
    | Function fn -> Format.fprintf format "%s" fn.origin

  let equal = ( = )
  let true' = Bool B.true'
  let false' = Bool B.false'

  (** Bool *)
  let not = function Bool e -> Bool (B.lnot e) | _ -> assert false

  let ( lxor ) lhs rhs =
    match (lhs, rhs) with
    | Bool lhs, Bool rhs -> Bool B.(lhs lxor rhs)
    | _, _ -> assert false

  let ( land ) lhs rhs =
    match (lhs, rhs) with
    | Bool lhs, Bool rhs -> Bool B.(lhs land rhs)
    | _, _ -> assert false

  let ( lor ) lhs rhs =
    match (lhs, rhs) with
    | Bool lhs, Bool rhs -> Bool B.(lhs lor rhs)
    | _, _ -> assert false

  let as_bool = function Bool bool -> bool | _ -> assert false

  (** Array *)

  let as_array = function Array array -> array | _ -> assert false

  let rec split2 lhs =
    match lhs with
    | Bool _ | Function _ -> assert false
    | Array [| lhs; rhs |] -> (lhs, rhs)
    | Array values ->
        let values = Array.map split2 values in
        let lhs, rhs = Array.split values in
        (Array lhs, Array rhs)

  let get i = function Array array -> array.(i) | _ -> assert false

  let anticirc = function
    | Array values as cir0 ->
        let cardinal = Array.length values in
        let circs =
          Array.init (cardinal - 1) @@ fun i ->
          let i = i + 1 in
          let value =
            Array.init cardinal (fun n ->
                let index = (n + i) mod cardinal in
                values.(index))
          in
          Array value
        in
        Array (Array.append [| cir0 |] circs)
    | _ -> assert false

  let circ = function
    | Array values as cir0 ->
        let cardinal = Array.length values in
        let circs =
          Array.init (cardinal - 1) @@ fun i ->
          let i = i + 1 in
          let value =
            Array.init cardinal (fun n ->
                let index = (cardinal + (n - i)) mod cardinal in
                values.(index))
          in
          Array value
        in
        Array (Array.append [| cir0 |] circs)
    | _ -> assert false

  let tabulate size f =
    let array = Array.init size f in
    Array array

  module type S = sig
    val n : int
  end

  module type SNaperian = sig
    type idx

    val tabulate : (idx -> t) -> t
    val lookup : t -> idx -> t
  end

  module Naperian (S : S) : SNaperian = struct
    type idx = int

    let tabulate f = tabulate S.n f
    let lookup s i = as_array s |> Fun.flip Array.get i
  end

  module NaperianCompose (F : SNaperian) (G : SNaperian) : SNaperian = struct
    type idx = F.idx * G.idx

    let lookup fgs (i, j) = G.lookup (F.lookup fgs i) j
    let tabulate f = F.tabulate (fun i -> G.tabulate (fun j -> f (i, j)))
  end

  let naperian n =
    (module Naperian (struct
      let n = n
    end) : SNaperian)

  let naperian_compose f g =
    (module NaperianCompose ((val f : SNaperian)) ((val g : SNaperian))
    : SNaperian)

  (** [L R 'a -> R L 'a] *)
  let reindex_lr lhs rhs value =
    let module L = (val lhs : SNaperian) in
    let module R = (val rhs : SNaperian) in
    R.tabulate (fun c -> L.tabulate (fun r -> R.lookup (L.lookup value r) c))

  (** Functions *)

  let as_function = function
    | Function fn_ident -> fn_ident.value
    | _ -> assert false

  (** Value *)

  let rec map2' f lhs rhs =
    match (lhs, rhs) with
    | Bool lhs, Bool rhs -> Bool (f lhs rhs)
    | Array lhs, Array rhs -> Array (Array.map2 (map2' f) lhs rhs)
    | Bool _, Array _ | Array _, Bool _ | Function _, _ | _, Function _ ->
        assert false

  let rec map2 f lhs rhs =
    match (lhs, rhs) with
    | (Bool _ as lhs), (Bool _ as rhs) -> f lhs rhs
    | Array lhs, Array rhs -> Array (Array.map2 (map2 f) lhs rhs)
    | Bool _, Array _ | Array _, Bool _ | Function _, _ | _, Function _ ->
        assert false

  let rec map' f = function
    | Bool b -> Bool (f b)
    | Array a -> Array (Array.map (map' f) a)
    | Function _ -> assert false

  let rec mapn' level f values =
    match level with
    | 0 -> f values
    | level ->
        let first = List.nth values 0 in
        let length = first |> as_array |> Array.length in
        let array = Array.init length (fun i -> mapn'' level i f values) in
        Array array

  and mapn'' level i f values =
    let values = List.map (fun value -> get i value) values in
    mapn' (level - 1) f values
end
