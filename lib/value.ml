type t =
  | VBool of bool
  | VArray of t Array.t
  | VFunction of { origin : string; value : t list -> t }

let rec pp format = function
  | VBool true -> Format.fprintf format "1"
  | VBool false -> Format.fprintf format "0"
  | VArray array ->
      let pp_sep format () = Format.pp_print_string format ", " in
      Format.fprintf format "[%a]" (Format.pp_print_array ~pp_sep pp) array
  | VFunction fn -> Format.fprintf format "%s" fn.origin

(** Bool *)

let true' = VBool true
let false' = VBool false
let not = function VBool e -> VBool (not e) | _ -> assert false

let ( lxor ) lhs rhs =
  match (lhs, rhs) with
  | VBool lhs, VBool rhs -> VBool (lhs <> rhs)
  | _, _ -> assert false

let ( land ) lhs rhs =
  match (lhs, rhs) with
  | VBool lhs, VBool rhs -> VBool (lhs && rhs)
  | _, _ -> assert false

let ( lor ) lhs rhs =
  match (lhs, rhs) with
  | VBool lhs, VBool rhs -> VBool (lhs || rhs)
  | _, _ -> assert false

let as_bool = function VBool bool -> bool | _ -> assert false

(** Array *)

let as_array = function VArray array -> array | _ -> assert false

let rec split2 lhs =
  match lhs with
  | VBool _ | VFunction _ -> assert false
  | VArray [| lhs; rhs |] -> (lhs, rhs)
  | VArray values ->
      let values = Array.map split2 values in
      let lhs, rhs = Array.split values in
      (VArray lhs, VArray rhs)

let get i = function VArray array -> array.(i) | _ -> assert false

let anticirc = function
  | VArray values as cir0 ->
      let cardinal = Array.length values in
      let circs =
        Array.init (cardinal - 1) @@ fun i ->
        let i = i + 1 in
        let value =
          Array.init cardinal (fun n ->
              let index = (n + i) mod cardinal in
              values.(index))
        in
        VArray value
      in
      VArray (Array.append [| cir0 |] circs)
  | _ -> assert false

let circ = function
  | VArray values as cir0 ->
      let cardinal = Array.length values in
      let circs =
        Array.init (cardinal - 1) @@ fun i ->
        let i = i + 1 in
        let value =
          Array.init cardinal (fun n ->
              let index = (cardinal + (n - i)) mod cardinal in
              values.(index))
        in
        VArray value
      in
      VArray (Array.append [| cir0 |] circs)
  | _ -> assert false

let tabulate size f =
  let array = Array.init size f in
  VArray array

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
  | VFunction fn_ident -> fn_ident.value
  | _ -> assert false

(** Value *)

let rec map2' f lhs rhs =
  match (lhs, rhs) with
  | VBool lhs, VBool rhs -> VBool (f lhs rhs)
  | VArray lhs, VArray rhs -> VArray (Array.map2 (map2' f) lhs rhs)
  | VBool _, VArray _ | VArray _, VBool _ | VFunction _, _ | _, VFunction _ ->
      assert false

let rec map2 f lhs rhs =
  match (lhs, rhs) with
  | (VBool _ as lhs), (VBool _ as rhs) -> f lhs rhs
  | VArray lhs, VArray rhs -> VArray (Array.map2 (map2 f) lhs rhs)
  | VBool _, VArray _ | VArray _, VBool _ | VFunction _, _ | _, VFunction _ ->
      assert false

let rec map' f = function
  | VBool b -> VBool (f b)
  | VArray a -> VArray (Array.map (map' f) a)
  | VFunction _ -> assert false

(*let rec pp format = function
  | VBool true -> Format.fprintf format "1"
  | VBool false -> Format.fprintf format "0"
  | VArray array ->
      let pp_sep format () = Format.pp_print_string format ", " in
      Format.fprintf format "[%a]" (Format.pp_print_array ~pp_sep pp) array
  | VFunction (fn, tys) ->
      let pp_none _format () = () in
      let pp_option =
        Format.pp_print_option ~none:pp_none @@ fun format tys ->
        Format.fprintf format "[%a]" Pp.pp_tys tys
      in
      Format.fprintf format "%a%a" Ast.FnIdent.pp fn pp_option tys*)

(* let as_bool = function VBool s -> Some s | VFunction _ | VArray _ -> None *)

let rec mapn' level f values =
  (*    let () = Format.eprintf "level = %u\n" level in*)
  match level with
  | 0 -> f values
  | level ->
      (*        let () =
          List.iter (fun value -> Format.eprintf "%a\n" pp value) values
        in*)
      let first = List.nth values 0 in
      let length = first |> as_array |> Array.length in
      let array = Array.init length (fun i -> mapn'' level i f values) in
      VArray array

and mapn'' level i f values =
  let values = List.map (fun value -> get i value) values in
  mapn' (level - 1) f values
