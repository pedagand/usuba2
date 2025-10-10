module Ty = struct
  type signature = {
    tyvars : Ast.TyIdent.t option;
    parameters : ty list;
    return_type : ty;
  }

  and ty =
    | TBool
    | TFun of signature
    | TVar of Ast.TyIdent.t
    | TNamedTuple of { name : Ast.TyDeclIdent.t; size : int; ty : ty }

  type lty = Lty of { t : (Ast.TyDeclIdent.t * int) list; ty : ty }

  let pp_tyvar_opt format = Format.pp_print_option Ast.TyIdent.pp format

  let rec pp format = function
    | TBool -> Format.fprintf format "bool"
    | TNamedTuple { name; size = _; ty } ->
        Format.fprintf format "%a %a" Ast.TyDeclIdent.pp name pp ty
    | TFun { tyvars; parameters; return_type } ->
        Format.fprintf format "fn %a(%a) -> %a" pp_tyvar_opt tyvars pps
          parameters pp return_type
    | TVar name -> Format.fprintf format "%a" Ast.TyIdent.pp name

  and pps format =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
      pp format

  let rec equal lhs rhs =
    match (lhs, rhs) with
    | TBool, TBool -> true
    | TFun _lhs, TFun _rhs -> failwith ""
    | TVar lhs, TVar rhs -> Ast.TyIdent.equal lhs rhs
    | ( TNamedTuple { name = lname; size = lsize; ty = lty },
        TNamedTuple { name = rname; size = rsize; ty = rty } ) ->
        Ast.TyDeclIdent.equal lname rname
        && Int.equal lsize rsize && equal lty rty
    | _, _ -> false

  let lequal lhs rhs =
    match (lhs, rhs) with
    | Lty { t = lt; ty = lty }, Lty { t = rt; ty = rty } ->
        if List.compare_lengths lt rt <> 0 then false
        else
          List.for_all2
            (fun (lname, lsize) (rname, rsize) ->
              Ast.TyDeclIdent.equal lname rname && Int.equal lsize rsize)
            lt rt
          && equal lty rty

  let cstrql lhs rhs =
    match (lhs, rhs) with
    | TBool, TBool -> true
    | TNamedTuple { name = lname; _ }, TNamedTuple { name = rname; _ } ->
        Ast.TyDeclIdent.equal lname rname
    | _, _ -> false

  let lcstreq lhs rhs =
    match (lhs, rhs) with
    | Lty { t = lt; ty = lty }, Lty { t = rt; ty = rty } -> (
        match (lt, rt) with
        | [], [] -> cstrql lty rty
        | (l, _) :: _, (r, _) :: _ -> Ast.TyDeclIdent.equal l r
        | _, _ -> false)

  let is_bool = ( = ) TBool
  let named_tuple name size ty = TNamedTuple { name; size; ty }
  let lty t ty = Lty { t; ty }

  let to_ty = function
    | Lty { t; ty } ->
        List.fold_right
          (fun (name, size) ty -> TNamedTuple { name; size; ty })
          t ty

  (* let prefix = function
    | Lty { t = (ty, _) :: _; ty = _ }
    | Lty { t = []; ty = TNamedTuple { name = ty; _ } } ->
        Some ty
    | _ -> None *)

  let cstr = function
    | TNamedTuple { name; _ } -> Some name
    | TBool | TFun _ | TVar _ -> None

  let view = function Lty { t; _ } -> t
  let length_view = function Lty { t; _ } -> List.length t

  let elt = function
    | TNamedTuple { ty; _ } -> Some ty
    | TBool | TFun _ | TVar _ -> None

  let rec remove_prefix ctsrs ty =
    match ctsrs with
    | [] -> Some ty
    | t :: q -> (
        match ty with
        | TBool | TFun _ | TVar _ -> None
        | TNamedTuple { name; ty; _ } ->
            if Ast.TyDeclIdent.equal t name then remove_prefix q ty else None)
end

type t = VBool of bool | VArray of t Array.t | VFunction of Ast.FnIdent.t

let rec pp format = function
  | VBool true -> Format.fprintf format "1"
  | VBool false -> Format.fprintf format "0"
  | VArray array ->
      let pp_sep format () = Format.pp_print_string format ", " in
      Format.fprintf format "[%a]" (Format.pp_print_array ~pp_sep pp) array
  | VFunction fn -> Format.fprintf format "%a" Ast.FnIdent.pp fn

let true' = VBool true
let false' = VBool false

let not = function
  | VBool e -> VBool (not e)
  | VArray _ | VFunction _ -> failwith "not can only be applied to scalar."

let ( lxor ) lhs rhs =
  match (lhs, rhs) with
  | VBool lhs, VBool rhs -> VBool (lhs <> rhs)
  | _, _ -> failwith "(lxor) can only be applied to two scalar"

let ( land ) lhs rhs =
  match (lhs, rhs) with
  | VBool lhs, VBool rhs -> VBool (lhs && rhs)
  | _, _ -> failwith "(land) can only be applied to two scalar"

let ( lor ) lhs rhs =
  match (lhs, rhs) with
  | VBool lhs, VBool rhs -> VBool (lhs || rhs)
  | _, _ -> failwith "(lor) can only be applied to two scalar"

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

let as_array = function
  | VArray array -> Some array
  | VBool _ | VFunction _ -> None

let as_function = function
  | VFunction fn_ident -> Some fn_ident
  | VBool _ | VArray _ -> None

let rec split2 lhs =
  match lhs with
  | VBool _ | VFunction _ -> invalid_arg ""
  | VArray [| lhs; rhs |] -> (lhs, rhs)
  | VArray values ->
      let values = Array.map split2 values in
      let lhs, rhs = Array.split values in
      (VArray lhs, VArray rhs)

let rec map' f = function
  | VBool b -> VBool (f b)
  | VArray a -> VArray (Array.map (map' f) a)
  | VFunction _ -> assert false

let get i = function
  | VArray array -> array.(i)
  | VBool _ as v -> if i = 0 then v else assert false
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

let anticirc = function
  | (VBool _ | VFunction _) as e -> VArray (Array.make 1 e)
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

let circ = function
  | (VBool _ | VFunction _) as e -> VArray (Array.make 1 e)
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

let as_bool = function VBool s -> Some s | VFunction _ | VArray _ -> None

let rec mapn' level f values =
  (*    let () = Format.eprintf "level = %u\n" level in*)
  match level with
  | 0 -> f values
  | level ->
      (*        let () =
          List.iter (fun value -> Format.eprintf "%a\n" pp value) values
        in*)
      let first = List.nth values 0 in
      let length = first |> as_array |> Option.get |> Array.length in
      let array = Array.init length (fun i -> mapn'' level i f values) in
      VArray array

and mapn'' level i f values =
  let values = List.map (fun value -> get i value) values in
  mapn' (level - 1) f values

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
  let lookup s i = as_array s |> Option.map (Fun.flip Array.get i) |> Option.get
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
