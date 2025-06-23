module Ty = struct
  type signature = {
    tyvars : Ast.TyIdent.t list;
    parameters : ty list;
    return_type : ty;
  }

  and ty =
    | TBool
    | TFun of signature
    | TNamedTuple of { name : Ast.TyDeclIdent.t; size : int; ty : ty }

  type lty = Lty of { t : (Ast.TyDeclIdent.t * int) list; ty : ty }

  let is_bool = ( = ) TBool
end

type t =
  | VBool of bool
  | Varray of t Array.t
  | VFunction of Ast.FnIdent.t * Ast.ty list option

let true' = VBool true
let false' = VBool false

let not = function
  | VBool e -> VBool (not e)
  | Varray _ | VFunction _ -> failwith "not can only be applied to scalar."

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
  | Varray lhs, Varray rhs -> Varray (Array.map2 (map2' f) lhs rhs)
  | VBool _, Varray _ | Varray _, VBool _ | VFunction _, _ | _, VFunction _ ->
      assert false

let rec map2 f lhs rhs =
  match (lhs, rhs) with
  | (VBool _ as lhs), (VBool _ as rhs) -> f lhs rhs
  | Varray lhs, Varray rhs -> Varray (Array.map2 (map2 f) lhs rhs)
  | VBool _, Varray _ | Varray _, VBool _ | VFunction _, _ | _, VFunction _ ->
      assert false

let as_array = function
  | Varray array -> Some array
  | VBool _ | VFunction _ -> None

let as_function = function
  | VFunction (fn_ident, e) -> Some (fn_ident, e)
  | VBool _ | Varray _ -> None

let rec map' f = function
  | VBool b -> VBool (f b)
  | Varray a -> Varray (Array.map (map' f) a)
  | VFunction _ -> assert false

let get i = function
  | Varray array -> array.(i)
  | VBool _ as v -> if i = 0 then v else assert false
  | VFunction _ -> assert false

(*let rec pp format = function
  | VBool true -> Format.fprintf format "1"
  | VBool false -> Format.fprintf format "0"
  | Varray array ->
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
  | (VBool _ | VFunction _) as e -> Varray (Array.make 1 e)
  | Varray values as cir0 ->
      let cardinal = Array.length values in
      let circs =
        Array.init (cardinal - 1) @@ fun i ->
        let i = i + 1 in
        let value =
          Array.init cardinal (fun n ->
              let index = (n + i) mod cardinal in
              values.(index))
        in
        Varray value
      in
      Varray (Array.append [| cir0 |] circs)

let circ = function
  | (VBool _ | VFunction _) as e -> Varray (Array.make 1 e)
  | Varray values as cir0 ->
      let cardinal = Array.length values in
      let circs =
        Array.init (cardinal - 1) @@ fun i ->
        let i = i + 1 in
        let value =
          Array.init cardinal (fun n ->
              let index = (cardinal + (n - i)) mod cardinal in
              values.(index))
        in
        Varray value
      in
      Varray (Array.append [| cir0 |] circs)

let as_bool = function VBool s -> Some s | VFunction _ | Varray _ -> None

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
      Varray array

and mapn'' level i f values =
  let values = List.map (fun value -> get i value) values in
  mapn' (level - 1) f values

(*let rec make_pure_nested ty value =
  match ty with
  | TyNormal.TyTuple { size; ty } ->
      Varray (Array.init size (fun _ -> make_pure_nested ty value))
  | TyNormal.TyBool | TyNormal.TyFun _ | TyNormal.TyVar _ -> value

let make_pure ty value =
  match ty with
  | Ast.TyTuple { size; ty = _ } -> Varray (Array.init size (Fun.const value))
  | Ast.TyBool | TyFun _ -> value
  | Ast.TyApp _ | TyVarApp _ -> assert false*)

let tabulate size f =
  let array = Array.init size f in
  Varray array
