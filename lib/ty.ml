type 't t =
  | Bool  (** [bool] *)
  | Var of 'ty_var  (** ['a] *)
  | App of 't spine  (** [tname0 (tyname1 (... (tyname_n ty)))] *)
  | Fun of 't signature  (** [['a]^? (ty1, ty2, ...) -> ty] *)
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

and 't signature = {
  tyvars : 'ty_var option;
  ops : 't t list;
  parameters : 't t list;
  return_type : 't t;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

and 't spine = {
  names : 'ty_decl list;
  bty : 't t;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

type 't spines = {
  names : 'ty_decl list;
  btys : 't t list;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

let is_App = function App _ -> true | _ -> false

module S = struct
  let bool = Bool
  let v v = Var v

  let app name ty =
    match ty with
    | App { names; bty } ->
        assert (not (is_App bty));
        let names = name :: names in
        App { names; bty }
    | _ -> App { names = [ name ]; bty = ty }

  let ( @ ) n ty = app n ty

  let apps names' ty =
    match ty with
    | App { names; bty } ->
        assert (not (is_App bty));
        let names = List.append names' names in
        App { names; bty }
    | _ -> if List.is_empty names' then ty else App { names = names'; bty = ty }

  let fn ?tyvars ops parameters return_type =
    Fun { tyvars; ops; parameters; return_type }
end

let rec bmap_signature on_binder on_var on_decl env
    { tyvars; ops; parameters; return_type } =
  let env, tyvars =
    Option.fold ~none:(env, None)
      ~some:(fun v ->
        let e, v = on_binder env v in
        (e, Some v))
      tyvars
  in
  let ops = List.map (bmap on_binder on_var on_decl env) ops in
  let parameters = List.map (bmap on_binder on_var on_decl env) parameters in
  let return_type = bmap on_binder on_var on_decl env return_type in
  { tyvars; ops; parameters; return_type }

and bmap_spine on_binder on_var on_decl env { names; bty } =
  {
    names = List.map on_decl names;
    bty = bmap on_binder on_var on_decl env bty;
  }

and bmap on_binder on_var on_decl env = function
  | Bool -> Bool
  | Var v -> Var (on_var env v)
  | App sp -> App (bmap_spine on_binder on_var on_decl env sp)
  | Fun si -> Fun (bmap_signature on_binder on_var on_decl env si)

let map on_var on_decl t =
  bmap (fun e v -> (e, on_var v)) (fun () v -> on_var v) on_decl () t

let pp_ pp_var pp_decl =
  let pp_var_opt format = Format.pp_print_option pp_var format in
  let rec go format = function
    | Bool -> Format.fprintf format "bool"
    | App { names; bty } -> go_apps bty format names
    | Fun { tyvars; ops; parameters; return_type } ->
        Format.fprintf format "fn %a<%a>(%a) -> %a" pp_var_opt tyvars gos ops
          gos parameters go return_type
    | Var name -> Format.fprintf format "%a" pp_var name
  and go_apps ty format = function
    | [] -> go format ty
    | name :: names ->
        Format.fprintf format "%a (%a)" pp_decl name (go_apps ty) names
  and gos format =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
      go format
  in
  go

let to_spine ty = match ty with App s -> s | _ -> raise Not_found
let from_spine (s : 't spine) = S.apps s.names s.bty

(* Definitions over scoped terms: *)

let pp = pp_ Ident.TyIdent.pp Ident.TyDeclIdent.pp

let merge ss s =
  let rec go ss (s : Ident.scoped spine) =
    (* XXX: ugly `... @ [...]` *)
    match (ss.names, s.names) with
    | [], [] -> { names = []; btys = ss.btys @ [ s.bty ] }
    | name1 :: spine1, name2 :: spine2 when Ident.TyDeclIdent.equal name1 name2
      ->
        let ss = go { ss with names = spine1 } { s with names = spine2 } in
        { ss with names = name1 :: ss.names }
    | _, _ ->
        {
          names = [];
          btys =
            List.map (fun ty -> S.apps ss.names ty) ss.btys @ [ from_spine s ];
        }
  in
  go ss s

let merges (spine : Ident.scoped spine) spines =
  List.fold_left merge { names = spine.names; btys = [ spine.bty ] } spines

let take lhs ty =
  let rec take_prefix pre t =
    match (pre, t) with
    | [], t -> t
    | name1 :: pre, name2 :: t when Ident.TyDeclIdent.equal name1 name2 ->
        take_prefix pre t
    | _, _ -> raise Not_found
  in
  match ty with
  | App { names; bty } ->
      let names = take_prefix lhs names in
      S.apps names bty
  | _ -> raise Not_found

let rec equal_ m ty1 ty2 =
  match (ty1, ty2) with
  | Bool, Bool -> true
  | Var x, Var y -> (
      try Ident.TyIdent.equal (Ident.TyIdent.Map.find x m) y
      with Not_found ->
        (* XXX: assuming that `x` and `y` are free since they have not been matched along *)
        Ident.TyIdent.equal x y)
  | App sp1, App sp2 -> equal_spine m sp1 sp2
  | Fun si1, Fun si2 -> equal_signature m si1 si2
  | _, _ -> false

and equal_spine m sp1 sp2 =
  try
    List.for_all2 Ident.TyDeclIdent.equal sp1.names sp2.names
    && equal_ m sp1.bty sp2.bty
  with Invalid_argument _ -> false

and equal_signature m si1 si2 =
  try
    let m =
      match (si1.tyvars, si2.tyvars) with
      | None, None -> m
      | Some x, Some y -> Ident.TyIdent.Map.add x y m
      | _, _ -> raise Not_found
    in
    List.for_all2 (equal_ m) si1.parameters si2.parameters
    && equal_ m si1.return_type si2.return_type
  with Not_found | Invalid_argument _ -> false

let equal xs ys = equal_ Ident.TyIdent.Map.empty xs ys

let rec bind v ty = function
  | Var v' when Ident.TyIdent.equal v v' -> ty
  | Var v -> Var v
  | Bool -> Bool
  | App sp -> S.apps sp.names (bind v ty sp.bty)
  | Fun si -> Fun (bind_signature v ty si)

and bind_signature v ty si =
  assert (
    match si.tyvars with
    | None -> true
    | Some v' -> not (Ident.TyIdent.equal v v'));
  {
    si with
    parameters = List.map (bind v ty) si.parameters;
    return_type = bind v ty si.return_type;
  }

let free_vars ty =
  let module Vars = Set.Make (Ident.TyIdent) in
  let rec free_vars vars = function
    | Bool -> vars
    | Var s -> Vars.add s vars
    | App { bty; names = _ } -> free_vars vars bty
    | Fun { tyvars; ops; parameters; return_type } ->
        let vars = free_vars vars return_type in
        let vars = List.fold_left free_vars vars ops in
        let vars = List.fold_left free_vars vars parameters in
        Option.fold ~none:vars ~some:(Fun.flip Vars.remove vars) tyvars
  in
  let fv = free_vars Vars.empty ty in
  Vars.elements fv

let ty_vars = function
  | Bool | Var _ | App _ -> None
  | Fun { tyvars; _ } -> tyvars
