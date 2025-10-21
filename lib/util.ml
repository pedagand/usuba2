module Cstrs = struct
  (* Should be here : More in list util equivalent. *)
  let rec remove_prefix f p list =
    match (p, list) with
    | [], list -> Some list
    | _ :: _, [] -> None
    | p :: ps, x :: xs -> if f p x then remove_prefix f ps xs else None

  let rec replace ~by f cstrs = function
    | [] -> ([], [])
    | x :: xs as list -> (
        match remove_prefix f cstrs list with
        | Some remains -> (by, remains)
        | None ->
            let by, remains = replace ~by f cstrs xs in
            (x :: by, remains))

  let reorder lhs rhs types =
    let eq = Ast.TyDeclIdent.equal in
    let head, remains = replace ~by:rhs eq lhs types in
    let queue, remains = replace ~by:lhs eq rhs remains in
    head @ queue @ remains
end

module Ty = struct
  open Ty

  let to_spine ty =
    let rec go acc ty =
      match ty with
      | App { name; ty } -> go (name :: acc) ty
      | bty -> (List.rev acc, bty)
    in
    go [] ty

  let rec from_spine (spine, ty) =
    match spine with
    | [] -> ty
    | name :: spine ->
        let ty = from_spine (spine, ty) in
        App { name; ty }

  let rec merge (spine1, tys) (spine2, ty2) =
    (* XXX: ugly `... @ [...]` *)
    match (spine1, spine2) with
    | [], [] -> ([], tys @ [ ty2 ])
    | name1 :: spine1, name2 :: spine2 when Ast.TyDeclIdent.equal name1 name2 ->
        let spine, tys = merge (spine1, tys) (spine2, ty2) in
        (name1 :: spine, tys)
    | _, _ ->
        ( [],
          List.map (fun ty -> from_spine (spine1, ty)) tys
          @ [ from_spine (spine2, ty2) ] )

  let rec prefix lhs ty =
    match (lhs, ty) with
    | [], ty -> Some ty
    | decl :: lhs, App { name; ty } when Ast.TyDeclIdent.equal decl name ->
        prefix lhs ty
    | _, _ -> None

  let rec instanciate types = function
    | Bool -> Bool
    | Fun signature ->
        let signature = instanciate_signature types signature in
        Fun signature
    | App { name; ty } ->
        let ty = instanciate types ty in
        App { name; ty }
    | Var v as t -> (
        match List.assoc_opt v types with None -> t | Some t -> t)

  and instanciate_signature types =
   fun { tyvars; parameters; return_type } ->
    let types =
      match tyvars with None -> types | Some ty -> List.remove_assoc ty types
    in
    let parameters = List.map (instanciate types) parameters in
    let return_type = instanciate types return_type in
    { tyvars; parameters; return_type }

  (*  let rec prefix = function
    | Ast.TyApp { name; ty } ->
        let names, elt = prefix ty in
        (name :: names, elt)
    | (TyBool | TyVar _ | TyFun _) as t -> ([], t)*)

  let rec equal assocs lhs rhs =
    match (lhs, rhs) with
    | Bool, Bool -> true
    | Var lhs, Var rhs ->
        Ast.TyIdent.equal lhs rhs
        || assocs
           |> List.find_map (fun (l, r) ->
                  if Ast.TyIdent.equal l lhs then Some r else None)
           |> Option.map (Ast.TyIdent.equal rhs)
           |> Option.value ~default:false
    | App { ty = lty; name = lname }, App { ty = rty; name = rname } ->
        Ast.TyDeclIdent.equal lname rname && equal assocs lty rty
    | Fun lsignature, Fun rsignature ->
        equal_signature assocs lsignature rsignature
    | _, _ -> false

  and equal_signature assocs lsignature rsignature =
    (* Big hack: instance with bool before checking*)
    let ( let* ) b f = match b with false -> false | true -> f () in
    let* () =
      List.compare_lengths lsignature.parameters rsignature.parameters = 0
    in
    let* () =
      Option.equal (fun _ _ -> true) lsignature.tyvars rsignature.tyvars
    in
    let assocs =
      List.combine
        (Option.to_list lsignature.tyvars)
        (Option.to_list rsignature.tyvars)
      @ assocs
    in
    let* () =
      List.for_all2 (equal assocs) lsignature.parameters rsignature.parameters
    in
    equal assocs lsignature.return_type rsignature.return_type

  let equal xs ys = equal [] xs ys
  let lift cstrs ty = List.fold_right (fun name ty -> App { name; ty }) cstrs ty

  let rec contains_boolean = function
    | Bool -> true
    | Var _ -> false
    | App { ty; name = _ } -> contains_boolean ty
    | Fun { parameters; return_type; tyvars = _ } ->
        contains_boolean return_type || List.exists contains_boolean parameters

  let rec lift_boolean cstrs = function
    | Bool as ty -> lift cstrs ty
    | Var _ as ty -> ty
    | App { ty; name } -> App { name; ty = lift_boolean cstrs ty }
    | Fun { parameters; return_type; tyvars } ->
        let return_type = lift_boolean cstrs return_type in
        let parameters = List.map (lift_boolean cstrs) parameters in
        Fun { tyvars; parameters; return_type }

  (*
  let lty t ty = { Ast.t; ty }
*)

  let rec ty_cstrs = function
    | (Bool | Var _ | Fun _) as e -> ([], e)
    | App { name; ty } ->
        let r, ty = ty_cstrs ty in
        (name :: r, ty)

  (*
  let to_ty { Ast.t; ty } =
    List.fold_right (fun (name, _) ty -> Ast.TyApp { name; ty }) t ty
*)
  let rec remove_prefix ctsrs ty =
    match ctsrs with
    | [] -> Some ty
    | t :: q -> (
        match ty with
        | Bool | Fun _ | Var _ -> None
        | App { name; ty; _ } ->
            if Ast.TyDeclIdent.equal t name then remove_prefix q ty else None)

  (*
  let prefix lty = lty.Ast.t
  let nest lty = List.length lty.Ast.t

  let hd = function
    | { Ast.t = (ty, _) :: _; ty = _ } | { t = []; ty = TyApp { name = ty; _ } }
      ->
        Some ty
    | _ -> None
*)

  let elt = function App { ty; _ } -> Some ty | Bool | Fun _ | Var _ -> None

  let cstrql lhs rhs =
    match (lhs, rhs) with
    | Bool, Bool -> true
    | App { name = lname; _ }, App { name = rname; _ } ->
        Ast.TyDeclIdent.equal lname rname
    | _, _ -> false

  (*
  let lcstreq lhs rhs =
    match (lhs, rhs) with
    | { Ast.t = lt; ty = lty }, { Ast.t = rt; ty = rty } -> (
        match (lt, rt) with
        | [], [] -> cstrql lty rty
        | (l, _) :: _, (r, _) :: _ -> Ast.TyDeclIdent.equal l r
        | _, _ -> false)
*)
end

module FunctionDecl = struct
  let signature fn_decl = fn_decl.Ast.signature
end
