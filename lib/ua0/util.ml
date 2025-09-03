module TermIdent = struct
  let prepend prefix base =
    Ast.TermIdent.(fresh @@ Format.asprintf "%s%a" prefix pp base)
end

module FnIdent = struct
  let prepend prefix base =
    Ast.FnIdent.(fresh @@ Format.asprintf "%s%a" prefix pp base)
end

module Cstrs = struct
  (* Should be here : More in list util equivalent. *)
  let rec remove_prefix f p list =
    match (p, list) with
    | [], list -> Some list
    | _ :: _, [] -> None
    | p :: ps, x :: xs -> if f p x then remove_prefix f ps xs else None

  let rec replace ~by f cstrs = function
    | [] -> []
    | x :: xs as list -> (
        match remove_prefix f cstrs list with
        | Some remains -> by @ remains
        | None -> x :: replace ~by f cstrs xs)

  let reorder lhs rhs types =
    let eq = Ast.TyDeclIdent.equal in
    types |> replace ~by:rhs eq lhs |> replace ~by:lhs eq rhs
end

module Ty = struct
  let rec instanciate types = function
    | Ast.TyBool -> Ast.TyBool
    | TyFun signature ->
        let signature = instanciate_signature types signature in
        Ast.TyFun signature
    | TyApp { name; ty } ->
        let ty = instanciate types ty in
        TyApp { name; ty }
    | TyVar v as t -> (
        match List.assoc_opt v types with None -> t | Some t -> t)

  and instanciate_signature types =
   fun Ast.{ tyvars; parameters; return_type } ->
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
    | Ast.TyBool, Ast.TyBool -> true
    | Ast.TyVar lhs, Ast.TyVar rhs ->
        Ast.TyIdent.equal lhs rhs
        || assocs
           |> List.find_map (fun (l, r) ->
                  if Ast.TyIdent.equal l lhs then Some r else None)
           |> Option.map (Ast.TyIdent.equal rhs)
           |> Option.value ~default:false
    | Ast.TyApp { ty = lty; name = lname }, Ast.TyApp { ty = rty; name = rname }
      ->
        Ast.TyDeclIdent.equal lname rname && equal assocs lty rty
    | Ast.TyFun lsignature, Ast.TyFun rsignature ->
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

  let equal = equal []

  let lift cstrs ty =
    List.fold_right (fun name ty -> Ast.TyApp { name; ty }) cstrs ty

  let rec contains_boolean = function
    | Ast.TyBool -> true
    | Ast.TyVar _ -> false
    | TyApp { ty; name = _ } -> contains_boolean ty
    | TyFun { parameters; return_type; tyvars = _ } ->
        contains_boolean return_type || List.exists contains_boolean parameters

  let rec lift_boolean cstrs = function
    | Ast.TyBool as ty -> lift cstrs ty
    | Ast.TyVar _ as ty -> ty
    | TyApp { ty; name } -> TyApp { name; ty = lift_boolean cstrs ty }
    | TyFun { parameters; return_type; tyvars } ->
        let return_type = lift_boolean cstrs return_type in
        let parameters = List.map (lift_boolean cstrs) parameters in
        TyFun { tyvars; parameters; return_type }

  let lty t ty = Ast.Lty { t; ty }

  let rec ty_cstrs = function
    | (Ast.TyBool | TyVar _ | TyFun _) as e -> ([], e)
    | TyApp { name; ty } ->
        let r, ty = ty_cstrs ty in
        (name :: r, ty)

  let to_ty = function
    | Ast.Lty { t; ty } ->
        List.fold_right (fun (name, _) ty -> Ast.TyApp { name; ty }) t ty

  let rec remove_prefix ctsrs ty =
    match ctsrs with
    | [] -> Some ty
    | t :: q -> (
        match ty with
        | Ast.TyBool | Ast.TyFun _ | Ast.TyVar _ -> None
        | TyApp { name; ty; _ } ->
            if Ast.TyDeclIdent.equal t name then remove_prefix q ty else None)

  let prefix = function Ast.Lty { t; _ } -> t
  let nest = function Ast.Lty { t; _ } -> List.length t

  let hd = function
    | Ast.Lty { t = (ty, _) :: _; ty = _ }
    | Lty { t = []; ty = TyApp { name = ty; _ } } ->
        Some ty
    | _ -> None

  let elt = function
    | Ast.TyApp { ty; _ } -> Some ty
    | TyBool | TyFun _ | TyVar _ -> None

  let cstrql lhs rhs =
    match (lhs, rhs) with
    | Ast.TyBool, Ast.TyBool -> true
    | TyApp { name = lname; _ }, TyApp { name = rname; _ } ->
        Ast.TyDeclIdent.equal lname rname
    | _, _ -> false

  let lcstreq lhs rhs =
    match (lhs, rhs) with
    | Ast.Lty { t = lt; ty = lty }, Ast.Lty { t = rt; ty = rty } -> (
        match (lt, rt) with
        | [], [] -> cstrql lty rty
        | (l, _) :: _, (r, _) :: _ -> Ast.TyDeclIdent.equal l r
        | _, _ -> false)
end

module FunctionDecl = struct
  let signature fn_decl =
    let Ast.{ fn_name = _; tyvars; parameters; return_type; body = _ } =
      fn_decl
    in
    let parameters = List.map snd parameters in
    Ast.{ tyvars; parameters; return_type }
end
