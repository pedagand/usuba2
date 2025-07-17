let err fmt = Format.kasprintf failwith fmt
let log fmt = Format.eprintf fmt

module TermIdent = struct
  let prepend prefix base =
    Ast.TermIdent.(fresh @@ Format.asprintf "%s%a" prefix pp base)
end

module FnIdent = struct
  let prepend prefix base =
    Ast.FnIdent.(fresh @@ Format.asprintf "%s%a" prefix pp base)
end

module Ty = struct
  let rec instanciate types = function
    | Ua0.Ast.TyBool -> Ua0.Ast.TyBool
    | TyFun signature ->
        let signature = instanciate_signature types signature in
        Ua0.Ast.TyFun signature
    | TyApp { name; ty } ->
        let ty = instanciate types ty in
        TyApp { name; ty }
    | TyVar v as t -> (
        match List.assoc_opt v types with None -> t | Some t -> t)

  and instanciate_signature types =
   fun { tyvars; parameters; return_type } ->
    let types =
      List.fold_left (fun tyvars ty -> List.remove_assoc ty tyvars) types tyvars
    in
    let parameters = List.map (instanciate types) parameters in
    let return_type = instanciate types return_type in
    { tyvars; parameters; return_type }

  let rec prefix = function
    | Ua0.Ast.TyApp { name; ty } ->
        let names, elt = prefix ty in
        (name :: names, elt)
    | (TyBool | TyVar _ | TyFun _) as t -> ([], t)

  let lprefix = function Ua0.Ast.Lty { t; ty = _ } -> t

  let to_ty = function
    | Ua0.Ast.Lty { t; ty } ->
        List.fold_right (fun (name, _) ty -> Ua0.Ast.TyApp { name; ty }) t ty

  let lty t ty = Ua0.Ast.Lty { t; ty }

  let lift' cstrs =
    List.fold_right (fun (name, _) ty -> Ua0.Ast.TyApp { name; ty }) cstrs

  let lift cstrs =
    List.fold_right (fun name ty -> Ua0.Ast.TyApp { name; ty }) cstrs
end

module Lty = struct
  let rec range acc f prefix ty =
    match prefix with
    | [] -> Ty.lty (List.rev acc) ty
    | t :: q ->
        let name, ty =
          match ty with
          | Ua0.Ast.TyApp { name; ty } -> (name, ty)
          | TyBool | TyFun _ | TyVar _ -> err "Not a named tuple."
        in
        let () =
          match Ast.TyDeclIdent.equal name t with
          | true -> ()
          | false ->
              err "range prefix = %a - ty = %a" Ast.TyDeclIdent.pp t
                Ast.TyDeclIdent.pp name
        in
        let size = f name in
        range ((name, size) :: acc) f q ty

  let range prefix = range [] prefix
end

module Term = struct
  let rec as_function_call = function
    | Ast.TFnCall { fn_name; ty_resolve; args } ->
        Some (fn_name, ty_resolve, args)
    | TLog { k = k, _; _ } -> as_function_call k
    | TFalse | TTrue | TVar _ | TFn _ | TLet _ | TLookup _ | TThunk _
    | TOperator _ ->
        None

  let rec as_funk = function
    | Ast.TThunk { lterm } -> Some lterm
    | TLog { k = k, _; _ } -> as_funk k
    | TFalse | TTrue | TVar _ | TFn _ | TLet _ | TLookup _ | TOperator _
    | TFnCall _ ->
        None

  let funk lterm =
    let _, lty = lterm in
    let ty = Ty.to_ty lty in
    let term = Ast.TThunk { lterm } in
    (term, ty)
end

module Lterm = struct
  let range f tys tterm =
    let _term, ty = tterm in
    let lty = Lty.range f tys ty in
    let range = Ast.LRange { ty = tys; term = tterm } in
    (range, lty)
end
