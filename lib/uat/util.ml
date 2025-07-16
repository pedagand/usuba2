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

  let to_ty = function
    | Ua0.Ast.Lty { t; ty } ->
        List.fold_right (fun (name, _) ty -> Ua0.Ast.TyApp { name; ty }) t ty

  let lty t ty = Ua0.Ast.Lty { t; ty }
end
