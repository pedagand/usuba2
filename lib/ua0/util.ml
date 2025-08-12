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

  let rec prefix = function
    | Ast.TyApp { name; ty } ->
        let names, elt = prefix ty in
        (name :: names, elt)
    | (TyBool | TyVar _ | TyFun _) as t -> ([], t)

  let rec contains_boolean = function
    | Ast.TyBool -> true
    | Ast.TyVar _ -> false
    | TyApp { ty; name = _ } -> contains_boolean ty
    | TyFun { parameters; return_type; tyvars = _ } ->
        contains_boolean return_type || List.exists contains_boolean parameters
end
