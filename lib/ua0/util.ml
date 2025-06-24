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
      List.fold_left (fun tyvars ty -> List.remove_assoc ty tyvars) types tyvars
    in
    let parameters = List.map (instanciate types) parameters in
    let return_type = instanciate types return_type in
    { tyvars; parameters; return_type }
end
