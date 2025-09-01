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
      match tyvars with None -> types | Some ty -> List.remove_assoc ty types
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

module FunctionDecl = struct
  let signature fn_decl =
    let Ua0.Ast.{ fn_name = _; tyvars; parameters; return_type; body = _ } =
      fn_decl
    in
    let parameters = List.map snd parameters in
    Ua0.Ast.{ tyvars; parameters; return_type }
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
  let v ty term = (Ast.TVar term, ty)

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

  let rec as_variable = function
    | Ast.TVar v -> Some v
    | TLog { k = k, _; _ } -> as_variable k
    | TFalse | TTrue | TFn _ | TLet _ | TLookup _ | TOperator _ | TFnCall _
    | TThunk _ ->
        None

  let funk lterm =
    let _, lty = lterm in
    let ty = Ty.to_ty lty in
    let term = Ast.TThunk { lterm } in
    (term, ty)

  let cstr ctr expr =
    let ctr, arity = ctr in
    let terms = List.init arity (Fun.const expr) in
    Ast.LConstructor { ty = ctr; terms }

  let cstr' ctr expr =
    let _, ty = expr in
    let cstr = cstr ctr expr in
    let ctr, _ = ctr in
    let lty = Ty.lty [] (Ua0.Scstr.Ty.app ctr ty) in
    (cstr, lty)
end

module Lterm = struct
  let as_reindex = function
    | Ast.LReindex { lhs; rhs; lterm } -> Some (lhs, rhs, lterm)
    | LLetPlus _ | LConstructor _ | LRange _ | LCirc _ -> None

  let as_mapn = function
    | Ast.LLetPlus { variable; lterm; ands; term } ->
        Some (variable, lterm, ands, term)
    | LConstructor _ | LRange _ | LReindex _ | LCirc _ -> None

  let as_range = function
    | Ast.LRange { ty; term } -> Some (ty, term)
    | LLetPlus _ | LConstructor _ | LReindex _ | LCirc _ -> None

  let range f tys tterm =
    let _term, ty = tterm in
    let lty = Lty.range f tys ty in
    let range = Ast.LRange { ty = tys; term = tterm } in
    (range, lty)

  let let_plus' variable lterm ands term =
    let lterm = Ast.LLetPlus { variable; lterm; ands; term } in
    let ty = Ty.lty [] (snd term) in
    (lterm, ty)
end
