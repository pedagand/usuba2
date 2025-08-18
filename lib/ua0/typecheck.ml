[@@@warning "-27"]

let err fmt = Format.kasprintf failwith fmt

module Env = struct
  module Vars = Map.Make (Ast.TermIdent)
  module Fns = Map.Make (Ast.FnIdent)
  module Types = Map.Make (Ast.TyDeclIdent)

  type t = {
    variables : Ast.ty Vars.t;
    functions : Ast.fn_declaration Fns.t;
    types : Ast.ty_declaration Types.t;
  }

  let empty =
    { variables = Vars.empty; functions = Fns.empty; types = Types.empty }

  let add_function fn env =
    let functions = Fns.add fn.Ast.fn_name fn env.functions in
    { env with functions }

  let add_variable variable ty env =
    let variables = Vars.add variable ty env.variables in
    { env with variables }

  let add_type ty_decl env =
    let types = Types.add ty_decl.Ast.name ty_decl env.types in
    { env with types }

  let clear_variables env = { env with variables = Vars.empty }

  let ty_variable variable env =
    match Vars.find_opt variable env.variables with
    | None -> err "Unbound variable : %a" Ast.TermIdent.pp variable
    | Some ty -> ty

  let arity name env =
    let typedecl = Types.find name env.types in
    typedecl.size

  let rec range acc prefix ty env =
    match prefix with
    | [] -> Ast.Lty { t = List.rev acc; ty }
    | t :: q ->
        let name, size, ty =
          match ty with
          | Ast.TyApp { name; ty } ->
              let size = arity name env in
              (name, size, ty)
          | TyBool | TyFun _ | TyVar _ -> err "Not a named tuple."
        in
        let () =
          match Ast.TyDeclIdent.equal name t with
          | true -> ()
          | false ->
              err "range prefix = %a - ty = %a" Ast.TyDeclIdent.pp t
                Ast.TyDeclIdent.pp name
        in
        range ((name, size) :: acc) q ty env

  let range prefix = range [] prefix
end

let rec typecheck_term env = function
  | Ast.TFalse | TTrue -> Ast.TyBool
  | TVar variable -> Env.ty_variable variable env
  | TFn { fn_ident; tyresolve } -> failwith ""
  | TLet { variable; term; k } ->
      let ty = typecheck_term env term in
      let env = Env.add_variable variable ty env in
      typecheck_term env k
  | TLookup { lterm; index } -> failwith ""
  | TThunk { lterm } -> failwith ""
  | TLog { message = _; variables = _; k } -> typecheck_term env k
  | TOperator operator -> typecheck_operator env operator
  | TFnCall { fn_name; ty_resolve; args } -> failwith ""

and typecheck_operator env = function
  | Ast.ONot expr ->
      let ty = typecheck_term env expr in
      let () = if ty <> TyBool then err "expected Bool find : %a" Pp.pp_ty ty in
      ty
  | OXor (lhs, rhs) | OAnd (lhs, rhs) | OOr (lhs, rhs) ->
      let ly = typecheck_term env lhs in
      let () = if ly <> TyBool then err "expected Bool find : %a" Pp.pp_ty ly in
      let ry = typecheck_term env rhs in
      let () = if ry <> TyBool then err "expected Bool find : %a" Pp.pp_ty ry in
      TyBool

and typecheck_lterm env = function
  | Ast.LLetPlus { variable; lterm; ands; term } -> failwith ""
  | LConstructor { ty; terms } -> failwith ""
  | LRange { ty; term } ->
      let _lty = typecheck_term env term in
      failwith ""
  | LReindex { lhs; rhs; lterm } -> failwith ""
  | LCirc lterm -> failwith ""

let typecheck_function env fn =
  let Ast.{ fn_name; tyvars; parameters; return_type; body } = fn in
  let env = Env.clear_variables env in
  let env =
    List.fold_left
      (fun env (variable, ty) -> Env.add_variable variable ty env)
      env parameters
  in
  Env.add_function fn env
