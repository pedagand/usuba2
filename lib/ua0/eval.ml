let rec find_fold_map f acc = function
  | [] -> Either.left acc
  | t :: q -> (
      let res = f acc t in
      match res with
      | Either.Left acc -> find_fold_map f acc q
      | Right _ as r -> r)

module Env = struct
  module Functions = Map.Make (Ast.FnIdent)
  module Types = Map.Make (Ast.TyDeclIdent)
  module Variables = Map.Make (Ast.TermIdent)
  module TyVariables = Map.Make (Ast.TyIdent)

  type t = {
    types : Ast.ty_declaration Types.t;
    functions : Ast.fn_declaration Functions.t;
    variables : (Value.t * Value.Ty.ty) Variables.t;
    type_variables : Value.Ty.ty TyVariables.t;
  }

  let init =
    {
      functions = Functions.empty;
      types = Types.empty;
      variables = Variables.empty;
      type_variables = TyVariables.empty;
    }

  let add_function (fn : Ast.fn_declaration) env =
    { env with functions = Functions.add fn.fn_name fn env.functions }

  let add_types (ty : Ast.ty_declaration) env =
    { env with types = Types.add ty.name ty env.types }

  let bind_variable variable value ty env =
    { env with variables = Variables.add variable (value, ty) env.variables }

  let err fmt = Format.kasprintf failwith fmt

  let type_declaration name env =
    match Types.find_opt name env.types with
    | None -> err "type %a not in env" Ast.TyDeclIdent.pp name
    | Some e -> e

  let rec of_ty env ty =
    match ty with
    | Ast.TyBool -> Value.Ty.TBool
    | TyApp { name; ty } ->
        let Ast.{ size; _ } = type_declaration name env in
        let ty = of_ty env ty in
        Value.Ty.TNamedTuple { name; size; ty }
    | TyFun signature ->
        let signature = of_signature signature env in
        Value.Ty.TFun signature
    | TyVar variable -> (
        match TyVariables.find_opt variable env.type_variables with
        | None -> err "Undefinied ty_variable : %a" Ast.TyIdent.pp variable
        | Some ty -> ty)

  and of_signature signature env =
    let Ast.{ tyvars; parameters; return_type } : Ast.signature = signature in

    Value.Ty.
      {
        tyvars;
        parameters = List.map (of_ty env) parameters;
        return_type = of_ty env return_type;
      }

  let lookup variable env =
    match Variables.find_opt variable env.variables with
    | Some e -> e
    | None -> err "variable %a not in env" Ast.TermIdent.pp variable

  let signature fn_name env =
    match Functions.find_opt fn_name env.functions with
    | Some fn_decl ->
        Value.Ty.
          {
            tyvars = fn_decl.tyvars;
            parameters =
              List.map (fun (_, ty) -> of_ty env ty) fn_decl.parameters;
            return_type = of_ty env fn_decl.return_type;
          }
    | None -> err "function %a not in env" Ast.FnIdent.pp fn_name
end

let rec eval_op env = function
  | Ast.ONot term ->
      let value, ty = eval_term env term in
      let () = assert (Value.Ty.is_bool ty) in
      let value = Value.not value in
      (value, ty)
  | OXor (lhs, rhs) ->
      let lvalue, lty = eval_term env lhs in
      let rvalue, rty = eval_term env rhs in
      let () = assert (Value.Ty.(is_bool lty && is_bool rty)) in
      let value = Value.( lxor ) lvalue rvalue in
      (value, lty)
  | OAnd (lhs, rhs) ->
      let lvalue, lty = eval_term env lhs in
      let rvalue, rty = eval_term env rhs in
      let () = assert (Value.Ty.(is_bool lty && is_bool rty)) in
      let value = Value.( land ) lvalue rvalue in
      (value, lty)
  | OOr (lhs, rhs) ->
      let lvalue, lty = eval_term env lhs in
      let rvalue, rty = eval_term env rhs in
      let () = assert (Value.Ty.(is_bool lty && is_bool rty)) in
      let value = Value.( lor ) lvalue rvalue in
      (value, lty)

and eval_term env = function
  | Ast.TFalse -> (Value.VBool false, Value.Ty.TBool)
  | TTrue -> (Value.VBool true, Value.Ty.TBool)
  | TVar variable -> Env.lookup variable env
  | TFn fn ->
      let signature = Env.signature fn env in
      (Value.VFunction (fn, None), Value.Ty.TFun signature)
  | TLet { variable; term; k } ->
      let value, ty = eval_term env term in
      let env = Env.bind_variable variable value ty env in
      eval_term env k
  | TLookup _ -> failwith ""
  | TThunk _ -> failwith ""
  | TOperator op -> eval_op env op
  | TFnCall _ -> failwith ""

let _eval _env (fn : Ast.fn_declaration) _ty_args _args =
  let Ast.{ fn_name = _; tyvars = _; parameters = _; return_type = _; body = _ }
      =
    fn
  in
  failwith ""

let eval_node fn_name _ty_args _args env = function
  | Ast.NTy tydel ->
      let env = Env.add_types tydel env in
      Either.right env
  | Ast.NFun fn_decl -> (
      match Ast.FnIdent.equal fn_name fn_decl.fn_name with
      | false ->
          let env = Env.add_function fn_decl env in
          Either.left env
      | true -> failwith "")

let eval ast fn_name ty_args args =
  ast
  |> find_fold_map (eval_node fn_name ty_args args) Env.init
  |> Either.find_right
