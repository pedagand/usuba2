let rec find_fold_map f acc = function
  | [] -> Either.left acc
  | t :: q -> (
      let res = f acc t in
      match res with
      | Either.Left acc -> find_fold_map f acc q
      | Right _ as r -> r)

module Value = struct
  type t = VBool of bool | Varray of t Array.t | VFunction of Ast.FnIdent.t

  let true' = VBool true
  let false' = VBool false

  let rec map2 f lhs rhs =
    match (lhs, rhs) with
    | VBool lhs, VBool rhs -> VBool (f lhs rhs)
    | Varray lhs, Varray rhs -> Varray (Array.map2 (map2 f) lhs rhs)
    | VBool _, Varray _ | Varray _, VBool _ | VFunction _, _ | _, VFunction _ ->
        assert false

  let rec map f = function
    | VBool b -> VBool (f b)
    | Varray a -> Varray (Array.map (map f) a)
    | VFunction _ -> assert false

  let as_function = function
    | VFunction fn_ident -> Some fn_ident
    | VBool _ | Varray _ -> None
end

module Types = Map.Make (Ast.TyDeclIdent)
module Functions = Map.Make (Ast.FnIdent)
module Variables = Map.Make (Ast.TermIdent)

module Env = struct
  type t = {
    type_decls : Ast.ty Types.t;
    fn_decls : Ast.kasumi_function_decl Functions.t;
    variables : (Value.t * Ast.ty) Variables.t;
  }

  let empty =
    {
      type_decls = Types.empty;
      fn_decls = Functions.empty;
      variables = Variables.empty;
    }

  let add_binding term variable env =
    let variables = Variables.add term variable env.variables in
    { env with variables }

  let signature_of_function_decl (function_decl : Ast.kasumi_function_decl) =
    Ast.
      {
        ty_vars = List.map fst function_decl.ty_vars;
        return_type = function_decl.return_type;
        parameters = List.map snd function_decl.parameters;
      }

  let function_decl fnident env = Functions.find fnident env.fn_decls

  let function' fnident env =
    let function_decl = Functions.find fnident env.fn_decls in
    let signature = signature_of_function_decl function_decl in
    let ty = Ast.TyFun signature in
    let value = Value.VFunction fnident in
    (value, ty)

  let value termid env = Variables.find termid env.variables
end

let rec eval_expression env =
  let ( $ ) g f x = g (f x) in
  function
  | Ast.ETrue -> (Value.true', Ast.TyBool)
  | EFalse -> (Value.false', Ast.TyBool)
  | EVar term -> Env.value term env
  | EFunVar fn -> Env.function' fn env
  | EFunctionCall { fn_name; ty_args = _; args } ->
      let fn_ident =
        match fn_name with
        | Either.Left fn -> fn
        | Either.Right termid ->
            let value, _ = Env.value termid env in
            Option.get @@ Value.as_function value
      in
      let fn_decl = Env.function_decl fn_ident env in
      let args = List.map (fst $ eval_expression env) args in
      eval env fn_decl args
  | EIndexing _ -> failwith ""
  | EOp _ -> failwith ""

and eval_statement env = function
  | Ast.StDeclaration { variable; expression } ->
      let value_ty = eval_expression env expression in
      Env.add_binding variable value_ty env
  | StConstructor { variable = _; ty = _; expressions = _ } -> failwith ""
  | SLetPLus { variable = _; expression = _; ands = _ } -> failwith ""

and eval env (fn_decl : Ast.kasumi_function_decl) args =
  let Ast.
        {
          fn_name = _;
          ty_vars = _;
          parameters;
          return_type = _;
          body = { statements; expression };
        } =
    fn_decl
  in
  let variables =
    List.fold_left2
      (fun variables (term, ty) value ->
        Variables.add term (value, ty) variables)
      Variables.empty parameters args
  in
  let env = Env.{ env with variables } in
  let env = List.fold_left eval_statement env statements in
  eval_expression env expression

let add_fndecl env (fn_decl : Ast.kasumi_function_decl) =
  Env.
    {
      env with
      fn_decls = Functions.add fn_decl.fn_name fn_decl env.Env.fn_decls;
    }

let add_typedecl env (type_decl : Ast.kasumi_type_decl) =
  let ty =
    match type_decl.definition with
    | TyApp { name; ty_args = _ } -> Types.find name env.Env.type_decls
    | (TyTuple _ | TyFun _ | TyBool) as ty -> ty
    | TyVarApp _ -> assert false
  in
  { env with type_decls = Types.add type_decl.ty_name ty env.type_decls }

let eval_node fn_name args env = function
  | Ast.KnFundecl function_decl -> (
      match Ast.FnIdent.equal fn_name function_decl.fn_name with
      | true ->
          let value = eval env function_decl args in
          Either.right value
      | false ->
          let env = add_fndecl env function_decl in
          Either.left env)
  | Ast.KnTypedecl type_decl ->
      let env = add_typedecl env type_decl in
      Either.left env

let eval ast fn_name args =
  ast |> find_fold_map (eval_node fn_name args) Env.empty |> Either.find_right
