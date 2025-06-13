module Types = Map.Make (Ast.TyDeclIdent)
module Functions = Map.Make (Ast.FnIdent)

module Bitslice = struct
  module Env = struct
    type t = {
      src : Ast.TyDeclIdent.t list;
      dst : Ast.TyDeclIdent.t list;
      fns_remove : Ast.FnIdent.t list;
      fn_decls : Ast.kasumi_function_decl Functions.t;
      ty_decls : Ast.kasumi_type_decl Types.t;
    }

    let init src dst fns_remove =
      {
        src;
        dst;
        fns_remove;
        fn_decls = Functions.empty;
        ty_decls = Types.empty;
      }

    let add_fndecl env (fn_decl : Ast.kasumi_function_decl) =
      { env with fn_decls = Functions.add fn_decl.fn_name fn_decl env.fn_decls }

    let add_typedecl env (type_decl : Ast.kasumi_type_decl) =
      { env with ty_decls = Types.add type_decl.ty_name type_decl env.ty_decls }

    let mem_fn_removes fn env =
      List.exists (Ast.FnIdent.equal fn) env.fns_remove
  end

  let rec bitslice_expression env = function
    | Ast.EFunctionCall { fn_name; ty_args = _; args } as e -> (
        match (fn_name, args) with
        | Either.Left fn_name, e :: [] when Env.mem_fn_removes fn_name env ->
            bitslice_expression env e
        | _fn_name, _args -> (env, [], e))
    | (Ast.ETrue | EFalse | EVar _ | EFunVar _ | EBuiltinCall _) as e ->
        (env, [], e)
    | EOp op ->
        let env, statements, op = bitslice_op env op in
        (env, statements, EOp op)
    | SLetPLus { variable; ty_arg; ty_ret; expression; ands; body } ->
        let () = ignore (variable, ty_arg, ty_ret, expression, ands, body) in
        failwith ""
    | EIndexing { expression; indexing } ->
        let env, statements, expression = bitslice_expression env expression in
        (env, statements, EIndexing { expression; indexing })

  and bitslice_op env = function
    | Ast.Unot expression ->
        let env, statements, expression = bitslice_expression env expression in
        (env, statements, Ast.Unot expression)
    | BAnd (lhs, rhs) ->
        let env, lstatements, lexpression = bitslice_expression env lhs in
        let env, rstatements, rexpression = bitslice_expression env rhs in
        (env, lstatements @ rstatements, BAnd (lexpression, rexpression))
    | BOr (lhs, rhs) ->
        let env, lstatements, lexpression = bitslice_expression env lhs in
        let env, rstatements, rexpression = bitslice_expression env rhs in
        (env, lstatements @ rstatements, BOr (lexpression, rexpression))
    | BXor (lhs, rhs) ->
        let env, lstatements, lexpression = bitslice_expression env lhs in
        let env, rstatements, rexpression = bitslice_expression env rhs in
        (env, lstatements @ rstatements, BXor (lexpression, rexpression))

  let bitslice_statement env = function
    | Ast.StDeclaration { variable; expression } ->
        let env, statements, expression = bitslice_expression env expression in
        let () = ignore (variable, expression, env, statements, expression) in
        failwith ""
    | Ast.StLog _ as log -> (env, [ log ])
    | Ast.StConstructor _ as c -> (env, [ c ])

  let bitslice_body env body =
    let Ast.{ statements; expression } = body in
    let () = ignore (statements, expression, env) in
    failwith ""

  let bitslice_fn _env function_decl =
    let Ast.
          {
            fn_name = _;
            ty_vars = _;
            parameters = _;
            return_type = _;
            body = _;
          } =
      function_decl
    in

    failwith ""

  let bitslice_node fn env = function
    | Ast.KnFundecl function_decl as node -> (
        match Ast.FnIdent.equal fn function_decl.fn_name with
        | true ->
            let function_decl = bitslice_fn env function_decl in
            (env, Ast.KnFundecl function_decl)
        | false ->
            let env = Env.add_fndecl env function_decl in
            (env, node))
    | Ast.KnTypedecl ty_decl as node ->
        let env = Env.add_typedecl env ty_decl in
        (env, node)

  let bitslice fns_remove src dst fn ast =
    let env = Env.init src dst fns_remove in
    let _, nodes = List.fold_left_map (bitslice_node fn) env ast in
    nodes
end
