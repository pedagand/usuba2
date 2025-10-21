let rec find_fold_map f acc = function
  | [] -> Either.left acc
  | t :: q -> (
      let res = f acc t in
      match res with
      | Either.Left acc -> find_fold_map f acc q
      | Right _ as r -> r)

let err fmt = Format.kasprintf failwith fmt
let log fmt = Format.eprintf fmt
let uncons l = match l with [] -> None | x :: xs -> Some (x, xs)

module Env = struct
  module Functions = Map.Make (Ast.FnIdent)
  module Types = Map.Make (Ast.TyDeclIdent)
  module Variables = Map.Make (Ast.TermIdent)
  module TyVariables = Map.Make (Ast.TyIdent)

  type t = {
    current_function : Ast.FnIdent.t option;
    types : Ast.ty_declaration Types.t;
    functions : Ast.fn_declaration Functions.t;
    variables : (Value.t * Value.Ty.ty) Variables.t;
    type_variables : Value.Ty.ty TyVariables.t;
  }

  let init =
    {
      current_function = None;
      functions = Functions.empty;
      types = Types.empty;
      variables = Variables.empty;
      type_variables = TyVariables.empty;
    }

  let pp format env =
    let () =
      Variables.iter
        (fun variable _ ->
          Format.fprintf format "%a - " Ast.TermIdent.pp variable)
        env.variables
    in
    ()

  let add_function (fn : Ast.fn_declaration) env =
    { env with functions = Functions.add fn.fn_name fn env.functions }

  let add_types (ty : Ast.ty_declaration) env =
    { env with types = Types.add ty.name ty env.types }

  let bind_variable variable value ty env =
    { env with variables = Variables.add variable (value, ty) env.variables }

  let type_declaration name env =
    match Types.find_opt name env.types with
    | None -> err "type %a not in env" Ast.TyDeclIdent.pp name
    | Some e -> e

  let fn_declaration name env =
    match Functions.find_opt name env.functions with
    | None -> err "function %a not in env" Ast.FnIdent.pp name
    | Some e -> e

  let rec range acc prefix ty env =
    match prefix with
    | [] -> Value.Ty.lty (List.rev acc) ty
    | t :: q ->
        let name, size, ty =
          match ty with
          | Value.Ty.TNamedTuple { name; size; ty } -> (name, size, ty)
          | TBool | TFun _ | TVar _ -> err "Not a named tuple."
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

  let cstr_log name env =
    let decl = type_declaration name env in
    decl.size

  let naperian cstr env = Value.naperian (cstr_log cstr env)

  let naperian_compose lhs rhs env =
    Value.naperian_compose (naperian lhs env) (naperian rhs env)

  let naperians cstrs env =
    let cstr, cstrs = Option.get @@ uncons cstrs in
    let n0 = naperian cstr env in
    List.fold_left
      (fun nap cstr -> Value.naperian_compose nap (naperian cstr env))
      n0 cstrs

  let clear_variables env = { env with variables = Variables.empty }
  let clear_tyvariables env = { env with type_variables = TyVariables.empty }

  let rec to_ty env = function
    | Value.Ty.TBool -> Ast.Ty.Bool
    | TNamedTuple { name; ty; size = _ } ->
        let ty = to_ty env ty in
        App { name; ty }
    | TVar v -> Var v
    | TFun signature ->
        let signature = to_signature env signature in
        Fun signature

  and to_signature env = function
    | { tyvars; parameters; return_type } ->
        let parameters = List.map (to_ty env) parameters in
        let return_type = to_ty env return_type in
        { tyvars; parameters; return_type }

  let rec of_ty env ty =
    match ty with
    | Ast.Ty.Bool -> Value.Ty.TBool
    | App { name; ty } ->
        let Ast.{ size; _ } = type_declaration name env in
        let ty = of_ty env ty in
        Value.Ty.TNamedTuple { name; size; ty }
    | Fun signature ->
        let signature = of_signature signature env in
        Value.Ty.TFun signature
    | Var variable -> (
        match TyVariables.find_opt variable env.type_variables with
        | None -> Value.Ty.TVar variable
        | Some ty -> ty)

  and of_signature signature env =
    let { tyvars; parameters; return_type } : _ Ast.Ty.signature = signature in

    Value.Ty.
      {
        tyvars;
        parameters = List.map (of_ty env) parameters;
        return_type = of_ty env return_type;
      }

  let init_tyvariables types env =
    let type_variables =
      List.fold_left
        (fun tyvars (tyvar, ty) ->
          let ty = of_ty env ty in
          TyVariables.add tyvar ty tyvars)
        TyVariables.empty types
    in
    { env with type_variables }

  let init_variables parameters values env =
    let env = clear_variables env in
    List.fold_left2
      (fun env (term, ty) value ->
        let ty = of_ty env ty in
        bind_variable term value ty env)
      env parameters values

  let lookup variable env =
    match Variables.find_opt variable env.variables with
    | Some e -> e
    | None ->
        err "variable %a not in env\nenv = %a\n" Ast.TermIdent.pp variable pp
          env

  let signature ~instance fn_name tyresolve env =
    match Functions.find_opt fn_name env.functions with
    | Some fn_decl ->
        (*        let () = log "lookup sig : %a\n" Ast.FnIdent.pp fn_name in*)
        let signature =
          Value.Ty.
            {
              tyvars = fn_decl.signature.tyvars;
              parameters = List.map (of_ty env) fn_decl.signature.parameters;
              return_type = of_ty env fn_decl.signature.return_type;
            }
        in
        let signature =
          match instance with
          | false -> signature
          | true ->
              let env =
                match (fn_decl.signature.tyvars, tyresolve) with
                | Some tyvar, Some ty ->
                    let ty = of_ty env ty in
                    {
                      env with
                      type_variables =
                        TyVariables.add tyvar ty env.type_variables;
                    }
                | None, None -> env
                | Some lhs, None ->
                    err "sig %a : expect type instance for : %a\n"
                      Ast.FnIdent.pp fn_name Ast.TyIdent.pp lhs
                | None, Some rhs ->
                    err "sig %a : no type instance expected but found : %a\n"
                      Ast.FnIdent.pp fn_name Pp.pp_ty rhs
              in
              Value.Ty.
                {
                  tyvars = None;
                  parameters = List.map (of_ty env) fn_decl.signature.parameters;
                  return_type = of_ty env fn_decl.signature.return_type;
                }
        in
        signature
    | None -> err "function %a not in env" Ast.FnIdent.pp fn_name

  let ty_lift types ty env =
    List.fold_right
      (fun name ty ->
        let size = cstr_log name env in
        Value.Ty.TNamedTuple { name; size; ty })
      types ty

  let let_variables_of_variables variables =
    match variables with
    | [] -> failwith "try lifting with no arguments"
    | x :: xs -> (x, xs)

  let lift fn_name signature types env =
    let open Ast in
    let new_signature =
      Value.Ty.
        {
          signature with
          parameters =
            List.map (fun ty -> ty_lift types ty env) signature.parameters;
          return_type = ty_lift types signature.return_type env;
        }
    in
    let new_signature = Value.Ty.to_ast_signature new_signature in
    let lift_fn_name = FnIdent.refresh "lift_" fn_name in
    let new_args_variables =
      List.map (fun _ -> TermIdent.fresh "l") signature.parameters
    in
    let variables_args_assocs =
      List.map (fun v -> (v, None)) new_args_variables
    in
    (* reverse the order of the let+ variables (most nested on head of list.) *)
    let variables_stage =
      List.fold_left
        (fun v_previous _ ->
          let v_current =
            List.map
              (fun (variable, _) -> (TermIdent.fresh "v", Some (Var variable)))
              (List.hd v_previous)
          in
          v_current :: v_previous)
        [ variables_args_assocs ] types
    in
    let variables_stage =
      List.filter_map
        (fun variables ->
          match List.exists (fun (_, p) -> Option.is_none p) variables with
          | true -> None
          | false -> Some (List.map (fun (v, p) -> (v, Option.get p)) variables))
        variables_stage
    in
    let variables, variables_stage =
      match variables_stage with
      | [] -> failwith "try lifting with no args"
      | x :: xs -> (x, xs)
    in
    let cterm =
      let ((variable, variable_letbind) as vv), ands =
        let_variables_of_variables variables
      in
      let args =
        List.map (fun (variable, _) -> Synth (Var variable)) (vv :: ands)
      in
      let ty_resolve = Option.map (fun v -> Ty.Var v) new_signature.tyvars in
      LetPlus
        {
          variable;
          lterm = variable_letbind;
          ands;
          term = Synth (FnCall { fn_name = Left fn_name; ty_resolve; args });
        }
    in
    let body =
      List.fold_left
        (fun cterm variables ->
          let (variable, variable_letbind), ands =
            let_variables_of_variables variables
          in
          LetPlus { variable; lterm = variable_letbind; ands; term = cterm })
        cterm variables_stage
    in
    let lift_fn =
      Ast.
        {
          fn_name = lift_fn_name;
          signature = new_signature;
          args = new_args_variables;
          body;
        }
    in
    (*    let () = log "%a\n\n" Pp.pp_fn lift_fn in*)
    let env = add_function lift_fn env in
    (env, (lift_fn_name, new_signature))
end

let rec ty_substitute types = function
  | Ast.Ty.Bool -> Ast.Ty.Bool
  | App { name; ty } ->
      let ty = ty_substitute types ty in
      App { name; ty }
  | Fun signature ->
      let signature = ty_substitute_sig types signature in
      Fun signature
  | Var variable as default ->
      types |> List.assoc_opt variable |> Option.value ~default

and ty_substitute_sig types signature =
  let { tyvars; parameters; return_type } : _ Ast.Ty.signature = signature in
  {
    tyvars;
    parameters = List.map (ty_substitute types) parameters;
    return_type = ty_substitute types return_type;
  }

let reduce_op = function
  | Operator.Not (value, ty) ->
      let () = assert (Value.Ty.is_bool ty) in
      (Value.not value, ty)
  | Xor ((lvalue, lty'), (rvalue, rty)) ->
      let () = assert (Value.Ty.(is_bool lty' && is_bool rty)) in
      (Value.( lxor ) lvalue rvalue, lty')
  | And ((lvalue, lty'), (rvalue, rty)) ->
      let () = assert (Value.Ty.(is_bool lty' && is_bool rty)) in
      (Value.( land ) lvalue rvalue, lty')
  | Or ((lvalue, lty'), (rvalue, rty)) ->
      let () = assert (Value.Ty.(is_bool lty' && is_bool rty)) in
      (Value.( lor ) lvalue rvalue, lty')

let rec eval_sterm env = function
  | Ast.Var variable -> (env, Env.lookup variable env)
  | Fn { fn_ident } ->
      let signature = Env.signature ~instance:false fn_ident None env in
      (env, (Value.VFunction fn_ident, Value.Ty.TFun signature))
  | Lookup { lterm; index } ->
      let env, (value, ty) = eval_sterm env lterm in
      let ty =
        match Value.Ty.(elt ty) with
        | None -> err "lookup: not a tuple type"
        | Some ty -> ty
      in
      let value = Value.get index value in
      (env, (value, ty))
  | Reindex { lhs; rhs; lterm } ->
      let prefix = lhs @ rhs in
      let nap_lhs = Env.naperians lhs env in
      let nap_rhs = Env.naperians rhs env in
      let env, (value, ty) = eval_sterm env lterm in
      let value = Value.reindex_lr nap_lhs nap_rhs value in
      (*      let () =
        log "reindex lterm ty : %a\nprefix = %a\n\n" Value.Ty.pp ty
          (Format.pp_print_list
             ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
             Ast.TyDeclIdent.pp)
          prefix
      in*)
      let ty_elt = Option.get @@ Value.Ty.remove_prefix prefix ty in
      let ty =
        List.fold_right
          (fun cstr ty ->
            let size = Env.cstr_log cstr env in
            Value.Ty.TNamedTuple { name = cstr; size; ty })
          (rhs @ lhs) ty_elt
      in
      (env, (value, ty))
  | Circ sterm ->
      let env, (value, ty) = eval_sterm env sterm in
      let value = Value.circ value in
      let wrapper =
        match Value.Ty.cstr ty with
        | None -> err "Not a tuple type"
        | Some prefix -> prefix
      in
      let size = Env.cstr_log wrapper env in
      let lty = Value.Ty.(named_tuple wrapper size ty) in
      (env, (value, lty))
  | Lift { tys; func } ->
      let env, (value, ty) = eval_sterm env func in
      let signature =
        match ty with
        | Value.Ty.TFun signature -> signature
        | TBool | TVar _ | TNamedTuple _ -> failwith "not a function"
      in
      let fn_name =
        match value with
        | Value.VFunction fn_name -> fn_name
        | VBool _ | VArray _ -> err "lift : expect a function pointer"
      in
      let env, (fn_name, signature) = Env.lift fn_name signature tys env in
      let signature =
        Value.Ty.of_ast_signature (Fun.flip Env.cstr_log env) signature
      in
      let value = Value.VFunction fn_name in
      (env, (value, Value.Ty.TFun signature))
  | FnCall { fn_name; ty_resolve; args } ->
      (*      let () = log "fncall : %a\n" Pp.pp_fn_name fn_name in
      let () = log "env = %a\n" Env.pp env in*)
      let env, args =
        List.fold_left_map
          (fun env term ->
            let env, (value, _) = eval_cterm env term in
            (env, value))
          env args
      in
      let fnident =
        match fn_name with
        | Either.Left fnident -> fnident
        | Right termident ->
            let value, _ = Env.lookup termident env in
            let e =
              match Value.as_function value with
              | None ->
                  err "id %a is not a function pointer: %a" Ast.TermIdent.pp
                    termident Value.pp value
              | Some e -> e
            in
            e
      in
      let fn_decl = Env.fn_declaration fnident env in
      let ty_resolve =
        Option.map
          (fun ty ->
            let ty = Env.of_ty env ty in
            Env.to_ty env ty)
          ty_resolve
      in
      (* ignore env of the called function, otherwise we lose the current env. *)
      let _, r = eval env fn_decl ty_resolve args in
      (env, r)
  | Operator operator ->
      let env, r = Operator.traverse eval_cterm env operator in
      (env, reduce_op r)
  | Ann (cterm, _ty) ->
      let ((_, _cty) as c) = eval_cterm env cterm in
      c

and eval_cterm env = function
  | Ast.False -> (env, (Value.VBool false, Value.Ty.TBool))
  | True -> (env, (Value.VBool true, Value.Ty.TBool))
  | Constructor { ty; terms } ->
      let cstr_log = Env.cstr_log ty env in
      let () = assert (List.compare_length_with terms cstr_log = 0) in
      let env, eter_ty = List.fold_left_map eval_cterm env terms in
      let eterms, etypes = List.split eter_ty in
      let ty_elt =
        match etypes with
        | [] -> err "Constructor with no args is forbidden"
        | t :: _ -> t
      in
      let ty = Value.Ty.named_tuple ty cstr_log ty_elt in
      let v = Value.VArray (Array.of_list eterms) in
      (env, (v, ty))
  | Let { variable; term; k } ->
      let env, (value, ty) = eval_sterm env term in
      let env = Env.bind_variable variable value ty env in
      eval_cterm env k
  | LetPlus { variable; lterm; ands; term } ->
      let env, (vvalue, vty) = eval_sterm env lterm in
      let cstr, size =
        match Value.Ty.cstr vty with
        | None -> err "Type is not a cstr type."
        | Some cstr ->
            let size = Env.cstr_log cstr env in
            (cstr, size)
      in
      let env, ands =
        List.fold_left_map
          (fun env (variable, lterm) ->
            let env, (value, aty) = eval_sterm env lterm in
            let () =
              match Value.Ty.cstrql vty aty with
              | true -> ()
              | false -> err "let+: ands not same constructor"
            in
            (env, (variable, (value, aty))))
          env ands
      in
      let ands = (variable, (vvalue, vty)) :: ands in
      let values = List.map (fun (_, (v, _)) -> v) ands in
      let args =
        List.map
          (fun (name, (_v, lty)) ->
            let ty =
              match Value.Ty.remove_prefix [ cstr ] lty with
              | Some ty -> ty
              | None ->
                  err "Wrong prefix prefix = [%a] - ty = \n" Ast.TyDeclIdent.pp
                    cstr
            in
            (name, ty))
          ands
      in
      let level = 1 in
      let ret = ref None in
      let value =
        Value.mapn' level
          (fun values ->
            let env =
              List.fold_left2
                (fun env (indent, ty) value ->
                  Env.bind_variable indent value ty env)
                env args values
            in
            let _, (value, ty) = eval_cterm env term in
            let () = if Option.is_none !ret then ret := Some ty in
            value)
          values
      in
      let ty_e =
        match !ret with None -> err "option is empty" | Some ty -> ty
      in
      let lty = Value.Ty.TNamedTuple { name = cstr; size; ty = ty_e } in
      (env, (value, lty))
  | Log { message; variables; k } ->
      let () = ignore (message, variables) in
      eval_cterm env k
  | Synth sterm -> eval_sterm env sterm

and eval env (fn : Ast.fn_declaration) ty_args vals =
  let Ast.
        {
          fn_name = current_function;
          signature = { tyvars; parameters; return_type = _ };
          args;
          body;
        } =
    fn
  in
  (*  let () = log "eval : %a\n" Ast.FnIdent.pp current_function in*)
  let types =
    match (tyvars, ty_args) with
    | Some tv, Some ta -> [ (tv, ta) ]
    | None, None -> []
    | Some lhs, None ->
        err "eval %a : expect type instance for : %a\n" Ast.FnIdent.pp
          current_function Ast.TyIdent.pp lhs
    | None, Some rhs ->
        err "eval %a : no type instance expected but found : %a\n"
          Ast.FnIdent.pp current_function Pp.pp_ty rhs
  in
  let env = Env.init_tyvariables types env in
  let env = Env.init_variables (List.combine args parameters) vals env in
  let env = { env with current_function = Some current_function } in
  eval_cterm env body

let eval_node fn_name ty_args args env = function
  | Ast.NTy tydel ->
      let env = Env.add_types tydel env in
      Either.left env
  | Ast.NFun fn_decl -> (
      match Ast.FnIdent.equal fn_name fn_decl.fn_name with
      | false ->
          let env = Env.add_function fn_decl env in
          Either.left env
      | true ->
          let value = eval env fn_decl ty_args args in
          Either.right value)

let eval ast fn_name ty_args args =
  ast
  |> find_fold_map (eval_node fn_name ty_args args) Env.init
  |> Either.find_right
