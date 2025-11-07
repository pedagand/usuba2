let err fmt = Format.kasprintf failwith fmt
let log fmt = Format.eprintf fmt
let uncons l = match l with [] -> None | x :: xs -> Some (x, xs)

module Env = struct
  module Functions = Map.Make (Ident.FnIdent)
  module Types = Map.Make (Ident.TyDeclIdent)
  module Variables = Map.Make (Ident.TermIdent)
  module TyVariables = Map.Make (Ident.TyIdent)

  type t = {
    current_function : Ident.FnIdent.t option;
    types : Prog.tydecl Types.t;
    functions : (Value.t list -> Value.t) Functions.t;
    variables : Value.t Variables.t;
    type_variables : Prog.ty TyVariables.t;
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
          Format.fprintf format "%a - " Ident.TermIdent.pp variable)
        env.variables
    in
    ()

  let add_function (fn : Ident.FnIdent.t) (f : Value.t list -> Value.t) env =
    { env with functions = Functions.add fn f env.functions }

  let add_types (ty : Prog.tydecl) env =
    { env with types = Types.add ty.name ty env.types }

  let bind_variable variable value env =
    { env with variables = Variables.add variable value env.variables }

  let type_declaration name env =
    match Types.find_opt name env.types with
    | None -> err "type %a not in env" Ident.TyDeclIdent.pp name
    | Some e -> e

  let fn_declaration name env =
    match Functions.find_opt name env.functions with
    | None -> err "function %a not in env" Ident.FnIdent.pp name
    | Some e -> e

  (*
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
          match Ident.TyDeclIdent.equal name t with
          | true -> ()
          | false ->
              err "range prefix = %a - ty = %a" Ident.TyDeclIdent.pp t
                Ident.TyDeclIdent.pp name
        in
        range ((name, size) :: acc) q ty env

  let range prefix = range [] prefix
*)

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

  (*
  let rec to_ty env = function
    | Value.Ty.TBool -> Ty.Bool
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
    | Ty.Bool -> Value.Ty.TBool
    | App { name; ty } ->
        let Ident.{ size; _ } = type_declaration name env in
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
    let { tyvars; parameters; return_type } : _ Ty.signature = signature in

    Value.Ty.
      {
        tyvars;
        parameters = List.map (of_ty env) parameters;
        return_type = of_ty env return_type;
      }
*)

  (*
  let init_tyvariables types env =
    let type_variables =
      List.fold_left
        (fun tyvars (tyvar, ty) ->
          let ty = of_ty env ty in
          TyVariables.add tyvar ty tyvars)
        TyVariables.empty types
    in
    { env with type_variables }
*)
  let init_variables parameters values env =
    let env = clear_variables env in
    List.fold_left2
      (fun env var value -> bind_variable var value env)
      env parameters values

  let lookup variable env =
    match Variables.find_opt variable env.variables with
    | Some e -> e
    | None ->
        err "variable %a not in env\nenv = %a\n" Ident.TermIdent.pp variable pp
          env

  (*
  let signature ~instance fn_name tyresolve env =
    match Functions.find_opt fn_name env.functions with
    | Some fn_decl ->
        (*        let () = log "lookup sig : %a\n" Ident.FnIdent.pp fn_name in*)
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
                      Ident.FnIdent.pp fn_name Ident.TyIdent.pp lhs
                | None, Some rhs ->
                    err "sig %a : no type instance expected but found : %a\n"
                      Ident.FnIdent.pp fn_name Ident.pp_ty rhs
              in
              Value.Ty.
                {
                  tyvars = None;
                  parameters = List.map (of_ty env) fn_decl.signature.parameters;
                  return_type = of_ty env fn_decl.signature.return_type;
                }
        in
        signature
    | None -> err "function %a not in env" Ident.FnIdent.pp fn_name

  let ty_lift types ty env =
    List.fold_right
      (fun name ty ->
        let size = cstr_log name env in
        Value.Ty.TNamedTuple { name; size; ty })
      types ty
*)
  let let_variables_of_variables variables =
    match variables with
    | [] -> failwith "try lifting with no arguments"
    | x :: xs -> (x, xs)

  let lift _ _ _ = failwith "NYI"

  (*
  let lift fn_name signature types env =
    let open Prog in
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
              (fun (variable, _) ->
                (TermIdent.fresh "v", Some (Term.Var variable)))
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
        List.map (fun (variable, _) -> Term.Synth (Var variable)) (vv :: ands)
      in
      let ty_resolve = Option.map (fun v -> Ty.Var v) new_signature.tyvars in
      Term.LetPlus
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
          Term.LetPlus
            { variable; lterm = variable_letbind; ands; term = cterm })
        cterm variables_stage
    in
    let lift_fn =
      Ident.
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
*)
end

(*
let rec ty_substitute types = function
  | Ty.Bool -> Ty.Bool
  | App { name; ty } ->
      let ty = ty_substitute types ty in
      App { name; ty }
  | Fun signature ->
      let signature = ty_substitute_sig types signature in
      Fun signature
  | Var variable as default ->
      types |> List.assoc_opt variable |> Option.value ~default

and ty_substitute_sig types signature =
  let { tyvars; parameters; return_type } : _ Ty.signature = signature in
  {
    tyvars;
    parameters = List.map (ty_substitute types) parameters;
    return_type = ty_substitute types return_type;
  }
*)
let reduce_op = function
  | Operator.Not v -> Value.not v
  | Xor (l, r) -> Value.(l lxor r)
  | And (l, r) -> Value.(l land r)
  | Or (l, r) -> Value.(l lor r)

let rec eval_sterm env = function
  | Term.Var variable -> (env, Env.lookup variable env)
  | Fn { fn_ident } ->
      let origin = Format.asprintf "%a" Ident.FnIdent.pp fn_ident in
      let value = Env.fn_declaration fn_ident env in
      (env, Value.VFunction { origin; value })
  | Lookup { lterm; index } ->
      let env, value = eval_sterm env lterm in
      let value = Value.get index value in
      (env, value)
  | Reindex { lhs; rhs; lterm } ->
      let nap_lhs = Env.naperians lhs env in
      let nap_rhs = Env.naperians rhs env in
      let env, value = eval_sterm env lterm in
      let value = Value.reindex_lr nap_lhs nap_rhs value in
      (env, value)
  | Circ sterm ->
      let env, value = eval_sterm env sterm in
      let value = Value.circ value in
      (env, value)
  | Lift { tys; func } ->
      let env, value = eval_sterm env func in
      let origin, value =
        match value with
        | Value.VFunction f -> (f.origin, f.value)
        | VBool _ | VArray _ -> assert false
      in
      let value = Value.mapn' (List.length tys) value in
      let origin =
        Format.asprintf "lift[%a](%s)"
          (Format.pp_print_list
             ~pp_sep:(fun format () -> Format.fprintf format ", ")
             Ident.TyDeclIdent.pp)
          tys origin
      in
      let value = Value.VFunction { origin; value } in
      (env, value)
  | FnCall { fn_name; args; _ } ->
      let env, args = List.fold_left_map eval_cterm env args in
      let f =
        match fn_name with
        | Either.Left fnident -> Env.fn_declaration fnident env
        | Right termident ->
            let value = Env.lookup termident env in
            Value.as_function value
      in
      (env, f args)
  | Operator operator ->
      let env, r = Operator.traverse eval_cterm env operator in
      (env, reduce_op r)
  | Ann (cterm, _) -> eval_cterm env cterm

and eval_cterm env = function
  | Term.False -> (env, Value.VBool false)
  | True -> (env, Value.VBool true)
  | Constructor { terms; _ } ->
      let env, vs = List.fold_left_map eval_cterm env terms in
      let v = Value.VArray (Array.of_list vs) in
      (env, v)
  | Let { variable; term; k } ->
      let env, value = eval_sterm env term in
      let env = Env.bind_variable variable value env in
      eval_cterm env k
  | LetPlus { variable; prefix; lterm; ands; term } ->
      let env, vvalue = eval_sterm env lterm in
      let env, ands =
        List.fold_left_map
          (fun env (variable, lterm) ->
            let env, value = eval_sterm env lterm in
            (env, (variable, value)))
          env ands
      in
      let ands = (variable, vvalue) :: ands in
      let args = List.map (fun (a, _) -> a) ands in
      let values = List.map (fun (_, v) -> v) ands in
      let level = List.length prefix in
      let value =
        Value.mapn' level
          (fun values ->
            let env =
              List.fold_left2
                (fun env indent value -> Env.bind_variable indent value env)
                env args values
            in
            let _, value = eval_cterm env term in
            value)
          values
      in
      (env, value)
  | Log { message; variables; k } ->
      let () = ignore (message, variables) in
      eval_cterm env k
  | Synth sterm -> eval_sterm env sterm

let eval_node env (fn : Prog.fndecl) vals =
  let env = Env.init_variables fn.args vals env in
  let _, v = eval_cterm env fn.body in
  v

let eval_node env = function
  | Prog.NTy tydel -> Env.add_types tydel env
  | Prog.NFun fn_decl ->
      Env.add_function fn_decl.fn_name (eval_node env fn_decl) env

let eval prog =
  let env = List.fold_left eval_node Env.init prog in
  env.Env.functions
