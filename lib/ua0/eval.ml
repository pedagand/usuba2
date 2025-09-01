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
    types : (Ast.TyDeclIdent.t, Ast.TyIdent.t) Ast.ty_declaration Types.t;
    functions :
      ( Ast.TyDeclIdent.t,
        Ast.FnIdent.t,
        Ast.TyIdent.t,
        Ast.TermIdent.t )
      Ast.fn_declaration
      Functions.t;
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

  let add_function (fn : _ Ast.fn_declaration) env =
    { env with functions = Functions.add fn.fn_name fn env.functions }

  let add_types (ty : _ Ast.ty_declaration) env =
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
    | Value.Ty.TBool -> Ast.TyBool
    | TNamedTuple { name; ty; size = _ } ->
        let ty = to_ty env ty in
        TyApp { name; ty }
    | TVar v -> Ast.TyVar v
    | TFun signature ->
        let signature = to_signature env signature in
        TyFun signature

  and to_signature env = function
    | { tyvars; parameters; return_type } ->
        let parameters = List.map (to_ty env) parameters in
        let return_type = to_ty env return_type in
        { tyvars; parameters; return_type }

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
        | None -> Value.Ty.TVar variable
        | Some ty -> ty)

  and of_signature signature env =
    let Ast.{ tyvars; parameters; return_type } : _ Ast.signature = signature in

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
    | None -> err "variable %a not in env" Ast.TermIdent.pp variable

  let signature ~instance fn_name tyresolve env =
    match Functions.find_opt fn_name env.functions with
    | Some fn_decl ->
        let () = log "lookup sig : %a\n" Ast.FnIdent.pp fn_name in
        let signature =
          Value.Ty.
            {
              tyvars = fn_decl.tyvars;
              parameters =
                List.map (fun (_, ty) -> of_ty env ty) fn_decl.parameters;
              return_type = of_ty env fn_decl.return_type;
            }
        in
        let signature =
          match instance with
          | false -> signature
          | true ->
              let env =
                match (fn_decl.tyvars, tyresolve) with
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
                  parameters =
                    List.map (fun (_, ty) -> of_ty env ty) fn_decl.parameters;
                  return_type = of_ty env fn_decl.return_type;
                }
        in
        signature
    | None -> err "function %a not in env" Ast.FnIdent.pp fn_name
end

let rec ty_substitute types = function
  | Ast.TyBool -> Ast.TyBool
  | TyApp { name; ty } ->
      let ty = ty_substitute types ty in
      Ast.TyApp { name; ty }
  | TyFun signature ->
      let signature = ty_substitute_sig types signature in
      Ast.TyFun signature
  | TyVar variable as default ->
      types |> List.assoc_opt variable |> Option.value ~default

and ty_substitute_sig types signature =
  let Ast.{ tyvars; parameters; return_type } : _ Ast.signature = signature in
  Ast.
    {
      tyvars;
      parameters = List.map (ty_substitute types) parameters;
      return_type = ty_substitute types return_type;
    }

let rec eval_op env = function
  | Ast.ONot term ->
      let value, ty = eval_term env term in
      let () = assert (Value.Ty.is_bool ty) in
      let value = Value.not value in
      (value, ty)
  | OXor (lhs, rhs) ->
      let lvalue, lty' = eval_term env lhs in
      let rvalue, rty = eval_term env rhs in
      let () = assert (Value.Ty.(is_bool lty' && is_bool rty)) in
      let value = Value.( lxor ) lvalue rvalue in
      (value, lty')
  | OAnd (lhs, rhs) ->
      let lvalue, lty' = eval_term env lhs in
      let rvalue, rty = eval_term env rhs in
      let () = assert (Value.Ty.(is_bool lty' && is_bool rty)) in
      let value = Value.( land ) lvalue rvalue in
      (value, lty')
  | OOr (lhs, rhs) ->
      let lvalue, lty' = eval_term env lhs in
      let rvalue, rty = eval_term env rhs in
      let () = assert (Value.Ty.(is_bool lty' && is_bool rty)) in
      let value = Value.( lor ) lvalue rvalue in
      (value, lty')

and eval_term env = function
  | Ast.TFalse -> (Value.VBool false, Value.Ty.TBool)
  | TTrue -> (Value.VBool true, Value.Ty.TBool)
  | TVar variable -> Env.lookup variable env
  | TFn { fn_ident; tyresolve } ->
      let signature = Env.signature ~instance:false fn_ident tyresolve env in
      (Value.VFunction (fn_ident, tyresolve), Value.Ty.TFun signature)
  | TLet { variable; term; k } ->
      let value, ty = eval_term env term in
      let env = Env.bind_variable variable value ty env in
      eval_term env k
  | TOperator op -> eval_op env op
  | TThunk { lterm } ->
      let value, lty = eval_lterm env lterm in
      let ty = Value.Ty.to_ty lty in
      (value, ty)
  | TLookup { lterm; index } ->
      let value, lty' = eval_lterm env lterm in
      let ty =
        match Value.Ty.(elt @@ to_ty lty') with
        | None -> err "lookup: not a tuple type"
        | Some ty -> ty
      in
      let value = Value.get index value in
      (value, ty)
  | TLog { message; variables; k } ->
      let () = log "%s\n" message in
      let () =
        List.iter
          (fun variable ->
            let value, ty = Env.lookup variable env in
            let ty = Env.to_ty env ty in
            log "log: %a : %a = %a\n" Ast.TermIdent.pp variable Pp.pp_ty ty
              Value.pp value)
          variables
      in
      let () = log "\n" in
      eval_term env k
  | TFnCall { fn_name; ty_resolve; args } ->
      let args = List.map (fun term -> fst @@ eval_term env term) args in
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
              | Some (e, _) -> e
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
      eval env fn_decl ty_resolve args

and eval_lterm env = function
  | Ast.LLetPlus { variable; lterm; ands; term } ->
      let vvalue, vty = eval_lterm env lterm in
      let iprefix = Value.Ty.view vty in
      let prefix = List.map fst iprefix in
      let ands =
        List.map
          (fun (variable, lterm) ->
            let value, aty = eval_lterm env lterm in
            let () =
              match Value.Ty.lcstreq vty aty with
              | true -> ()
              | false -> err "let+: ands not same constructor"
            in
            (variable, (value, aty)))
          ands
      in
      let ands = (variable, (vvalue, vty)) :: ands in
      let values = List.map (fun (_, (v, _)) -> v) ands in
      let args =
        List.map
          (fun (name, (_v, lty)) ->
            let ty =
              match Value.Ty.remove_prefix prefix (Value.Ty.to_ty lty) with
              | Some ty -> ty
              | None ->
                  err "Wrong prefix prefix = [%a] - ty = \n"
                    (Format.pp_print_list Ast.TyDeclIdent.pp)
                    prefix
            in
            (name, ty))
          ands
      in

      let level = Value.Ty.nest vty in
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
            let value, ty = eval_term env term in
            let () = if Option.is_none !ret then ret := Some ty in
            value)
          values
      in
      let ty_e =
        match !ret with None -> err "option is empty" | Some ty -> ty
      in
      let lty = Value.Ty.lty iprefix ty_e in
      (value, lty)
  | LConstructor { ty; terms } ->
      let cstr_log = Env.cstr_log ty env in
      let () = assert (List.compare_length_with terms cstr_log = 0) in
      let eterms, etypes = terms |> List.map (eval_term env) |> List.split in
      let ty_elt =
        match etypes with
        | [] -> err "Constructor with no args is forbidden"
        | t :: _ -> t
      in
      let ty = Value.Ty.named_tuple ty cstr_log ty_elt in
      let lty = Value.Ty.lty [] ty in
      let v = Value.VArray (Array.of_list eterms) in
      (v, lty)
  | LRange { ty; term } ->
      let value, t = eval_term env term in
      let lty = Env.range ty t env in
      (value, lty)
  | LReindex { lhs; rhs; lterm } ->
      let prefix = lhs @ rhs in
      let nap_lhs = Env.naperians lhs env in
      let nap_rhs = Env.naperians rhs env in
      let value, lty = eval_lterm env lterm in
      let value = Value.reindex_lr nap_lhs nap_rhs value in
      let ty = Value.Ty.to_ty lty in
      let () =
        log "reindex lterm ty : %a\nprefix = %a\n\n" Value.Ty.pp ty
          (Format.pp_print_list
             ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
             Ast.TyDeclIdent.pp)
          prefix
      in
      let ty_elt = Option.get @@ Value.Ty.remove_prefix prefix ty in
      let ty =
        List.fold_right
          (fun cstr ty ->
            let size = Env.cstr_log cstr env in
            Value.Ty.TNamedTuple { name = cstr; size; ty })
          (rhs @ lhs) ty_elt
      in
      (value, Value.Ty.lty [] ty)
  | LCirc lterm ->
      let value, lty' = eval_lterm env lterm in
      let value = Value.circ value in
      let wrapper =
        match Value.Ty.prefix lty' with
        | None -> err "Not a tuple type"
        | Some prefix -> prefix
      in
      let size = Env.cstr_log wrapper env in
      let lty = Value.Ty.(named_tuple wrapper size (to_ty lty')) in
      let lty = Value.Ty.lty [] lty in
      (value, lty)

and eval env (fn : _ Ast.fn_declaration) ty_args args =
  let Ast.
        {
          fn_name = current_function;
          tyvars;
          parameters;
          return_type = _;
          body;
        } =
    fn
  in
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
  let env = Env.init_variables parameters args env in
  let env = { env with current_function = Some current_function } in
  eval_term env body

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
