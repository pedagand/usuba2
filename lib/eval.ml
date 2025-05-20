module Types = Map.Make (Ast.TyDeclIdent)
module Functions = Map.Make (Ast.FnIdent)
module Variables = Map.Make (Ast.TermIdent)

let rec find_fold_map f acc = function
  | [] -> Either.left acc
  | t :: q -> (
      let res = f acc t in
      match res with
      | Either.Left acc -> find_fold_map f acc q
      | Right _ as r -> r)

let rec mapn f lists =
  let args, lists =
    List.split
    @@ List.filter_map (function [] -> None | t :: q -> Some (t, q)) lists
  in
  match args with [] -> [] | args -> f args :: mapn f lists

let mapn f lists =
  match lists with
  | [] -> []
  | t :: q ->
      let l = List.length t in
      let () =
        assert (List.for_all (fun list -> List.compare_length_with list l = 0) q)
      in
      mapn f lists

let err fmt = Printf.ksprintf failwith fmt

module Cty = struct
  type signature = {
    ty_vars : Ast.TyIdent.t list;
    parameters : t list;
    return_type : t;
  }

  and t = TyTuple of { size : int; ty : t } | TyFun of signature | TyBool
end

module Value = struct
  type t =
    | VBool of bool
    | Varray of t Array.t
    | VFunction of Ast.FnIdent.t * Ast.ty list option

  let true' = VBool true
  let false' = VBool false

  let rec map2' f lhs rhs =
    match (lhs, rhs) with
    | VBool lhs, VBool rhs -> VBool (f lhs rhs)
    | Varray lhs, Varray rhs -> Varray (Array.map2 (map2' f) lhs rhs)
    | VBool _, Varray _ | Varray _, VBool _ | VFunction _, _ | _, VFunction _ ->
        assert false

  let rec map2 f lhs rhs =
    match (lhs, rhs) with
    | (VBool _ as lhs), (VBool _ as rhs) -> f lhs rhs
    | Varray lhs, Varray rhs -> Varray (Array.map2 (map2 f) lhs rhs)
    | VBool _, Varray _ | Varray _, VBool _ | VFunction _, _ | _, VFunction _ ->
        assert false

  let rec map' f = function
    | VBool b -> VBool (f b)
    | Varray a -> Varray (Array.map (map' f) a)
    | VFunction _ -> assert false

  let get i = function
    | Varray array -> array.(i)
    | VBool _ as v -> if i = 0 then v else assert false
    | VFunction _ -> assert false

  let as_function = function
    | VFunction (fn_ident, e) -> Some (fn_ident, e)
    | VBool _ | Varray _ -> None

  let rec make_pure_nested ty value =
    match ty with
    | Ast.TyTuple { size; ty } ->
        Varray (Array.init size (fun _ -> make_pure_nested ty value))
    | Ast.TyBool | TyFun _ -> value
    | Ast.TyApp _ | TyVarApp _ -> assert false

  let make_pure ty value =
    match ty with
    | Ast.TyTuple { size; ty = _ } -> Varray (Array.init size (Fun.const value))
    | Ast.TyBool | TyFun _ -> value
    | Ast.TyApp _ | TyVarApp _ -> assert false

  let tabulate size f =
    let array = Array.init size f in
    Varray array

  let rec pp format = function
    | VBool true -> Format.fprintf format "1"
    | VBool false -> Format.fprintf format "0"
    | Varray array ->
        let pp_sep format () = Format.pp_print_string format ", " in
        Format.pp_print_array ~pp_sep pp format array
    | VFunction (fn, tys) ->
        let pp_none _format () = () in
        let pp_option =
          Format.pp_print_option ~none:pp_none @@ fun format tys ->
          Format.fprintf format "[%a]" Pp.pp_tys tys
        in
        Format.fprintf format "%a%a" Ast.FnIdent.pp fn pp_option tys
end

module Ty = struct
  let are_same_ty_ctsr lhs rhs =
    match (lhs, rhs) with
    | ( Ast.TyApp { name = lhs; ty_args = _ },
        Ast.TyApp { name = rhs; ty_args = _ } ) ->
        Ast.TyDeclIdent.equal lhs rhs
    | TyVarApp { name = lhs; ty_args = _ }, TyVarApp { name = rhs; ty_args = _ }
      ->
        Ast.TyIdent.equal lhs rhs
    | TyTuple { size = lhs; ty = _ }, TyTuple { size = rhs; ty = _ } ->
        Int.equal lhs rhs
    | TyBool, TyBool -> true
    | _, _ -> false

  let substitute ty = function
    | Ast.TyVarApp { name; ty_args = _ } ->
        Ast.TyVarApp { name; ty_args = Some ty }
    | TyApp { name; ty_args = _ } -> TyApp { name; ty_args = Some ty }
    | TyTuple { size; ty } -> TyTuple { size; ty }
    | TyFun _ | TyBool -> assert false

  let rec instanciate map = function
    | Ast.TyVarApp { name; ty_args = Some ty } -> (
        let ty_args = instanciate map ty in
        let ident =
          List.find_map
            (fun (tyident, e_ty) ->
              match Ast.TyIdent.equal name tyident with
              | true -> (
                  (* Since name is a type constructor, we expect TyDeclIdent *)
                  match e_ty with
                  | Either.Left tydeclident -> Some tydeclident
                  | Either.Right _ty ->
                      err "tyinstance: expected TyDeclIdent found ty")
              | false -> None)
            map
        in
        match ident with
        | None -> Ast.TyVarApp { name; ty_args = Some ty_args }
        | Some ident -> Ast.TyApp { name = ident; ty_args = Some ty_args })
    | TyVarApp { name; ty_args = None } as t -> (
        let ty =
          List.find_map
            (fun (tyident, e_ty) ->
              match Ast.TyIdent.equal name tyident with
              | true -> (
                  (* Since name is a type constructor, we expect TyDeclIdent *)
                  match e_ty with
                  | Either.Left _ ->
                      err "tyinstance: expected ty found tydeclident"
                  | Either.Right ty -> Some ty)
              | false -> None)
            map
        in
        match ty with None -> t | Some ty -> ty)
    | TyFun signature -> TyFun (instanciate_signature map signature)
    | TyApp { name; ty_args = Some ty } ->
        let ty_args = instanciate map ty in
        Ast.TyApp { name; ty_args = Some ty_args }
    | TyTuple { size; ty } ->
        let ty = instanciate map ty in
        TyTuple { size; ty }
    | (TyApp { name = _; ty_args = None } | TyBool) as ty -> ty

  and instanciate_signature map =
   fun { ty_vars; parameters; return_type } ->
    let map =
      List.filter
        (fun (id, _) ->
          not @@ List.exists (fun (t, _) -> Ast.TyIdent.equal id t) ty_vars)
        map
    in
    let parameters = List.map (instanciate map) parameters in
    let return_type = instanciate map return_type in
    { ty_vars; parameters; return_type }

  let ty_nested = function
    | Ast.TyApp { ty_args = Some ty; name = _ }
    | TyVarApp { ty_args = Some ty; name = _ }
    | TyTuple { ty; size = _ } ->
        Some ty
    | TyApp { ty_args = None; name = _ }
    | TyVarApp { ty_args = None; name = _ }
    | TyFun _ | TyBool ->
        None
end

module Env = struct
  type t = {
    type_decls : (Ast.kasumi_type_decl * Ast.ty) Types.t;
    fn_decls : Ast.kasumi_function_decl Functions.t;
    variables : (Value.t * Ast.ty) Variables.t;
    type_instances : (Ast.TyIdent.t * (Ast.TyDeclIdent.t, Ast.ty) Either.t) list;
  }

  let empty =
    {
      type_decls = Types.empty;
      fn_decls = Functions.empty;
      variables = Variables.empty;
      type_instances = [];
    }

  let instanciate ty env = Ty.instanciate env.type_instances ty
  let ty_canon tydecl env = snd @@ Types.find tydecl env.type_decls

  let rec canonical_type ty env =
    match ty with
    | Ast.TyApp { name; ty_args = _ } ->
        canonical_type (snd @@ Types.find name env.type_decls) env
    | TyTuple { size; ty } ->
        let ty = canonical_type ty env in
        Ast.TyTuple { size; ty }
    | (TyVarApp _ | TyFun _ | TyBool) as ty -> ty

  let ty_arity ty env =
    match ty with
    | Ast.TyApp { name; _ } ->
        let decl, _ = Types.find name env.type_decls in
        if decl.ty_vars = [] then 0 else 1
    | Ast.TyVarApp _ -> err "ty_arity: can not compute arity of tyvarapp"
    | Ast.TyTuple _ -> 1
    | TyFun _ | TyBool -> 0

  let size ty env =
    let ty = canonical_type ty env in
    match ty with
    | Ast.TyTuple { size; _ } -> size
    | TyBool -> 1
    | Ast.TyFun _ -> 0
    | Ast.TyApp _ | TyVarApp _ -> assert false

  let partially_applied ty env =
    let arity = ty_arity ty env in
    match ty with
    | Ast.TyApp { name; ty_args } ->
        if List.length (Option.to_list ty_args) <> arity then Some name
        else None
    | Ast.TyVarApp _ -> err "ty_arity: can not compute arity of tyvarapp"
    | Ast.TyTuple _ | TyFun _ | TyBool -> None

  let add_binding term variable env =
    let variables = Variables.add term variable env.variables in
    { env with variables }

  let clear_variables env = { env with variables = Variables.empty }

  let signature_of_function_decl (function_decl : Ast.kasumi_function_decl) =
    Ast.
      {
        ty_vars = function_decl.ty_vars;
        return_type = function_decl.return_type;
        parameters = List.map snd function_decl.parameters;
      }

  let function_decl fnident env = Functions.find fnident env.fn_decls

  let sig_function fnident env =
    let () = Format.eprintf "look for : %a\n" Ast.FnIdent.pp fnident in
    let function_decl = Functions.find fnident env.fn_decls in
    let signature = signature_of_function_decl function_decl in
    (fnident, signature)

  let function' fnident env =
    let value, signature = sig_function fnident env in
    let ty = Ast.TyFun signature in
    (value, ty)

  let value termid env = Variables.find termid env.variables
end

let rec eval_expression env =
  let ( $ ) g f x = g (f x) in
  function
  | Ast.ETrue -> (Value.true', Ast.TyBool)
  | EFalse -> (Value.false', Ast.TyBool)
  | EVar term -> Env.value term env
  | EFunVar (fn, tys) ->
      let fn_ident, signature = Env.sig_function fn env in
      let signature =
        match tys with
        | None -> signature
        | Some tys ->
            let type_mapping = instanciate_types env signature.ty_vars tys in
            Ty.instanciate_signature type_mapping signature
      in
      let ty = Ast.TyFun signature in
      let value = Value.VFunction (fn_ident, tys) in
      (value, ty)
  | EBuiltinCall { builtin; ty_args; args } ->
      eval_builin env ty_args args builtin
  | EFunctionCall { fn_name; ty_args; args } ->
      let fn_ident, ty_args =
        match fn_name with
        | Either.Left fn -> (fn, ty_args)
        | Either.Right termid ->
            let value, _s = Env.value termid env in
            let fn_ident, tys = Option.get @@ Value.as_function value in
            let ty_args =
              match tys with
              | None -> ty_args
              | Some tys ->
                  let () = assert (ty_args = []) in
                  tys
            in
            (fn_ident, ty_args)
      in
      let fn_decl = Env.function_decl fn_ident env in
      let args = List.map (fst $ eval_expression env) args in
      eval env fn_decl ty_args args
  | EOp op -> eval_op env op
  | SLetPLus { variable; expression; ands; body } ->
      let ((_, ty) as valuet) = eval_expression' env expression in
      let ands =
        List.map
          (fun (term, expression) -> (term, eval_expression' env expression))
          ands
      in
      let () =
        match
          List.for_all
            (fun (_, (_, t)) ->
              let () =
                Format.eprintf "@let+: ty = %a - t = %a\n" Pp.pp_ty ty Pp.pp_ty
                  t
              in
              Ty.are_same_ty_ctsr ty t)
            ands
        with
        | true -> ()
        | false -> err "@eval: let_plus not same type"
      in
      let args = (variable, valuet) :: ands in
      let nty = Option.get @@ Ty.ty_nested ty in
      let size = Env.size ty env in
      let array =
        Array.init size (fun index ->
            let env = Env.clear_variables env in
            let env =
              List.fold_left
                (fun env (ident, (value, _)) ->
                  let value = Value.get index value in
                  Env.add_binding ident (value, nty) env)
                env args
            in
            eval_body env body)
      in
      let values, types = Array.split array in
      let value = Value.Varray values in
      let ty_value = Array.get types 0 in
      let ty = Ty.substitute ty_value ty in
      (value, ty)
  | EIndexing { expression; indexing = { name; index } } ->
      let value, ty = eval_expression env expression in
      let ty' = Env.ty_canon name env in
      let () =
        Format.eprintf "indexing ty = %a - ty' = %a\n" Pp.pp_ty ty Pp.pp_ty ty'
      in
      (*      let () = assert (ty = ty') in*)
      let size, _ty' =
        match ty' with
        | TyTuple { size; ty } -> (size, ty)
        | TyFun _ | TyBool | TyApp _ | TyVarApp _ -> err "non-indexable type"
      in
      let () =
        if index < 0 || index >= size then
          err "invalid index : %d outside of 0-%d" index size
      in
      let value =
        match value with
        | Varray values -> Array.get values index
        | VBool _ | VFunction _ -> assert false
      in
      let ty =
        match ty' with
        | TyTuple { ty; size = _ } | TyApp { ty_args = Some ty; name = _ } -> ty
        | TyApp { ty_args = None; name = _ } | TyFun _ | TyVarApp _ | TyBool ->
            let () = Format.eprintf "@indexing2 = %a\n" Pp.pp_ty ty in
            assert false
      in
      (value, ty)

and eval_expression' env expression' =
  let value, ty = eval_expression env expression' in
  let ty = Env.instanciate ty env in
  (value, ty)

and eval_builin env ty_args args = function
  | Ast.BCirc -> failwith ""
  | BAntiCirc -> failwith ""
  | BPure ->
      let ty =
        match ty_args with
        | t :: [] -> t
        | [] -> err "@pure : missing type args"
        | _ :: _ :: _ -> err "@pure : too many ty args"
      in
      let arg =
        match args with
        | t :: [] -> t
        | [] -> err "@pure : missing arg"
        | _ :: _ :: _ -> err "@pure : too many args"
      in
      let value, _vty = eval_expression env arg in
      let ty = Env.canonical_type ty env in
      (Value.make_pure_nested ty value, ty)

and eval_op env = function
  | Ast.Unot expr ->
      let value, ty = eval_expression env expr in
      (Value.map' not value, ty)
  | BAnd (lhs, rhs) ->
      let lvalue, lty = eval_expression env lhs in
      let rvalue, rty = eval_expression env rhs in
      let () = assert (lty = rty) in
      (Value.map2' ( && ) lvalue rvalue, lty)
  | BOr (lhs, rhs) ->
      let lvalue, lty = eval_expression env lhs in
      let rvalue, rty = eval_expression env rhs in
      let () = assert (lty = rty) in
      (Value.map2' ( || ) lvalue rvalue, lty)
  | BXor (lhs, rhs) ->
      let lvalue, lty = eval_expression env lhs in
      let rvalue, rty = eval_expression env rhs in
      let () = assert (lty = rty) in
      (Value.map2' ( <> ) lvalue rvalue, lty)

and eval_statement env = function
  | Ast.StDeclaration { variable; expression } ->
      let value_ty = eval_expression env expression in
      Env.add_binding variable value_ty env
  | StConstructor { variable; ty; expressions } -> (
      let ty' = Env.canonical_type ty env in
      match ty' with
      | Ast.TyTuple { size; ty } ->
          let () = assert (List.compare_length_with expressions size = 0) in
          let values =
            List.map
              (fun expression ->
                let value, vty = eval_expression env expression in
                let vty = Env.canonical_type vty env in
                let () =
                  Format.eprintf "@stcstr: ty = %a - vty' = %a\n" Pp.pp_ty ty
                    Pp.pp_ty vty
                in
                value)
              expressions
          in
          let array = Array.of_list values in
          let value = Value.Varray array in
          Env.add_binding variable (value, ty) env
      | TyBool -> (
          match expressions with
          | t :: [] ->
              let value, t = eval_expression env t in
              let () = assert (t = TyBool) in
              Env.add_binding variable (value, t) env
          | [] -> err "cstr(bool): missing args"
          | _ :: _ :: _ -> err "cstr(boo): too many args: expects 1")
      | TyFun _s -> failwith ""
      | TyVarApp _ | TyApp _ -> assert false)

and eval_body env body =
  let Ast.{ statements; expression } = body in
  let env = List.fold_left eval_statement env statements in
  eval_expression env expression

and instanciate_types env ty_vars ty_args =
  List.map2
    (fun (tyident, kind) ty ->
      match kind with
      | Ast.KType -> (tyident, Either.Right ty)
      | KArrow _ -> (
          match Env.partially_applied ty env with
          | None -> err "@eval: expected type-constructor found type"
          | Some typedeclident -> (tyident, Either.Left typedeclident)))
    ty_vars ty_args

and eval env (fn_decl : Ast.kasumi_function_decl) ty_args args =
  let Ast.{ fn_name; ty_vars; parameters; return_type = _; body } = fn_decl in
  let () =
    Format.eprintf "fn = %a:\nty_vars = [%a]\nty_args = [%a]\n\n" Ast.FnIdent.pp
      fn_name Pp.pp_tyvars ty_vars Pp.pp_ty_args ty_args
  in
  let type_instances = instanciate_types env ty_vars ty_args in
  let env = { env with type_instances } in
  let variables =
    List.fold_left2
      (fun variables (term, ty) value ->
        let ty = Env.instanciate ty env in
        Variables.add term (value, ty) variables)
      Variables.empty parameters args
  in
  let env = Env.{ env with variables } in
  eval_body env body

let add_fndecl env (fn_decl : Ast.kasumi_function_decl) =
  Env.
    {
      env with
      fn_decls = Functions.add fn_decl.fn_name fn_decl env.Env.fn_decls;
    }

let add_typedecl env (type_decl : Ast.kasumi_type_decl) =
  let ty =
    match type_decl.definition with
    | TyApp { name; ty_args = _ } -> snd @@ Types.find name env.Env.type_decls
    | (TyTuple _ | TyFun _ | TyBool) as ty -> ty
    | TyVarApp _ -> assert false
  in
  {
    env with
    type_decls = Types.add type_decl.ty_name (type_decl, ty) env.type_decls;
  }

let eval_node fn_name ty_args args env = function
  | Ast.KnFundecl function_decl -> (
      match Ast.FnIdent.equal fn_name function_decl.fn_name with
      | true ->
          let value = eval env function_decl ty_args args in
          Either.right value
      | false ->
          let env = add_fndecl env function_decl in
          Either.left env)
  | Ast.KnTypedecl type_decl ->
      let env = add_typedecl env type_decl in
      Either.left env

let eval ast fn_name ty_args args =
  ast
  |> find_fold_map (eval_node fn_name ty_args args) Env.empty
  |> Either.find_right
