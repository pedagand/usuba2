(*[@@@warning "-27"]*)

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

  let set_variables variables env =
    let variables = Vars.of_seq @@ List.to_seq variables in
    { env with variables }

  let ty_variable variable env =
    match Vars.find_opt variable env.variables with
    | None -> err "Unbound variable : %a" Ast.TermIdent.pp variable
    | Some ty -> ty

  let fn_declaration fn_name env =
    match Fns.find_opt fn_name env.functions with
    | None -> err "Unbound fn : %a" Ast.FnIdent.pp fn_name
    | Some fn -> fn

  let arity name env =
    let typedecl = Types.find name env.types in
    typedecl.size

  let signature variable tyvar env =
    let signature =
      match variable with
      | Either.Left fn_ident ->
          env |> fn_declaration fn_ident |> Util.FunctionDecl.signature
      | Either.Right variable -> (
          match ty_variable variable env with
          | Ast.TyFun signature -> signature
          | ty ->
              err "%a should be a function ty not %a" Ast.TermIdent.pp variable
                Pp.pp_ty ty)
    in
    let tyvars =
      match (signature.tyvars, tyvar) with
      | None, None -> []
      | Some lhs, Some rhs -> [ (lhs, rhs) ]
      | None, Some _t -> err "Unexpected ty vars for function"
      | Some _, None -> err "Missing expected type variable"
    in
    Util.Ty.instanciate_signature tyvars signature

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

  let rec skip eq to_skip list =
    match (to_skip, list) with
    | [], l | _ :: _, ([] as l) -> l
    | t :: q, x :: xs ->
        if eq t x then skip eq q xs else invalid_arg "to_skip: no full prefix"

  let uncons list = match list with [] -> (None, []) | t :: q -> (Some t, q)

  let rec destination to_reindex re_lindex re_rindex =
    match to_reindex with
    | [] -> []
    | t :: q ->
        let lhd, ltail = uncons re_lindex in
        let rhd, rtail = uncons re_rindex in
        let is_head = Option.equal Ast.TyDeclIdent.equal (Some t) in

        if is_head lhd then
          let q = skip Ast.TyDeclIdent.equal ltail q in
          re_rindex @ destination q re_lindex re_rindex
        else if is_head rhd then
          let q = skip Ast.TyDeclIdent.equal rtail q in
          re_lindex @ destination q re_rindex re_lindex
        else t :: destination q re_lindex re_rindex

  let reindex ~lhs ~rhs lty =
    let ty = Util.Ty.to_ty lty in
    let to_reindex, ty = Util.Ty.ty_cstrs ty in
    let cstrs = destination to_reindex lhs rhs in
    Util.Ty.lift cstrs ty
end

let rec typecheck_term env = function
  | Ast.TFalse | TTrue -> Ast.TyBool
  | TVar variable -> Env.ty_variable variable env
  | TFn { fn_ident; tyresolve } ->
      let signature = Env.signature (Left fn_ident) tyresolve env in
      TyFun signature
  | TLet { variable; term; k } ->
      let ty = typecheck_term env term in
      let env = Env.add_variable variable ty env in
      typecheck_term env k
  | TLookup { lterm; index = _ } ->
      (* Maybe check indexing *)
      let lty' = typecheck_lterm env lterm in
      let ty =
        match Util.Ty.(elt @@ to_ty lty') with
        | None -> err "lookup: not a tuple type"
        | Some ty -> ty
      in
      ty
  | TThunk { lterm } ->
      let lty = typecheck_lterm env lterm in
      Util.Ty.to_ty lty
  | TLog { message = _; variables = _; k } -> typecheck_term env k
  | TOperator operator -> typecheck_operator env operator
  | TFnCall { fn_name; ty_resolve; args } ->
      let signature = Env.signature fn_name ty_resolve env in
      let tyargs = List.map (typecheck_term env) args in
      let () =
        List.iter2
          (fun ty_expected ty_arg ->
            if ty_expected <> ty_arg then
              err "Fncall: expected type %a found %a" Pp.pp_ty ty_expected
                Pp.pp_ty ty_arg)
          signature.parameters tyargs
      in
      signature.return_type

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
  | Ast.LLetPlus { variable; lterm; ands; term } ->
      let vty = typecheck_lterm env lterm in
      let prefix' = Util.Ty.prefix vty in
      let prefix = List.map fst prefix' in
      let ands =
        List.map
          (fun (variable, lterm) ->
            let aty = typecheck_lterm env lterm in
            let () =
              match Util.Ty.lcstreq vty aty with
              | true -> ()
              | false -> err "let+: ands not same constructor"
            in
            (variable, aty))
          ands
      in
      let variables = (variable, vty) :: ands in
      let args =
        List.map
          (fun (name, vty) ->
            let ty =
              match Util.Ty.remove_prefix prefix (Util.Ty.to_ty vty) with
              | Some ty -> ty
              | None ->
                  err "Wrong prefix prefix = [%a] - ty = \n"
                    (Format.pp_print_list Ast.TyDeclIdent.pp)
                    prefix
            in
            (name, ty))
          variables
      in
      let env = Env.set_variables args env in
      let ty = typecheck_term env term in
      Util.Ty.lty prefix' ty
  | LConstructor { ty = name; terms } ->
      let cstr_arity = Env.arity name env in
      let () =
        match List.compare_length_with terms cstr_arity = 0 with
        | true -> ()
        | false ->
            err "%a expectes %u args but %u was provied" Ast.TyDeclIdent.pp name
              cstr_arity (List.length terms)
      in
      let term, terms =
        match terms with
        | [] -> err "Constructor with no args is forbidden"
        | t :: q -> (t, q)
      in
      let ty = typecheck_term env term in
      let () =
        List.iter
          (fun term ->
            let t = typecheck_term env term in
            if t <> ty then err "not uniform type")
          terms
      in
      Util.Ty.lty [] (Ast.TyApp { name; ty })
  | LRange { ty; term } ->
      let t = typecheck_term env term in
      Env.range ty t env
  | LReindex { lhs; rhs; lterm } ->
      let lty = typecheck_lterm env lterm in
      let ty = Env.reindex ~lhs ~rhs lty in
      Util.Ty.lty [] ty
  | LCirc lterm ->
      let lty = typecheck_lterm env lterm in
      let wrapper =
        match Util.Ty.hd lty with
        | None -> err "Not a tuple type"
        | Some hd -> hd
      in
      Util.Ty.lty [] (Ast.TyApp { name = wrapper; ty = Util.Ty.to_ty lty })

let typecheck_function env fn =
  let Ast.{ fn_name = _; tyvars = _; parameters; return_type; body } = fn in
  let env = Env.clear_variables env in
  let env =
    List.fold_left
      (fun env (variable, ty) -> Env.add_variable variable ty env)
      env parameters
  in
  let ty = typecheck_term env body in
  let () = assert (ty = return_type) in
  (Env.add_function fn env, ty)
