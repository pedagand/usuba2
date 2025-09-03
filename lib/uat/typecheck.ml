(*[@@@warning "-27"]*)

module Pp = Ua0.Pp

let err fmt = Format.kasprintf failwith fmt

module Env = struct
  module Vars = Map.Make (Ast.TermIdent)
  module Fns = Map.Make (Ast.FnIdent)
  module Types = Map.Make (Ast.TyDeclIdent)

  type t = {
    variables : Ast.ty Vars.t;
    functions :
      ( Ast.TyDeclIdent.t,
        Ast.FnIdent.t,
        Ast.TyIdent.t,
        Ast.TermIdent.t )
      Ua0.Ast.fn_declaration
      Fns.t;
    types : (Ast.TyDeclIdent.t, Ast.TyIdent.t) Ua0.Ast.ty_declaration Types.t;
  }

  let empty =
    { variables = Vars.empty; functions = Fns.empty; types = Types.empty }

  let add_function fn env =
    let functions = Fns.add fn.Ua0.Ast.fn_name fn env.functions in
    { env with functions }

  let add_variable variable ty env =
    let variables = Vars.add variable ty env.variables in
    { env with variables }

  let add_type ty_decl env =
    let types = Types.add ty_decl.Ua0.Ast.name ty_decl env.types in
    { env with types }

  let clear_variables env = { env with variables = Vars.empty }

  let set_variables variables env =
    let variables = Vars.of_seq @@ List.to_seq variables in
    { env with variables }

  let ty_variable variable env =
    match Vars.find_opt variable env.variables with
    | None ->
        let () =
          Vars.iter
            (fun variable ty ->
              Format.eprintf "%a : %a - " Ast.TermIdent.pp variable Pp.pp_ty ty)
            env.variables
        in
        err "Unbound variable : %a" Ast.TermIdent.pp variable
    | Some ty -> ty

  let fn_declaration fn_name env =
    match Fns.find_opt fn_name env.functions with
    | None -> err "Unbound fn : %a" Ast.FnIdent.pp fn_name
    | Some fn -> fn

  let arity name env =
    let typedecl = Types.find name env.types in
    typedecl.size

  let signature ~instance variable tyvar env =
    let pp =
      Format.pp_print_either ~left:Ast.FnIdent.pp ~right:Ast.TermIdent.pp
    in
    let signature =
      match variable with
      | Either.Left fn_ident ->
          env |> fn_declaration fn_ident |> Util.FunctionDecl.signature
      | Either.Right variable -> (
          match ty_variable variable env with
          | Ua0.Ast.TyFun signature -> signature
          | ty ->
              err "%a should be a function ty not %a" Ast.TermIdent.pp variable
                Ua0.Pp.pp_ty ty)
    in
    match instance with
    | false -> signature
    | true ->
        let tyvars =
          match (signature.tyvars, tyvar) with
          | None, None -> []
          | Some lhs, Some rhs -> [ (lhs, rhs) ]
          | None, Some _t ->
              err "call `%a`: Unexpected ty vars for function" pp variable
          | Some _, None ->
              err "call `%a`: Missing expected type variable" pp variable
        in
        (* Remove tyvars from signature since instance with remove free type variables.*)
        let signature = { signature with tyvars = None } in
        Util.Ty.instanciate_signature tyvars signature

  let rec range acc prefix ty env =
    match prefix with
    | [] -> Ua0.Ast.Lty { t = List.rev acc; ty }
    | t :: q ->
        let name, size, ty =
          match ty with
          | Ua0.Ast.TyApp { name; ty } ->
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
    let to_reindex, ty = Ua0.Util.Ty.ty_cstrs ty in
    let cstrs = destination to_reindex lhs rhs in
    Util.Ty.lift cstrs ty
end

let rec typecheck_term env = function
  | Ua0.Ast.TFalse -> (Ast.TFalse, Ua0.Ast.TyBool)
  | TTrue -> (TTrue, Ua0.Ast.TyBool)
  | TVar variable ->
      let ty = Env.ty_variable variable env in
      (TVar variable, ty)
  | TFn { fn_ident; tyresolve } ->
      let signature =
        Env.signature ~instance:false (Left fn_ident) tyresolve env
      in
      (TFn { fn_ident }, TyFun signature)
  | TLet { variable; term; k } ->
      let ((_, ty) as term) = typecheck_term env term in
      let env = Env.add_variable variable ty env in
      let ((_, ty) as k) = typecheck_term env k in
      (TLet { variable; term; k }, ty)
  | TLookup { lterm; index } ->
      (* Maybe check indexing *)
      let ((_, lty') as lterm) = typecheck_lterm env lterm in
      let ty =
        match Ua0.Util.Ty.(elt @@ to_ty lty') with
        | None -> err "lookup: not a tuple type"
        | Some ty -> ty
      in
      (TLookup { lterm; index }, ty)
  | TThunk { lterm } ->
      let ((_, lty) as lterm) = typecheck_lterm env lterm in
      (TThunk { lterm }, Util.Ty.to_ty lty)
  | TLog { message = _; variables = _; k } -> typecheck_term env k
  | TOperator operator ->
      let op, ty = typecheck_operator env operator in
      (TOperator op, ty)
  | TFnCall { fn_name; ty_resolve; args } ->
      let signature = Env.signature ~instance:true fn_name ty_resolve env in
      let args =
        List.map2
          (fun ty_expected arg ->
            let ((_, ty_arg) as term) = typecheck_term env arg in
            let () =
              if ty_expected <> ty_arg then
                let pp =
                  Format.pp_print_either ~left:Ast.FnIdent.pp
                    ~right:Ast.TermIdent.pp
                in
                err "call `%a`: expected type %a found %a" pp fn_name Ua0.Pp.pp_ty
                  ty_expected Ua0.Pp.pp_ty ty_arg
            in
            term)
          signature.parameters args
      in
      (TFnCall { fn_name; ty_resolve; args }, signature.return_type)

and typecheck_operator env =
  let check_bools env lhs rhs =
    let ((_, ly) as lhs) = typecheck_term env lhs in
    let () =
      if ly <> TyBool then err "expected Bool find : %a" Ua0.Pp.pp_ty ly
    in
    let ((_, ry) as rhs) = typecheck_term env rhs in
    let () =
      if ry <> TyBool then err "expected Bool find : %a" Ua0.Pp.pp_ty ry
    in
    (lhs, rhs)
  in
  let module Pp = Ua0.Pp in
  function
  | Ua0.Ast.ONot expr ->
      let ((_, ty) as expr) = typecheck_term env expr in
      let () =
        if ty <> Ua0.Ast.TyBool then err "expected Bool find : %a" Pp.pp_ty ty
      in
      (Ua0.Ast.ONot expr, ty)
  | OXor (lhs, rhs) ->
      let lhs, rhs = check_bools env lhs rhs in
      (OXor (lhs, rhs), TyBool)
  | OAnd (lhs, rhs) ->
      let lhs, rhs = check_bools env lhs rhs in
      (OAnd (lhs, rhs), TyBool)
  | OOr (lhs, rhs) ->
      let lhs, rhs = check_bools env lhs rhs in
      (OOr (lhs, rhs), TyBool)

and typecheck_lterm env = function
  | Ua0.Ast.LConstructor { ty = name; terms } ->
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
      let ((_, ty) as term) = typecheck_term env term in
      let terms =
        List.map
          (fun term ->
            let ((_, t) as term) = typecheck_term env term in
            let () =
              if not @@ Ua0.Util.Ty.equal t ty then
                err "cstr `%a` : not uniform type - %a <> %a" Ast.TyDeclIdent.pp
                  name Ua0.Pp.pp_ty t Ua0.Pp.pp_ty ty
            in
            term)
          terms
      in
      let lty = Ua0.(Util.Ty.lty [] (Ast.TyApp { name; ty })) in
      (Ast.LConstructor { ty = name; terms = term :: terms }, lty)
  | Ua0.Ast.LLetPlus { variable; lterm; ands; term } ->
      let ((_, vty) as lterm) = typecheck_lterm env lterm in
      let prefix' = Ua0.Util.Ty.prefix vty in
      let prefix = List.map fst prefix' in
      let ands =
        List.map
          (fun (variable, lterm) ->
            let ((_, aty) as lterm) = typecheck_lterm env lterm in
            let () =
              match Ua0.Util.Ty.lcstreq vty aty with
              | true -> ()
              | false -> err "let+: ands not same constructor"
            in
            (variable, lterm))
          ands
      in
      let variables = (variable, lterm) :: ands in
      let env, _args =
        List.fold_left_map
          (fun env (name, (_, vty)) ->
            let ty =
              match Ua0.Util.Ty.remove_prefix prefix (Util.Ty.to_ty vty) with
              | Some ty -> ty
              | None ->
                  err "Wrong prefix prefix = [%a] - ty = \n"
                    (Format.pp_print_list Ast.TyDeclIdent.pp)
                    prefix
            in
            let env = Env.add_variable name ty env in
            (env, (name, ty)))
          env variables
      in
      let ((_, ty) as term) = typecheck_term env term in
      (LLetPlus { variable; lterm; ands; term }, Util.Ty.lty prefix' ty)
  | LRange { ty; term } ->
      let ((_, t) as term) = typecheck_term env term in
      let lty = Env.range ty t env in
      (LRange { ty; term }, lty)
  | LReindex { lhs; rhs; lterm } ->
      let ((_, lty') as lterm) = typecheck_lterm env lterm in
      let cstrs, ty = Util.Ty.(prefix @@ to_ty lty') in
      let _cstrs_reindexed = Ua0.Util.Cstrs.reorder lhs rhs cstrs in
      let ty_new =
        List.fold_right
          (fun name ty -> Ua0.Ast.TyApp { name; ty })
          (rhs @ lhs) ty
      in
      let () =
        Format.eprintf "source = %a - reindex = %a\n" Ua0.Pp.pp_ty
          (Util.Ty.to_ty lty') Ua0.Pp.pp_ty ty_new
      in
      (LReindex { lhs; rhs; lterm }, Util.Ty.lty [] ty_new)
  | LCirc lterm ->
      let ((_, lty) as lterm) = typecheck_lterm env lterm in
      let wrapper =
        match Ua0.Util.Ty.hd lty with
        | None -> err "Not a tuple type"
        | Some hd -> hd
      in
      let lty =
        Util.Ty.lty []
          (Ua0.Ast.TyApp { name = wrapper; ty = Util.Ty.to_ty lty })
      in
      (LCirc lterm, lty)

let typecheck_function env fn =
  let Ua0.Ast.{ fn_name; tyvars; parameters; return_type; body } = fn in
  let env = Env.clear_variables env in
  let env =
    List.fold_left
      (fun env (variable, ty) -> Env.add_variable variable ty env)
      env parameters
  in
  let ((_, ty) as body) = typecheck_term env body in
  let () =
    match Ua0.Util.Ty.equal return_type ty with
    | true -> ()
    | false ->
        err "fn `%a` : return type %a but term has the type : %a" Ast.FnIdent.pp
          fn_name Ua0.Pp.pp_ty return_type Ua0.Pp.pp_ty ty
  in
  let fn_uat = Ast.{ fn_name; tyvars; parameters; return_type; body } in
  (Env.add_function fn env, fn_uat)

let add_typedecl = Fun.flip Env.add_type

let of_ua0_node env = function
  | Ua0.Ast.NFun fn_declaration ->
      let env, fn_decl = typecheck_function env fn_declaration in
      (env, Ast.NFun fn_decl)
  | Ua0.Ast.NTy type_decl -> (add_typedecl env type_decl, Ast.NTy type_decl)

let of_ua0_module env = List.fold_left_map of_ua0_node env
let of_ua0_module = of_ua0_module Env.empty
