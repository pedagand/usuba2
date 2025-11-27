module Idents = struct
  let err fmt = Format.kasprintf failwith fmt

  module Env = struct
    module SMap = Map.Make (String)
    open Ident

    type t = {
      types : TyDeclIdent.t SMap.t;
      variables : TermIdent.t SMap.t;
      fns : FnIdent.t SMap.t;
      tyvars : TyIdent.t SMap.t;
    }

    let empty =
      {
        types = SMap.empty;
        variables = SMap.empty;
        fns = SMap.empty;
        tyvars = SMap.empty;
      }

    let add_variable name env =
      let variable = TermIdent.fresh name in
      let variables = SMap.add name variable env.variables in
      ({ env with variables }, variable)

    let add_fn name env =
      let fresh = FnIdent.fresh name in
      let fns = SMap.add name fresh env.fns in
      ({ env with fns }, fresh)

    let add_type name env =
      let fresh = TyDeclIdent.fresh name in
      let types = SMap.add name fresh env.types in
      ({ env with types }, fresh)

    let add_tyvar name env =
      let fresh = TyIdent.fresh name in
      let tyvars = SMap.add name fresh env.tyvars in
      ({ env with tyvars }, fresh)

    let clear_variables env = { env with variables = SMap.empty }
    let clear_ty_variables env = { env with tyvars = SMap.empty }

    let find_tyvar name env =
      match SMap.find_opt name env.tyvars with
      | None -> err "Unbound type variable : %s" name
      | Some t -> t

    let find_tycstr name env =
      match SMap.find_opt name env.types with
      | None -> err "Unbound type constructor : %s" name
      | Some t -> t

    let find_variable name env =
      match SMap.find_opt name env.variables with
      | None -> err "Unbound variable : %s" name
      | Some s -> s

    let find_fn_ident name env =
      match SMap.find_opt name env.fns with
      | None -> err "Unbound fn name : %s" name
      | Some s -> s

    let find_callable name env =
      try Either.Right (find_variable name env)
      with _ -> Either.Left (find_fn_ident name env)

    let find_variable_term name env =
      Either.fold
        ~left:(fun fn_ident -> Term.Fn { fn_ident })
        ~right:(fun s -> Var s)
        (find_callable name env)

    let tyvars env = env.tyvars |> SMap.bindings |> List.map snd
  end

  let ty env =
    Ty.bmap
      (fun env x -> Env.add_tyvar x env)
      (fun env x -> Env.find_tyvar x env)
      (fun name -> Env.find_tycstr name env)
      env

  let rec sterm env = function
    | Term.Var v -> Env.find_variable_term v env
    | Fn { fn_ident } ->
        let fn_ident = Env.find_fn_ident fn_ident env in
        Fn { fn_ident }
    | Lookup { lterm; index } ->
        let lterm = sterm env lterm in
        Lookup { lterm; index }
    | Reindex { lhs; rhs; lterm } ->
        let lhs = List.map (Fun.flip Env.find_tycstr env) lhs in
        let rhs = List.map (Fun.flip Env.find_tycstr env) rhs in
        let lterm = sterm env lterm in
        Reindex { lhs; rhs; lterm }
    | Circ lterm ->
        let lterm = sterm env lterm in
        Circ lterm
    | Lift { tys; func } ->
        let func = sterm env func in
        let tys = List.map (Fun.flip Env.find_tycstr env) tys in
        Lift { tys; func }
    | FnCall { fn_name; ty_resolve; args } ->
        let fn_name = Either.fold ~left:Fun.id ~right:Fun.id fn_name in
        let fn_name = Env.find_callable fn_name env in
        let ty_resolve = Option.map (ty env) ty_resolve in
        let args = List.map (cterm env) args in
        FnCall { fn_name; ty_resolve; args }
    | Operator ops ->
        let op = Operator.map (cterm env) ops in
        Operator op
    | Ann (c, t) ->
        let cterm = cterm env c in
        let ty = ty env t in
        Ann (cterm, ty)

  and cterm env = function
    | (Term.False | True) as e -> e
    | Let { variable; term = l; k } ->
        let t = sterm env l in
        let env, variable = Env.add_variable variable env in
        let k = cterm env k in
        Let { variable; term = t; k }
    | LetPlus { variable; prefix; lterm; ands; term = t } ->
        (*
          Evaluate the ltherm before adding variable to env.
          Otherwise variable shadowning issues.
        *)
        let lterm = sterm env lterm in
        let env, variable = Env.add_variable variable env in
        let env, ands =
          List.fold_left_map
            (fun env (variable, lterm) ->
              let lterm = sterm env lterm in
              let env, variable = Env.add_variable variable env in
              (env, (variable, lterm)))
            env ands
        in
        let term = cterm env t in
        let prefix = List.map (Fun.flip Env.find_tycstr env) prefix in
        LetPlus { variable; prefix; lterm; ands; term }
    | Constructor { ty; terms } ->
        let terms = List.map (cterm env) terms in
        let ty = Env.find_tycstr ty env in
        Constructor { ty; terms }
    | Log { message; variables; k } ->
        let variables = List.map (Fun.flip Env.find_variable env) variables in
        let k = cterm env k in
        Log { message; variables; k }
    | Synth s ->
        let sterm = sterm env s in
        Synth sterm

  let fn_declaration env fn_declaration =
    let Prog.{ fn_name; signature; args; body } = fn_declaration in
    let env = Env.clear_variables env in
    let env = Env.clear_ty_variables env in
    let env, tyvars =
      match signature.tyvars with
      | None -> (env, None)
      | Some t ->
          let env, t = Env.add_tyvar t env in
          (env, Some t)
    in
    let env, parameters =
      List.fold_left_map
        (fun env (variable, t) ->
          let ty = ty env t in
          let env, variable = Env.add_variable variable env in
          (env, (variable, ty)))
        env
        (List.combine args signature.parameters)
    in
    let return_type = ty env signature.return_type in
    let args, parameters = List.split parameters in
    let signature = { Ty.tyvars; parameters; return_type } in
    let body = cterm env body in
    (* Add name at the end to allow fn_name shadowing. *)
    let env, fn_name = Env.add_fn fn_name env in
    (env, Prog.{ fn_name; signature; args; body })

  let ty_declaration env ty_declaration =
    let Prog.{ tyvar; name; size } = ty_declaration in
    let tyvar = Ident.TyIdent.fresh tyvar in
    let env, name = Env.add_type name env in
    let ty = Prog.{ tyvar; name; size } in
    (env, ty)

  let node env = function
    | Prog.NFun fn_decl ->
        let env, fn = fn_declaration env fn_decl in
        (env, Prog.NFun fn)
    | Prog.NTy type_decl ->
        let env, ty = ty_declaration env type_decl in
        (env, Prog.NTy ty)

  let of_string_ast_env modules = List.fold_left_map node Env.empty modules

  let of_string_ast modules =
    let _, ast = List.fold_left_map node Env.empty modules in
    ast
end
