module BoolOperator = struct
  type t = BNot | BXor | BAnd | BOr

  let compare = Stdlib.compare
  let equal = Stdlib.( = )
end

(* make boolean operations as passed explicilty as function arguments *)
module ExplicitBoolFun = struct
  let rec ebf_term booleans = function
    | Ast.TOperator operator -> ebf_operator booleans operator
    | TLet { variable; term; k } ->
        let term = ebf_term booleans term in
        let k = ebf_term booleans k in
        Ast.TLet { variable; term; k }
    | TLookup { lterm; index } ->
        let lterm = ebf_lterm booleans lterm in
        TLookup { lterm; index }
    | TLog { message; variables; k } ->
        let k = ebf_term booleans k in
        TLog { message; variables; k }
    | TFnCall { fn_name; ty_resolve; args } ->
        let args = List.map (ebf_term booleans) args in
        TFnCall { fn_name; ty_resolve; args }
    | TThunk { lterm } ->
        let lterm = ebf_lterm booleans lterm in
        TThunk { lterm }
    | (TFalse | TTrue | TVar _ | TFn _) as e -> e

  and ebf_operator booleans = function
    | Ast.ONot term ->
        let term = ebf_term booleans term in
        let term_name = List.assoc BoolOperator.BNot booleans in
        Ast.TFnCall
          { fn_name = Left term_name; ty_resolve = None; args = [ term ] }
    | Ast.OXor (lhs, rhs) ->
        let lhs = ebf_term booleans lhs in
        let rhs = ebf_term booleans rhs in
        let term_name = List.assoc BoolOperator.BXor booleans in
        TFnCall
          { fn_name = Left term_name; ty_resolve = None; args = [ lhs; rhs ] }
    | Ast.OAnd (lhs, rhs) ->
        let lhs = ebf_term booleans lhs in
        let rhs = ebf_term booleans rhs in
        let term_name = List.assoc BoolOperator.BAnd booleans in
        TFnCall
          { fn_name = Left term_name; ty_resolve = None; args = [ lhs; rhs ] }
    | Ast.OOr (lhs, rhs) ->
        let lhs = ebf_term booleans lhs in
        let rhs = ebf_term booleans rhs in
        let term_name = List.assoc BoolOperator.BOr booleans in
        TFnCall
          { fn_name = Left term_name; ty_resolve = None; args = [ lhs; rhs ] }

  and ebf_lterm booleans = function
    | Ast.LLetPlus { variable; lterm; ands; term } ->
        let lterm = ebf_lterm booleans lterm in
        let ands =
          List.map
            (fun (variable, lterm) ->
              let lterm = ebf_lterm booleans lterm in
              (variable, lterm))
            ands
        in
        let term = ebf_term booleans term in
        Ast.LLetPlus { variable; lterm; ands; term }
    | LConstructor { ty; terms } ->
        let terms = List.map (ebf_term booleans) terms in
        LConstructor { ty; terms }
    | LReindex { lhs; rhs; lterm } ->
        let lterm = ebf_lterm booleans lterm in
        LReindex { lhs; rhs; lterm }
    | LRange { ty; term } ->
        let term = ebf_term booleans term in
        LRange { ty; term }
    | LCirc lterm ->
        let lterm = ebf_lterm booleans lterm in
        LCirc lterm

  let ebf new_fn_name booleans fn_declaration =
    let Ast.{ body; _ } = fn_declaration in
    let body = ebf_term booleans body in
    { fn_declaration with fn_name = new_fn_name; body }
end

module LiftBoolean = struct
  module Env = struct
    module Vars = Map.Make (String)
    module Fns = Map.Make (Ast.FnIdent)
    module FnsBool = Map.Make (BoolOperator)
    open Ast

    type t = {
      cstrs : (Ast.TyDeclIdent.t * int) list;
      lifted_functions :
        (TyDeclIdent.t, FnIdent.t, TyIdent.t, TermIdent.t) Ast.fn_declaration
        Fns.t;
      env_functions :
        (TyDeclIdent.t, FnIdent.t, TyIdent.t, TermIdent.t) Ast.fn_declaration
        Fns.t;
      bool_functions :
        (TyDeclIdent.t, FnIdent.t, TyIdent.t, TermIdent.t) Ast.fn_declaration
        FnsBool.t;
    }

    let init cstrs env_functions bool_functions =
      { cstrs; env_functions; bool_functions; lifted_functions = Fns.empty }

    let lifted_function fn_ident env =
      Fns.find_opt fn_ident env.lifted_functions

    let add_lifted_functions fn_ident fn_decl env =
      let lifted_functions = Fns.add fn_ident fn_decl env.lifted_functions in
      { env with lifted_functions }

    let lift_term term env =
      List.fold_right
        (fun (cstr', arity) term ->
          let terms = List.init arity (Fun.const term) in
          Scstr.(LTerm.(Term.(funk @@ cstr cstr' terms))))
        env.cstrs term

    let lift_ty ty env = Util.Ty.lift (List.map fst env.cstrs) ty

    let lift_boolean_ty ty env =
      Util.Ty.lift_boolean (List.map fst env.cstrs) ty

    let find_env_function fn_ident env = Fns.find fn_ident env.env_functions
    let fn_not env = FnsBool.find BNot env.bool_functions
    let fn_and env = FnsBool.find BAnd env.bool_functions
    let fn_xor env = FnsBool.find BXor env.bool_functions
    let fn_or env = FnsBool.find BOr env.bool_functions
  end

  let rec lb_term env = function
    | Ast.TFn { fn_ident; tyresolve } ->
        let env, (fn_ident, tyresolve) = lb_fn_ident env fn_ident tyresolve in
        (env, Ast.TFn { fn_ident; tyresolve })
    | TFnCall { fn_name; ty_resolve; args } ->
        let env, (fn_name, ty_resolve) =
          match fn_name with
          | Either.Left fn_name ->
              let env, (fn_name, ty_resolve) =
                lb_fn_ident env fn_name ty_resolve
              in
              (env, (Either.Left fn_name, ty_resolve))
          | Either.Right _ as e ->
              let ty_resolve =
                Option.map (Fun.flip Env.lift_ty env) ty_resolve
              in
              (env, (e, ty_resolve))
        in
        let env, args = List.fold_left_map lb_term env args in
        (env, TFnCall { fn_name; ty_resolve; args })
    | (Ast.TFalse | Ast.TTrue) as term -> (env, Env.lift_term term env)
    | TVar _ as v -> (env, v)
    | TLet { variable; term; k } ->
        let env, term = lb_term env term in
        let env, k = lb_term env k in
        (env, TLet { variable; term; k })
    | TLookup { lterm; index } ->
        let env, lterm = lb_lterm env lterm in
        (env, TLookup { lterm; index })
    | TThunk { lterm } ->
        let env, lterm = lb_lterm env lterm in
        (env, TThunk { lterm })
    | TLog { message; variables; k } ->
        let env, k = lb_term env k in
        (env, TLog { message; variables; k })
    | TOperator operator -> lb_operator env operator

  and lb_fn_ident env fn_ident tyresolve =
    let tyresolve = Option.map (Fun.flip Env.lift_ty env) tyresolve in
    match Env.lifted_function fn_ident env with
    | None ->
        let fn_decl = Env.find_env_function fn_ident env in
        let env, fn_decl = lb env fn_decl in
        let env = Env.add_lifted_functions fn_ident fn_decl env in
        (env, (fn_decl.fn_name, tyresolve))
    | Some fn_decl -> (env, (fn_decl.fn_name, tyresolve))

  and lb_lterm env = function
    | Ast.LLetPlus { variable; lterm; ands; term } ->
        let env, lterm = lb_lterm env lterm in
        let env, ands =
          List.fold_left_map
            (fun env (variable, lterm) ->
              let env, lterm = lb_lterm env lterm in
              (env, (variable, lterm)))
            env ands
        in
        let env, term = lb_term env term in
        (env, Ast.LLetPlus { variable; lterm; ands; term })
    | LConstructor { ty; terms } ->
        let env, terms = List.fold_left_map lb_term env terms in
        (env, LConstructor { ty; terms })
    | LRange { ty; term } ->
        let env, term = lb_term env term in
        (env, LRange { ty; term })
    | LReindex { lhs; rhs; lterm } ->
        let env, lterm = lb_lterm env lterm in
        (env, LReindex { lhs; rhs; lterm })
    | LCirc lterm ->
        let env, lterm = lb_lterm env lterm in
        (env, LCirc lterm)

  and lb_operator env = function
    | Ast.ONot term ->
        let env, term = lb_term env term in
        let fn = Env.fn_not env in
        let term = Scstr.Term.(fn_call fn.fn_name [ term ]) in
        (env, term)
    | OAnd (lhs, rhs) ->
        let env, lhs = lb_term env lhs in
        let env, rhs = lb_term env rhs in
        let fn = Env.fn_and env in
        let term = Scstr.Term.(fn_call fn.fn_name [ lhs; rhs ]) in
        (env, term)
    | OXor (lhs, rhs) ->
        let env, lhs = lb_term env lhs in
        let env, rhs = lb_term env rhs in
        let fn = Env.fn_xor env in
        let term = Scstr.Term.(fn_call fn.fn_name [ lhs; rhs ]) in
        (env, term)
    | OOr (lhs, rhs) ->
        let env, lhs = lb_term env lhs in
        let env, rhs = lb_term env rhs in
        let fn = Env.fn_or env in
        let term = Scstr.Term.(fn_call fn.fn_name [ lhs; rhs ]) in
        (env, term)

  and lb env fn_decl =
    let Ast.{ fn_name; tyvars; parameters; return_type; body } = fn_decl in
    let return_type = Env.lift_boolean_ty return_type env in
    let parameters =
      List.map
        (fun (variable, ty) ->
          let ty = Env.lift_boolean_ty ty env in
          (variable, ty))
        parameters
    in
    let env, body = lb_term env body in
    let fn_name = Util.FnIdent.prepend "lift_boolean" fn_name in
    (env, Ast.{ fn_name; tyvars; parameters; return_type; body })
end

module Idents = struct
  let err fmt = Format.kasprintf failwith fmt

  module Env = struct
    module SMap = Map.Make (String)

    type t = {
      types : Ast.TyDeclIdent.t SMap.t;
      variables : Ast.TermIdent.t SMap.t;
      fns : Ast.FnIdent.t SMap.t;
      tyvars : Ast.TyIdent.t SMap.t;
    }

    let empty =
      {
        types = SMap.empty;
        variables = SMap.empty;
        fns = SMap.empty;
        tyvars = SMap.empty;
      }

    let add_variable name env =
      let variable = Ast.TermIdent.fresh name in
      let variables = SMap.add name variable env.variables in
      ({ env with variables }, variable)

    let add_fn name env =
      let fresh = Ast.FnIdent.fresh name in
      let fns = SMap.add name fresh env.fns in
      ({ env with fns }, fresh)

    let add_type name env =
      let fresh = Ast.TyDeclIdent.fresh name in
      let types = SMap.add name fresh env.types in
      ({ env with types }, fresh)

    let add_tyvar name env =
      let fresh = Ast.TyIdent.fresh name in
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
  end

  let rec ty env = function
    | Ast.TyBool -> Ast.TyBool
    | TyVar x ->
        let name = Env.find_tyvar x env in
        Ast.TyVar name
    | TyApp { name; ty = t } ->
        let name = Env.find_tycstr name env in
        let ty = ty env t in
        TyApp { name; ty }
    | TyFun signatu ->
        let signature = signature env signatu in
        TyFun signature

  and signature env sing =
    let Ast.{ tyvars; parameters; return_type } : _ Ast.signature = sing in
    let env, tyvars =
      match tyvars with
      | None -> (env, None)
      | Some t ->
          let env, t = Env.add_tyvar t env in
          (env, Some t)
    in
    let parameters = List.map (ty env) parameters in
    let return_type = ty env return_type in
    { tyvars; parameters; return_type }

  let rec term env = function
    | (Ast.TFalse | Ast.TTrue) as e -> e
    | Ast.TVar v ->
        let v = Env.find_variable v env in
        TVar v
    | TLet { variable; term = l; k } ->
        let t = term env l in
        let env, variable = Env.add_variable variable env in
        let k = term env k in
        TLet { variable; term = t; k }
    | TFn { fn_ident; tyresolve } ->
        let fn_ident = Env.find_fn_ident fn_ident env in
        let tyresolve = Option.map (ty env) tyresolve in
        TFn { fn_ident; tyresolve }
    | TLookup { lterm; index } ->
        let lterm = lterm' env lterm in
        TLookup { lterm; index }
    | TThunk { lterm } ->
        let lterm = lterm' env lterm in
        TThunk { lterm }
    | TLog { message; variables; k } ->
        let variables = List.map (Fun.flip Env.find_variable env) variables in
        let k = term env k in
        TLog { message; variables; k }
    | TOperator ops ->
        let op = op env ops in
        TOperator op
    | TFnCall { fn_name; ty_resolve; args } ->
        let fn_name =
          Either.map
            ~left:(Fun.flip Env.find_fn_ident env)
            ~right:(Fun.flip Env.find_variable env)
            fn_name
        in
        let ty_resolve = Option.map (ty env) ty_resolve in
        let args = List.map (term env) args in
        TFnCall { fn_name; ty_resolve; args }

  and op env = function
    | Ast.ONot t ->
        let term = term env t in
        Ast.ONot term
    | Ast.OAnd (lhs, rhs) ->
        let lhs = term env lhs in
        let rhs = term env rhs in
        OAnd (lhs, rhs)
    | Ast.OOr (lhs, rhs) ->
        let lhs = term env lhs in
        let rhs = term env rhs in
        OOr (lhs, rhs)
    | Ast.OXor (lhs, rhs) ->
        let lhs = term env lhs in
        let rhs = term env rhs in
        OXor (lhs, rhs)

  and lterm' env = function
    | Ast.LLetPlus { variable; lterm; ands; term = t } ->
        let variable = Env.find_variable variable env in
        let lterm = lterm' env lterm in
        let e = Env.clear_variables env in
        let e, ands =
          List.fold_left_map
            (fun e (variable, lterm) ->
              let e, variable = Env.add_variable variable e in
              (* Use same env to "evaluate" lterm *)
              let lterm = lterm' env lterm in
              (e, (variable, lterm)))
            e ands
        in
        let term = term e t in
        Ast.LLetPlus { variable; lterm; ands; term }
    | LConstructor { ty; terms } ->
        let terms = List.map (term env) terms in
        let ty = Env.find_tycstr ty env in
        LConstructor { ty; terms }
    | LRange { ty; term = t } ->
        let ty = List.map (Fun.flip Env.find_tycstr env) ty in
        let term = term env t in
        LRange { ty; term }
    | LReindex { lhs; rhs; lterm } ->
        let lhs = List.map (Fun.flip Env.find_tycstr env) lhs in
        let rhs = List.map (Fun.flip Env.find_tycstr env) rhs in
        let lterm = lterm' env lterm in
        LReindex { lhs; rhs; lterm }
    | LCirc lterm ->
        let lterm = lterm' env lterm in
        Ast.LCirc lterm

  let fn_declaration env fn_declaration =
    let Ast.{ fn_name; tyvars; parameters; return_type; body } =
      fn_declaration
    in
    let env, fn_name = Env.add_fn fn_name env in
    let env = Env.clear_variables env in
    let env = Env.clear_ty_variables env in
    let env, tyvars =
      match tyvars with
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
        env parameters
    in
    let return_type = ty env return_type in
    let body = term env body in
    (env, Ast.{ fn_name; tyvars; parameters; return_type; body })

  let ty_declaration env ty_declaration =
    let Ast.{ tyvar; name; size } = ty_declaration in
    let tyvar = Ast.TyIdent.fresh tyvar in
    let env, name = Env.add_type name env in
    let ty = Ast.{ tyvar; name; size } in
    (env, ty)

  let node env = function
    | Ast.NFun fn_decl ->
        let env, fn = fn_declaration env fn_decl in
        (env, Ast.NFun fn)
    | Ast.NTy type_decl ->
        let env, ty = ty_declaration env type_decl in
        (env, Ast.NTy ty)

  let of_string_ast modules =
    let _, ast = List.fold_left_map node Env.empty modules in
    ast
end
