(*[@@@warning "-27"]*)

module Env = struct
  open Ident

  type t = {
    current_function : string;
    variables : Prog.ty TermIdent.Map.t;
    functions : Prog.fndecl FnIdent.Map.t;
    types : Prog.tydecl TyDeclIdent.Map.t;
  }

  let empty =
    {
      current_function = String.empty;
      variables = TermIdent.Map.empty;
      functions = FnIdent.Map.empty;
      types = TyDeclIdent.Map.empty;
    }

  let set_function current_function e = { e with current_function }

  let add_function fn env =
    let functions = FnIdent.Map.add fn.Prog.fn_name fn env.functions in
    { env with functions }

  let add_variable variable ty env =
    let variables = TermIdent.Map.add variable ty env.variables in
    { env with variables }

  let add_variables variables env =
    let variables =
      TermIdent.Map.add_seq (List.to_seq variables) env.variables
    in
    { env with variables }

  let add_type ty_decl env =
    let types = TyDeclIdent.Map.add ty_decl.Prog.name ty_decl env.types in
    { env with types }

  let clear_variables env = { env with variables = TermIdent.Map.empty }
  let ty_variable variable env = TermIdent.Map.find variable env.variables
  let fn_declaration fn_name env = FnIdent.Map.find fn_name env.functions

  let arity name env =
    let typedecl = TyDeclIdent.Map.find name env.types in
    typedecl.size
end

exception Ill_typed

let rec typecheck env ty tm =
  match (ty, tm) with
  | Ty.Bool, Term.False -> ()
  | Bool, True -> ()
  | App { names = name :: names; bty }, Constructor { ty = _name'; terms } ->
      if Env.arity name env <> List.length terms then raise Ill_typed;
      let ty = Ty.S.apps names bty in
      terms |> List.iter (typecheck env ty)
  | ty0, Let { variable; term; k } ->
      let ty = typesynth env term in
      let env = Env.add_variable variable ty env in
      typecheck env ty0 k
  | ty0, LetPlus { variable; prefix; lterm; ands; term } -> (
      try
        let ty0 = Ty.take prefix ty0 in
        let ty_var = lterm |> typesynth env |> Ty.take prefix in
        let ty_ands =
          List.map
            (fun (var, tm) ->
              let ty = tm |> typesynth env |> Ty.take prefix in
              (var, ty))
            ands
        in
        let env = Env.add_variables ((variable, ty_var) :: ty_ands) env in
        typecheck env ty0 term
      with Not_found -> raise Ill_typed)
  | ty0, Log { message = _; variables = _; k } -> typecheck env ty0 k
  | ty0, Synth t ->
      let ty = typesynth env t in
      if not (Ty.equal ty ty0) then raise Ill_typed;
      ()
  | _, _ -> raise Ill_typed

and typesynth env = function
  | Var variable -> Env.ty_variable variable env
  | Fn { fn_ident } ->
      let fn = Env.fn_declaration fn_ident env in
      let si = fn.signature in
      Ty.S.fn ~tyvars:si.tyvars si.parameters si.return_type
  | Lookup { lterm; index } -> (
      let ty = typesynth env lterm in
      match ty with
      | App { bty; names = name :: names } when index < Env.arity name env ->
          Ty.S.apps names bty
      | _ -> raise Ill_typed)
  | Operator operator -> typesynth_operator env operator
  | FnCall { fn_name; ty_resolve; args } ->
      let si =
        match fn_name with
        | Left fn_ident ->
            let fn = Env.fn_declaration fn_ident env in
            fn.signature
        | Right x -> (
            let ty = Env.ty_variable x env in
            match ty with Fun si -> si | _ -> raise Ill_typed)
      in
      let parameters, return_type =
        match (si.tyvars, ty_resolve) with
        | None, None -> (si.parameters, si.return_type)
        | Some a, Some ty ->
            let parameters = List.map (Ty.bind a ty) si.parameters in
            let return_type = Ty.bind a ty si.return_type in
            (parameters, return_type)
        | _, _ -> raise Ill_typed
      in
      List.iter2
        (fun ty_expected arg -> typecheck env ty_expected arg)
        parameters args;
      return_type
  | Reindex { lhs; rhs; lterm } -> (
      let ty = typesynth env lterm in
      try
        let ty = Ty.take lhs ty in
        let ty = Ty.take rhs ty in
        Ty.S.apps (rhs @ lhs) ty
      with Not_found -> raise Ill_typed)
  | Circ t -> (
      let ty = typesynth env t in
      match ty with
      | App { names = name :: names; bty } ->
          Ty.S.apps (name :: name :: names) bty
      | _ -> raise Ill_typed)
  | Lift { tys; func = t } -> (
      let ty = typesynth env t in
      match ty with
      | Fun signature ->
          Ty.S.fn ~tyvars:signature.tyvars
            (signature.parameters |> List.map (fun bty -> Ty.S.apps tys bty))
            (Ty.S.apps tys signature.return_type)
      | _ -> raise Ill_typed)
  | Ann (tm, ty) ->
      typecheck env ty tm;
      ty

and typesynth_operator env op =
  Operator.iter (typecheck env Ty.S.bool) op;
  Ty.S.bool

let typecheck_function env fn =
  let Prog.{ fn_name; signature; args; body } = fn in
  let env =
    Env.set_function (Format.asprintf "%a" Ident.FnIdent.pp fn_name) env
  in
  let env =
    Env.clear_variables env
    (* XXX: what's [clear_variables]? *)
  in
  let env =
    List.fold_left2
      (fun env variable ty -> Env.add_variable variable ty env)
      env args signature.parameters
  in
  typecheck env signature.return_type body;
  Env.add_function fn env

let add_typedecl = Fun.flip Env.add_type

let of_ua0_node env = function
  | Prog.NFun fn_declaration -> typecheck_function env fn_declaration
  | Prog.NTy type_decl -> add_typedecl env type_decl

let of_ua0_prog env = List.fold_left of_ua0_node env
let of_ua0_prog = of_ua0_prog Env.empty
