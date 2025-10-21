(*[@@@warning "-27"]*)

let err fmt = Format.kasprintf failwith fmt

module Env = struct
  module Vars = Map.Make (Ast.TermIdent)
  module Fns = Map.Make (Ast.FnIdent)
  module Types = Map.Make (Ast.TyDeclIdent)

  type t = {
    variables : Ast.scoped Ast.Ty.ty Vars.t;
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

  let add_variables variables env =
    let variables = Vars.add_seq (List.to_seq variables) env.variables in
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
          | Fun signature -> signature
          | ty ->
              err "%a should be a function ty not %a" Ast.TermIdent.pp variable
                Pp.pp_ty ty)
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

  (*
  let rec range acc prefix ty env =
    match prefix with
    | [] -> { Ast.t = List.rev acc; ty }
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
*)

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

  (*
  let reindex ~lhs ~rhs lty =
    let ty = Util.Ty.to_ty lty in
    let to_reindex, ty = Util.Ty.ty_cstrs ty in
    let cstrs = destination to_reindex lhs rhs in
    Util.Ty.lift cstrs ty
*)
end

exception IllTyped

let rec typecheck env ty tm =
  match (ty, tm) with
  | Ast.Ty.Bool, Ast.False -> ()
  | Bool, True -> ()
  | App { name; ty }, Constructor { ty = _name'; terms } ->
      if Env.arity name env <> List.length terms then raise IllTyped;
      terms |> List.iter (typecheck env ty)
  | ty0, Let { variable; term; k } ->
      let ty = typesynth env term in
      let env = Env.add_variable variable ty env in
      typecheck env ty0 k
  | ty0, LetPlus { variable; lterm; ands; term } ->
      let ty_var = lterm |> typesynth env |> Util.Ty.to_spine in
      let ty_ands =
        List.map
          (fun (var, tm) ->
            let ty = tm |> typesynth env |> Util.Ty.to_spine in
            (var, ty))
          ands
      in
      let spine, bty = Util.Ty.to_spine ty0 in
      let spine, btys =
        List.fold_left Util.Ty.merge (spine, [ bty ])
          (ty_var :: List.map snd ty_ands)
      in
      let rec try_spine spine btys =
        match btys with
        | bty0 :: bty_var :: bty_ands -> (
            let env = Env.add_variable variable bty_var env in
            let env =
              Env.add_variables
                (List.combine (List.map fst ty_ands) bty_ands)
                env
            in
            try typecheck env bty0 term
            with IllTyped -> (
              match spine with
              | [] -> raise IllTyped
              | name :: spine ->
                  try_spine spine
                    (List.map (fun ty -> Ast.Ty.App { name; ty }) btys)))
        | _ -> assert false
      in
      try_spine (List.rev spine) btys
  | ty0, Log { message = _; variables = _; k } -> typecheck env ty0 k
  | ty0, Synth t ->
      let ty = typesynth env t in
      if not (Util.Ty.equal ty ty0) then raise IllTyped;
      ()
  | _, _ -> raise IllTyped

and typesynth env = function
  | Var variable -> Env.ty_variable variable env
  | Fn { fn_ident } ->
      let signature = Env.signature ~instance:false (Left fn_ident) None env in
      Fun signature
  | Lookup { lterm; index } -> (
      let ty = typesynth env lterm in
      match ty with
      | App { ty; name } when index < Env.arity name env -> ty
      | _ -> raise IllTyped)
  | Operator operator -> typesynth_operator env operator
  | FnCall { fn_name; ty_resolve; args } ->
      let signature = Env.signature ~instance:true fn_name ty_resolve env in
      List.iter2
        (fun ty_expected arg -> typecheck env ty_expected arg)
        signature.parameters args;
      signature.return_type
  | Reindex { lhs; rhs; lterm } ->
      let ty = typesynth env lterm in
      let ty = Util.Ty.prefix lhs ty |> Option.get in
      let ty = Util.Ty.prefix rhs ty |> Option.get in
      Util.Ty.from_spine (rhs, Util.Ty.from_spine (lhs, ty))
  | Circ t -> (
      let ty = typesynth env t in
      match ty with
      | App { name; ty } -> App { name; ty = App { name; ty } }
      | _ -> raise IllTyped)
  | Lift { tys; func = t } -> (
      let ty = typesynth env t in
      match ty with
      | Fun signature ->
          Fun
            {
              signature with
              parameters =
                signature.parameters
                |> List.map (fun bty -> Util.Ty.from_spine (tys, bty));
              return_type = Util.Ty.from_spine (tys, signature.return_type);
            }
      | _ -> raise IllTyped)
  | Ann (tm, ty) ->
      typecheck env ty tm;
      ty

and typesynth_operator env op =
  Operator.iter (typecheck env Ast.Ty.Bool) op;
  Ast.Ty.Bool

let typecheck_function env fn =
  let Ast.{ fn_name; signature; args; body } = fn in
  ignore fn_name;
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
  | Ast.NFun fn_declaration -> typecheck_function env fn_declaration
  | Ast.NTy type_decl -> add_typedecl env type_decl

let of_ua0_prog env = List.fold_left of_ua0_node env
let of_ua0_prog = of_ua0_prog Env.empty
