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

let rec prefix lhs ty =
  match (lhs, ty) with
  | [], ty -> ty
  | decl :: lhs, Ast.Ty.App { name; ty } when Ast.TyDeclIdent.equal decl name ->
      prefix lhs ty
  | _, _ -> raise IllTyped

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
  | App { name; ty }, LetPlus { variable; lterm; ands; term } ->
      let ty_var = lterm |> typesynth env |> prefix [ name ] in
      let ty_ands =
        List.map
          (fun (var, tm) ->
            let ty = tm |> typesynth env |> prefix [ name ] in
            (var, ty))
          ands
      in
      let env =
        Env.set_variables ty_ands (Env.add_variable variable ty_var env)
      in
      typecheck env ty term
  | ty0, Log { message = _; variables = _; k } -> typecheck env ty0 k
  | ty0, Synth t ->
      let ty = typesynth env t in
      if not (Util.Ty.equal ty ty0) then raise IllTyped;
      ()
  | _, _ -> failwith "Ill-typed"

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
      let flatten = List.fold_right (fun name ty -> Ast.Ty.App { name; ty }) in
      let ty = typesynth env lterm in
      let ty = prefix lhs ty in
      let ty = prefix rhs ty in
      flatten rhs (flatten lhs ty)
  | Circ t -> (
      let ty = typesynth env t in
      match ty with
      | App { name; ty } -> App { name; ty = App { name; ty } }
      | _ -> raise IllTyped)
  | Ann (tm, ty) ->
      typecheck env ty tm;
      ty

and typesynth_operator env op =
  Ast.Operator.iter (typecheck env Ast.Ty.Bool) op;
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
