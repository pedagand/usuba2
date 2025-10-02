(*[@@@warning "-27"]*)

module Pp = Ua0.Pp

let err fmt = Format.kasprintf failwith fmt

module Env = struct
  module Vars = Map.Make (Ast.TermIdent)
  module Fns = Map.Make (Ast.FnIdent)
  module Types = Map.Make (Ast.TyDeclIdent)

  type t = {
    variables : Ast.ty Vars.t;
    functions : Ua0.Ast.fn_declaration Fns.t;
    types : Ua0.Ast.ty_declaration Types.t;
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
          env |> fn_declaration fn_ident |> Ua0.Util.FunctionDecl.signature
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
    | [] -> { Ua0.Ast.t = List.rev acc; ty }
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

exception IllTyped

let take_app _f _ty = failwith "NYI"
let tl _ty = failwith "NYI"

let rec typecheck env ty tm =
  match (ty, tm) with
  | Ua0.Ast.TyBool, Ua0.Ast.False -> ()
  | TyBool, True -> ()
  | TyApp { name; ty }, Constructor { ty = name'; terms } ->
      ignore ty;
      assert (name = name');
      (* XXX: remove `ty` from `LConstructor` *)
      terms |> List.iter (typecheck env ty)
  | ty0, Let { variable; term; k } ->
      let ty = typesynth env term in
      let env = Env.add_variable variable ty env in
      typecheck env ty0 k
  | TyApp { name; ty }, LetPlus { variable; lterm; ands; term } ->
      let ty_var = lterm |> typesynth env |> take_app name in
      let ty_ands =
        List.map
          (fun (var, tm) ->
            let ty = tm |> typesynth env |> take_app name in
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
      if ty != ty0 then raise IllTyped;
      ()
  | _, _ -> failwith "Ill-typed"

and typesynth env = function
  | Var variable -> Env.ty_variable variable env
  | Fn { fn_ident; tyresolve } ->
      let signature =
        Env.signature ~instance:false (Left fn_ident) tyresolve env
      in
      TyFun signature
  | Lookup { lterm; index } ->
      let ty = typesynth env lterm in
      (* XXX: check indexing *)
      ignore index;
      tl ty
      (*
      let ty =
        match Ua0.Util.Ty.(elt @@ to_ty ty) with
        | None -> err "lookup: not a tuple type"
        | Some ty -> ty
      in
      (TLookup { lterm; index }, ty) *)
  | Operator operator -> typesynth_operator env operator
  | FnCall { fn_name; ty_resolve; args } ->
      let signature = Env.signature ~instance:true fn_name ty_resolve env in
      List.iter2
        (fun ty_expected arg -> typecheck env ty_expected arg)
        signature.parameters args;
      signature.return_type
  | Reindex { lhs; rhs; lterm } ->
      let ty = typesynth env lterm in
      let cstrs, ty = Util.Ty.(prefix ty) in
      let cstrs_reindexed = Ua0.Util.Cstrs.reorder lhs rhs cstrs in
      let ty_new =
        List.fold_right
          (fun name ty -> Ua0.Ast.TyApp { name; ty })
          cstrs_reindexed ty
      in
      ty_new
  (*
      let ((_, lty') as lterm) = typecheck_lterm env lterm in
      let cstrs, ty = Util.Ty.(prefix @@ to_ty lty') in
      let cstrs_reindexed = Ua0.Util.Cstrs.reorder lhs rhs cstrs in
      let ty_new =
        List.fold_right
          (fun name ty -> Ua0.Ast.TyApp { name; ty })
          cstrs_reindexed ty
      in
      (LReindex { lhs; rhs; lterm }, Util.Ty.lty [] ty_new) *)
  | Circ term ->
      let ty = typesynth env term in
      let lty = Util.Ty.lty [] ty in
      let wrapper =
        match Ua0.Util.Ty.hd lty with
        | None -> err "Not a tuple type"
        | Some hd -> hd
      in
      Ua0.Ast.TyApp { name = wrapper; ty = Util.Ty.to_ty lty }
  | Ann (tm, ty) ->
      typecheck env ty tm;
      ty

and typesynth_operator env op =
  Ua0.Ast.Operator.iter (typecheck env Ua0.Ast.TyBool) op;
  Ua0.Ast.TyBool

let typecheck_function env fn =
  let Ua0.Ast.{ fn_name; tyvars; parameters; return_type; body } = fn in
  ignore fn_name;
  ignore tyvars;
  let env =
    Env.clear_variables env
    (* XXX: what's [clear_variables]? *)
  in
  let env =
    List.fold_left
      (fun env (variable, ty) -> Env.add_variable variable ty env)
      env parameters
  in
  typecheck env return_type body;
  Env.add_function fn env

let add_typedecl = Fun.flip Env.add_type

let of_ua0_node env = function
  | Ua0.Ast.NFun fn_declaration -> typecheck_function env fn_declaration
  | Ua0.Ast.NTy type_decl -> add_typedecl env type_decl

let of_ua0_prog env = List.fold_left of_ua0_node env
let of_ua0_prog = of_ua0_prog Env.empty
