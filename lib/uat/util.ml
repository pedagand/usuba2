let err fmt = Format.kasprintf failwith fmt
let log fmt = Format.eprintf fmt

module TermIdent = struct
  let prepend prefix base =
    Ast.TermIdent.(fresh @@ Format.asprintf "%s%a" prefix pp base)
end

module FnIdent = struct
  let prepend prefix base =
    Ast.FnIdent.(fresh @@ Format.asprintf "%s%a" prefix pp base)
end

module Ty = struct
  let rec instanciate types = function
    | Ua0.Ast.TyBool -> Ua0.Ast.TyBool
    | TyFun signature ->
        let signature = instanciate_signature types signature in
        Ua0.Ast.TyFun signature
    | TyApp { name; ty } ->
        let ty = instanciate types ty in
        TyApp { name; ty }
    | TyVar v as t -> (
        match List.assoc_opt v types with None -> t | Some t -> t)

  and instanciate_signature types =
   fun { tyvars; parameters; return_type } ->
    let types =
      match tyvars with None -> types | Some ty -> List.remove_assoc ty types
    in
    let parameters = List.map (instanciate types) parameters in
    let return_type = instanciate types return_type in
    { tyvars; parameters; return_type }

  let rec prefix = function
    | Ua0.Ast.TyApp { name; ty } ->
        let names, elt = prefix ty in
        (name :: names, elt)
    | (TyBool | TyVar _ | TyFun _) as t -> ([], t)

  let lprefix lty = lty.Ua0.Ast.t

  let to_ty lty =
    List.fold_right
      (fun (name, _) ty -> Ua0.Ast.TyApp { name; ty })
      lty.Ua0.Ast.t lty.ty

  let lty t ty = { Ua0.Ast.t; ty }

  let lift' cstrs =
    List.fold_right (fun (name, _) ty -> Ua0.Ast.TyApp { name; ty }) cstrs

  let lift cstrs =
    List.fold_right (fun name ty -> Ua0.Ast.TyApp { name; ty }) cstrs
end

module Lty = struct
  let rec range acc f prefix ty =
    match prefix with
    | [] -> Ty.lty (List.rev acc) ty
    | t :: q ->
        let name, ty =
          match ty with
          | Ua0.Ast.TyApp { name; ty } -> (name, ty)
          | TyBool | TyFun _ | TyVar _ -> err "Not a named tuple."
        in
        let () =
          match Ast.TyDeclIdent.equal name t with
          | true -> ()
          | false ->
              err "range prefix = %a - ty = %a" Ast.TyDeclIdent.pp t
                Ast.TyDeclIdent.pp name
        in
        let size = f name in
        range ((name, size) :: acc) f q ty

  let range prefix = range [] prefix
end

module Term = struct
  let v ty term = (Ast.TVar term, ty)

  let rec as_function_call = function
    | Ast.TFnCall { fn_name; ty_resolve; args } ->
        Some (fn_name, ty_resolve, args)
    | TLog { k = k, _; _ } -> as_function_call k
    | TFalse | TTrue | TVar _ | TFn _ | TLet _ | TLookup _ | TThunk _
    | TOperator _ ->
        None

  let rec as_funk = function
    | Ast.TThunk { lterm } -> Some lterm
    | TLog { k = k, _; _ } -> as_funk k
    | TFalse | TTrue | TVar _ | TFn _ | TLet _ | TLookup _ | TOperator _
    | TFnCall _ ->
        None

  let rec as_variable = function
    | Ast.TVar v -> Some v
    | TLog { k = k, _; _ } -> as_variable k
    | TFalse | TTrue | TFn _ | TLet _ | TLookup _ | TOperator _ | TFnCall _
    | TThunk _ ->
        None

  let funk lterm =
    let _, lty = lterm in
    let ty = Ty.to_ty lty in
    let term = Ast.TThunk { lterm } in
    (term, ty)

  let cstr ctr expr =
    let ctr, arity = ctr in
    let terms = List.init arity (Fun.const expr) in
    Ast.LConstructor { ty = ctr; terms }

  let cstr' ctr expr =
    let _, ty = expr in
    let cstr = cstr ctr expr in
    let ctr, _ = ctr in
    let lty = Ty.lty [] (Ua0.Scstr.Ty.app ctr ty) in
    (cstr, lty)
end

module Lterm = struct
  let as_reindex = function
    | Ast.LReindex { lhs; rhs; lterm } -> Some (lhs, rhs, lterm)
    | LLetPlus _ | LConstructor _ | LRange _ | LCirc _ -> None

  let as_mapn = function
    | Ast.LLetPlus { variable; lterm; ands; term } ->
        Some (variable, lterm, ands, term)
    | LConstructor _ | LRange _ | LReindex _ | LCirc _ -> None

  let as_range = function
    | Ast.LRange { ty; term } -> Some (ty, term)
    | LLetPlus _ | LConstructor _ | LReindex _ | LCirc _ -> None

  let range f tys tterm =
    let _term, ty = tterm in
    let lty = Lty.range f tys ty in
    let range = Ast.LRange { ty = tys; term = tterm } in
    (range, lty)

  let let_plus' variable lterm ands term =
    let lterm = Ast.LLetPlus { variable; lterm; ands; term } in
    let ty = Ty.lty [] (snd term) in
    (lterm, ty)
end

module FunctionDecl = struct
  let signature fn_decl =
    let Ua0.Ast.{ fn_name = _; tyvars; parameters; return_type; body = _ } =
      fn_decl
    in
    let parameters = List.map snd parameters in
    Ua0.Ast.{ tyvars; parameters; return_type }
end

module Eq = struct
  module Env = Map.Make (Ast.TermIdent)

  let ( let* ) o f = match o with true -> f () | false -> false

  let variable env lhs rhs =
    env |> Env.find_opt lhs
    |> Option.map (Ast.TermIdent.equal rhs)
    |> Option.value ~default:false

  let for_all eq lhs rhs =
    let* () = List.compare_lengths lhs rhs = 0 in
    List.for_all2 eq lhs rhs

  let rec term env lhs rhs = term' env (fst lhs) (fst rhs)

  and term' env lhs rhs =
    match (lhs, rhs) with
    | Ast.TFalse, Ast.TFalse | TTrue, TTrue -> true
    | TVar lhs, TVar rhs -> variable env lhs rhs
    | TFn { fn_ident = lhs; _ }, TFn { fn_ident = rhs; _ } ->
        Ast.FnIdent.equal lhs rhs
    | ( TLet { variable = lvariable; term = lterm; k = lk },
        TLet { variable = rvariable; term = rterm; k = rk } ) ->
        let* () = term env lterm rterm in
        let env = Env.add lvariable rvariable env in
        term env lk rk
    | ( TLookup { lterm = llterm; index = lindex },
        TLookup { lterm = rlterm; index = rindex } ) ->
        let* () = lindex = rindex in
        lterm env llterm rlterm
    | TThunk { lterm = llterm }, TThunk { lterm = rterm } ->
        lterm env llterm rterm
    | TLog { k = lk; _ }, TLog { k = rk; _ } -> term env lk rk
    | TOperator lhs, TOperator rhs -> operator env lhs rhs
    | ( TFnCall { fn_name = lfn_name; ty_resolve = lty; args = largs },
        TFnCall { fn_name = rfn_name; ty_resolve = rty; args = rargs } ) ->
        let* () =
          List.compare_lengths (Option.to_list lty) (Option.to_list rty) = 0
        in
        let* () =
          match (lfn_name, rfn_name) with
          | Either.Left lhs, Either.Left rhs -> Ast.FnIdent.equal lhs rhs
          | Either.Right lhs, Right rhs -> variable env lhs rhs
          | _, _ -> false
        in
        for_all (term env) largs rargs
        (* TODO: Check ty_resolve *)
    | _, _ -> false

  and operator env lhs rhs =
    match (lhs, rhs) with
    | Ua0.Ast.ONot lhs, Ua0.Ast.ONot rhs -> term env lhs rhs
    | OAnd (llhs, lrhs), OAnd (rlhs, rrhs)
    | OOr (llhs, lrhs), OOr (rlhs, rrhs)
    | OXor (llhs, lrhs), OXor (rlhs, rrhs) ->
        let* () = term env llhs rlhs in
        term env lrhs rrhs
    | _, _ -> false

  and lterm env lhs rhs = lterm' env (fst lhs) (fst rhs)

  and lterm' env lhs rhs =
    match (lhs, rhs) with
    | ( Ast.LLetPlus
          { variable = lvariable; lterm = llterm; ands = lands; term = l_term },
        Ast.LLetPlus
          { variable = rvariable; lterm = rlterm; ands = rands; term = r_term }
      ) ->
        let* () = lterm env llterm rlterm in
        let* () =
          for_all (fun (_, lhs) (_, rhs) -> lterm env lhs rhs) lands rands
        in
        let env = Env.add lvariable rvariable env in
        let env =
          List.fold_left2
            (fun env (lhs, _) (rhs, _) -> Env.add lhs rhs env)
            env lands rands
        in
        term env l_term r_term
    | ( LConstructor { ty = lty; terms = lterms },
        LConstructor { ty = rty; terms = rterms } ) ->
        Ast.TyDeclIdent.equal lty rty && List.for_all2 (term env) lterms rterms
    | LRange { ty = lty; term = lterm }, LRange { ty = rty; term = rterm } ->
        let* () = for_all Ast.TyDeclIdent.equal lty rty in
        term env lterm rterm
    | ( LReindex { lhs = llhs; rhs = lrhs; lterm = llterm },
        LReindex { lhs = rlhs; rhs = rrhs; lterm = rlterm } ) ->
        let* () = for_all Ast.TyDeclIdent.equal llhs rlhs in
        let* () = for_all Ast.TyDeclIdent.equal lrhs rrhs in
        lterm env llterm rlterm
    | LCirc lhs, LCirc rhs -> lterm env lhs rhs
    | _, _ -> false

  let fn_decl (lhs : Ast.fn_declaration) (rhs : Ast.fn_declaration) =
    let env = Env.empty in
    let* () = List.compare_lengths lhs.parameters rhs.parameters = 0 in
    let env =
      List.fold_left2
        (fun env (lvariable, _) (rvariable, _) ->
          Env.add lvariable rvariable env)
        env lhs.parameters rhs.parameters
    in
    term env lhs.body rhs.body
end
