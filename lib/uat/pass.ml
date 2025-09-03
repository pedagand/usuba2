(*
F.map subcells['a] = reindex[F, S] o subcells[F 'a] o reindex[S, F]   

F.map (G.map f) = reindex[F, G] o G.map(F.map f)

F.map (reindex[G, H]) o reindex[F, H] = reindex[FG, H]

reindex[F, G] o G.map (reindex[F, H])

*)

let uncons list = match list with [] -> (None, []) | t :: q -> (Some t, q)

module Idents = Set.Make (Ast.TermIdent)
module MIdents = Map.Make (Ast.TermIdent)
module ReindexWrap = ReindexWrap

module InlineLet = struct
  module Env = struct
    type t = Ast.(term tys) MIdents.t

    let empty : t = MIdents.empty
    let add v t env : t = MIdents.add v t env
    let find v env : Ast.(term tys) = MIdents.find v env
  end

  let rec inline_term env = function
    | Ast.TVar variable -> fst @@ Env.find variable env
    | (Ast.TFalse | TTrue) as e -> e
    | _ -> failwith ""

  and inline_term' env term =
    let term, ty = term in
    let term = inline_term env term in
    (term, ty)

  let inline_function function_decl =
    let Ast.{ parameters; body; return_type = _; fn_name = _; tyvars = _ } =
      function_decl
    in
    let env =
      List.fold_left
        (fun env (variable, ty) ->
          let term = Scstr.Term.v variable in
          let term = (term, ty) in
          Env.add variable term env)
        Env.empty parameters
    in
    let body = inline_term' env body in
    { function_decl with body }
end

module CancelReindex = struct
  module Env = struct
    type t = {
      to_reindex : Ast.TyDeclIdent.t list;
      re_lindex : Ast.TyDeclIdent.t list;
      re_rindex : Ast.TyDeclIdent.t list;
      variables : Idents.t;
    }

    let init to_reindex re_lindex re_rindex variables =
      { to_reindex; re_rindex; re_lindex; variables = Idents.of_list variables }

    let mem variable env = Idents.mem variable env.variables

    let same_reindex lhs rhs env =
      let ( === ) = List.equal Ast.TyDeclIdent.equal in
      (lhs === env.re_lindex && rhs === env.re_rindex)
      || (lhs === env.re_rindex && rhs === env.re_lindex)
  end

  let is_parameter_reindexed env tlterm =
    let ( let* ) = Option.bind in
    let lterm, _ = tlterm in
    let* lreindex_out, rreindex_out, lterm = Util.Lterm.as_reindex lterm in
    let* () =
      match Env.same_reindex lreindex_out rreindex_out env with
      | true -> Some ()
      | false -> None
    in
    let* _, tterm = Util.Lterm.as_range (fst lterm) in
    let* variable = Util.Term.as_variable (fst tterm) in
    let is_parameter = Env.mem variable env in
    match is_parameter with true -> Some lterm | false -> None

  let cancel_reindex env tlterm =
    let ( let* ) = Option.bind in
    let lterm, _ = tlterm in
    let* lreindex_out, rreindex_out, (lterm_map, _tylterm_map) =
      Util.Lterm.as_reindex lterm
    in
    let* () =
      match Env.same_reindex lreindex_out rreindex_out env with
      | true -> Some ()
      | false -> None
    in
    let* variable, lterm, ands, _term = Util.Lterm.as_mapn lterm_map in
    let lterms = (variable, lterm) :: ands in
    let lterms =
      List.map
        (fun (_, tlterm) ->
          match is_parameter_reindexed env tlterm with
          | None -> lterm
          | Some t -> t)
        lterms
    in
    let (_variable, _lterm), _ands =
      match lterms with x :: xs -> (x, xs) | [] -> assert false
    in
    failwith ""
end

module InsertReindex = struct
  module Env = struct
    type t = {
      to_reindex : Ast.TyDeclIdent.t list;
      re_lindex : Ast.TyDeclIdent.t list;
      re_rindex : Ast.TyDeclIdent.t list;
      casts : Idents.t;
    }

    let init to_reindex re_lindex re_rindex casts =
      { to_reindex; re_lindex; re_rindex; casts }

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

    let destination env =
      let { to_reindex; re_lindex; re_rindex; casts = _ } = env in
      destination to_reindex re_lindex re_rindex

    let arity : Ast.TyDeclIdent.t -> t -> int = failwith ""

    let should_wrap ty env =
      let prefix, _ = Util.Ty.prefix ty in
      List.equal Ast.TyDeclIdent.equal env.to_reindex prefix

    let should_reindex term env = Idents.mem term env.casts

    let retype ty env =
      let _, elt = Util.Ty.prefix ty in
      let () = assert (should_wrap ty env) in
      let new_prefix = destination env in
      List.fold_right (fun name ty -> Ua0.Ast.TyApp { name; ty }) new_prefix elt

    let reindex tlterm env =
      let _lterm, lty' = tlterm in
      let prefix, ty = Util.Ty.(prefix @@ to_ty lty') in
      let lterm =
        Ast.LReindex
          { lterm = tlterm; lhs = env.re_lindex; rhs = env.re_rindex }
      in
      let dst = destination { env with to_reindex = prefix } in
      let lty = Util.Ty.(lty [] @@ lift dst ty) in
      (lterm, lty)

    let reindex_param term ty' env =
      let nty = Util.Ty.lty [] ty' in
      let rty = retype ty' env in
      let lrty = Util.Ty.lty [] rty in
      let open Scstr in
      LTerm.(
        Term.(
          funk
            (ty nty
            @@ reindex env.re_lindex env.re_lindex
                 (ty lrty @@ range [] @@ ty rty @@ v term))))
  end

  let term_cstr' ctr expr =
    let ((_, lty) as t) = Util.Term.cstr' ctr expr in
    let term = Ast.TThunk { lterm = t } in
    let ty = Util.Ty.to_ty lty in
    (term, ty)

  let lift inlines cstrs expr =
    match fst expr with
    | Ast.TVar variable -> (
        match MIdents.find_opt variable inlines with
        | None -> expr
        | Some e -> Util.Term.funk e)
    | _ -> List.fold_right term_cstr' cstrs expr

  let wrap_lreindex env lterm =
    let lterm, _lty = lterm in
    let ( let* ) = Option.bind in
    let* variable, ((_, ty_lterm) as ltty), ands, tterm =
      match lterm with
      | Ast.LLetPlus { variable; lterm; ands; term } ->
          Some (variable, lterm, ands, term)
      | LConstructor _ | LRange _ | LReindex _ | LCirc _ -> None
    in
    let* fn_name, ty_resolve, args = Util.Term.as_function_call (fst tterm) in
    let cstrs = Util.Ty.lprefix ty_lterm in
    let letargs = (variable, ltty) :: ands in
    let inlines =
      let letargs =
        List.map
          (fun (variable, tlterm) ->
            let tlerm = Env.reindex tlterm env in
            (variable, tlerm))
          letargs
      in
      MIdents.of_seq @@ List.to_seq letargs
    in
    let args = List.map (lift inlines cstrs) args in
    let ty_resolve = Option.map (Util.Ty.lift' cstrs) ty_resolve in
    let term = Ast.TFnCall { fn_name; ty_resolve; args } in
    let tterm = (term, snd tterm) in
    let tterm =
      Util.(
        Lterm.(
          Term.(
            funk (Env.reindex (range (Fun.flip Env.arity env) [] tterm) env))))
    in
    Some tterm

  let wrap_reindex env tterm =
    let term, _ty = tterm in
    let ( >>= ) = Option.bind in
    term |> Util.Term.as_funk >>= wrap_lreindex env

  let wrap f env fun_decl =
    let Ast.{ fn_name; tyvars; parameters; return_type; body } = fun_decl in
    let fn_name = Util.FnIdent.prepend "w" fn_name in
    let body = match f env body with None -> body | Some body -> body in
    let body, parameters =
      List.fold_left_map
        (fun body (para, ty) ->
          let npara = Util.TermIdent.prepend "w" para in
          let body =
            match Env.should_reindex para env with
            | true ->
                let term = Env.reindex_param npara ty env in
                ( Ast.TLet { variable = para; term = (term, ty); k = body },
                  snd body )
            | false -> body
          in
          (body, (npara, ty)))
        body parameters
    in
    let body =
      Util.(
        Lterm.(
          Term.(funk (Env.reindex (range (Fun.flip Env.arity env) [] body) env))))
    in
    let nreturn_type = Env.retype return_type env in
    Ast.{ fn_name; tyvars; parameters; return_type = nreturn_type; body }
end

module ReSimplify = struct
  module Env = struct
    type t = Ast.(term tys) MIdents.t

    let empty = MIdents.empty
    let add = MIdents.add
    let find = MIdents.find
  end

  let prefix_eq lhs rhs lhs' rhs' =
    let ( = ) = List.equal Ast.TyDeclIdent.equal in
    (lhs = lhs' && rhs = rhs') || (lhs = rhs' && rhs = lhs')

  let rec simplify_reindex ty' slhs srhs env = function
    | Ast.LReindex { lhs; rhs; lterm } -> (
        match prefix_eq lhs rhs slhs srhs with
        | true -> Some lterm
        | false -> None)
    | Ast.LRange { ty; term } ->
        Option.map
          (fun term -> (Ast.LRange { ty; term }, ty'))
          (simplify_reindex_term' slhs srhs env term)
    | Ast.LLetPlus _ | LConstructor _ | LCirc _ -> None

  and simplify_reindex' slhs srhs env lterm =
    let lterm, ty = lterm in
    match simplify_reindex ty slhs srhs env lterm with
    | None -> None
    | Some lterm -> Some lterm

  and simplify_reindex_term ty slhs srhs env = function
    | Ast.TVar variable ->
        simplify_reindex_term' slhs srhs env (Env.find variable env)
    | Ast.TThunk { lterm } ->
        Option.map
          (fun lterm -> (Ast.TThunk { lterm }, ty))
          (simplify_reindex' slhs srhs env lterm)
    | TFalse | TTrue | TFn _ | TLet _ | TLookup _ | TLog _ | TOperator _
    | TFnCall _ ->
        None

  and simplify_reindex_term' slhs srhs env term =
    let term, ty = term in
    match simplify_reindex_term ty slhs srhs env term with
    | None -> None
    | Some term -> Some term

  let rec simplify_term env = function
    | Ast.TVar variable -> fst @@ Env.find variable env
    | TLet { variable; term; k } ->
        let term = simplify_term' env term in
        let env = Env.add variable term env in
        fst @@ simplify_term' env k
    | TLookup { lterm; index } ->
        let lterm = simplify_lterm' env lterm in
        Ast.TLookup { lterm; index }
    | TThunk { lterm } ->
        let lterm = simplify_lterm' env lterm in
        TThunk { lterm }
    | TLog { message; variables; k } ->
        let k = simplify_term' env k in
        Ast.TLog { message; variables; k }
    | TOperator operator ->
        let operator = simplify_operator env operator in
        TOperator operator
    | TFnCall { fn_name; ty_resolve; args } ->
        let args = List.map (simplify_term' env) args in
        TFnCall { fn_name; ty_resolve; args }
    | (TFn _ | TFalse | TTrue) as e -> e

  and simplify_term' env term =
    let term, ty = term in
    let term = simplify_term env term in
    (term, ty)

  and simplify_operator env = function
    | Ua0.Ast.ONot term ->
        let term = simplify_term' env term in
        Ua0.Ast.ONot term
    | OXor (lhs, rhs) ->
        let lhs = simplify_term' env lhs in
        let rhs = simplify_term' env rhs in
        OXor (lhs, rhs)
    | OAnd (lhs, rhs) ->
        let lhs = simplify_term' env lhs in
        let rhs = simplify_term' env rhs in
        OAnd (lhs, rhs)
    | OOr (lhs, rhs) ->
        let lhs = simplify_term' env lhs in
        let rhs = simplify_term' env rhs in
        OOr (lhs, rhs)

  and simplify_lterm env = function
    | Ast.LReindex { lhs; rhs; lterm } -> (
        match simplify_reindex' lhs rhs env lterm with
        | Some lterm -> fst @@ simplify_lterm' env lterm
        | None ->
            let lterm = simplify_lterm' env lterm in
            Ast.LReindex { lhs; rhs; lterm })
    | Ast.LLetPlus { variable; lterm; ands; term } ->
        let lterm = simplify_lterm' env lterm in
        let ands =
          List.map
            (fun (variable, lterm) ->
              let lterm = simplify_lterm' env lterm in
              (variable, lterm))
            ands
        in
        let term = simplify_term' env term in
        Ast.LLetPlus { variable; lterm; ands; term }
    | LConstructor { ty; terms } ->
        let terms = List.map (simplify_term' env) terms in
        LConstructor { ty; terms }
    | LRange { ty; term } ->
        let term = simplify_term' env term in
        LRange { ty; term }
    | LCirc lterm ->
        let lterm = simplify_lterm' env lterm in
        LCirc lterm

  and simplify_lterm' env lterm =
    let lterm, ty = lterm in
    let lterm = simplify_lterm env lterm in
    (lterm, ty)
end

module Dup = struct
  let dup arity cs function_decl =
    let promote ty = Ua0.Ast.TyApp { name = cs; ty } in
    let Ast.{ fn_name; tyvars; parameters; return_type; body } =
      function_decl
    in
    let fn_name = Util.FnIdent.prepend "dup" fn_name in
    let new_parameters =
      List.map
        (fun (variable, ty) ->
          let variable = Util.TermIdent.prepend "dup" variable in
          let ty = promote ty in
          (variable, ty))
        parameters
    in
    let new_return_type = promote return_type in
    let lands =
      List.map2
        (fun (new_variable, new_ty) (variable, _ty) ->
          let lterm =
            Util.(Lterm.(Term.(range arity [ cs ] (v new_ty new_variable))))
          in
          (variable, lterm))
        new_parameters parameters
    in
    let body =
      match lands with
      | [] ->
          let arity = arity cs in
          Util.Term.cstr' (cs, arity) body
      | (variable, lterm) :: ands ->
          Util.Lterm.let_plus' variable lterm ands body
    in
    let body = Util.Term.funk body in
    Ast.
      {
        fn_name;
        tyvars;
        parameters = new_parameters;
        return_type = new_return_type;
        body;
      }
end
