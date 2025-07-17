(*
F.map subcells['a] = reindex[F, S] o subcells[F 'a] o reindex[S, F]   

F.map (G.map f) = reindex[F, G] o G.map(F.map f)

F.map (reindex[G, H]) o reindex[F, H] = reindex[FG, H]

reindex[F, G] o G.map (reindex[F, H])

*)

module B = struct
  module Idents = Set.Make (Ast.TermIdent)
  module MIdents = Map.Make (Ast.TermIdent)

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
                 (ty lrty @@ range [] @@ ty rty @@ v rty term))))
  end

  let cstr ctr expr =
    let ctr, arity = ctr in
    let terms = List.init arity (Fun.const expr) in
    Ast.LConstructor { ty = ctr; terms }

  let cstr' ctr expr =
    let _, ty = expr in
    let cstr = cstr ctr expr in
    let ctr, _ = ctr in
    let lty = Util.Ty.lty [] (Ua0.Scstr.Ty.app ctr ty) in
    (cstr, lty)

  let term_cstr' ctr expr =
    let ((_, lty) as t) = cstr' ctr expr in
    let term = Ast.TThunk { lterm = t } in
    let ty = Util.Ty.to_ty lty in
    (term, ty)

  let lift inlines cstrs expr =
    match fst expr with
    | Ast.TVar (variable, _) -> (
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
    let ty_resolve = List.map (Util.Ty.lift' cstrs) ty_resolve in
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

  let wrap env fun_decl =
    let Ast.{ fn_name; tyvars; parameters; return_type; body } = fun_decl in
    match wrap_reindex env body with
    | None -> fun_decl
    | Some body ->
        let fn_name = Util.FnIdent.prepend "w" fn_name in
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
        let nreturn_type = Env.retype return_type env in
        let body =
          Util.(
            Lterm.(
              Term.(
                funk (Env.reindex (range (Fun.flip Env.arity env) [] body) env))))
        in
        Ast.{ fn_name; tyvars; parameters; return_type = nreturn_type; body }
end
