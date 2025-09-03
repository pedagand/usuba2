(** [ReindexWrap] aims to create a new function with the parameters already
    bitsliced by calling the specification version. *)

let ty_reindex lcstrs rcstrs ty =
  let cstrs, ty = Util.Ty.prefix ty in
  let cstrs_reindexed = Ua0.Util.Cstrs.reorder lcstrs rcstrs cstrs in
  List.fold_right (fun name ty -> Ua0.Ast.TyApp { name; ty }) cstrs_reindexed ty

let reindex_term ty ty_new lcstrs rcstrs term =
  let lty = Util.Ty.lty [] ty in
  let lty_new = Util.Ty.lty [] ty_new in
  Ast.TThunk
    {
      lterm =
        ( Ast.LReindex
            {
              lhs = lcstrs;
              rhs = rcstrs;
              lterm = (Ast.LRange { ty = []; term = (term, ty) }, lty);
            },
          lty_new );
    }

let reindex_type lcstrs rcstrs ty =
  let cstrs, ty = Util.Ty.prefix ty in
  let cstrs_reindexed = Ua0.Util.Cstrs.reorder rcstrs lcstrs cstrs in
  let keep_term_ident =
    let cmp = List.compare_length_with cstrs 1 in
    (* Check if List.length <= 1*)
    cmp <= 0 || List.equal Ast.TyDeclIdent.equal cstrs cstrs_reindexed
  in
  match keep_term_ident with
  | false ->
      let ty_new =
        List.fold_right
          (fun name ty -> Ua0.Ast.TyApp { name; ty })
          cstrs_reindexed ty
      in
      Some ty_new
  | true -> None

let wr_function lcstrs rcstrs fn =
  let Ast.{ fn_name; tyvars; parameters; return_type; body } = fn in
  let fn_name = Util.FnIdent.prepend "wr_" fn_name in
  let body, return_type =
    match reindex_type lcstrs rcstrs return_type with
    | None -> (body, return_type)
    | Some new_return_type ->
        let term =
          reindex_term return_type new_return_type rcstrs lcstrs (fst body)
        in
        ((term, new_return_type), new_return_type)
  in
  let body, parameters =
    List.fold_left_map
      (fun body ((variable, ty) as vt) ->
        match reindex_type lcstrs rcstrs ty with
        | None -> (body, vt)
        | Some ty_new ->
            let variable_new = Util.TermIdent.prepend String.empty variable in
            let reindex =
              reindex_term ty ty_new lcstrs rcstrs (TVar variable)
            in
            let body =
              Scstr.(Term.(let_ variable (reindex, ty_new) body, snd body))
            in
            (body, (variable_new, ty_new)))
      body parameters
  in
  let return_type = ty_reindex rcstrs lcstrs return_type in
  Ast.{ fn_name; tyvars; parameters; return_type; body }
