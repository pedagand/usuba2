(** [ReindexWrap] aims to create a new function with the parameters already
    bitsliced by calling the specification version. *)
let ty_reindex lcstrs rcstrs ty =
  let cstrs, ty = Util.Ty.prefix ty in
  let cstrs_reindexed = Ua0.Util.Cstrs.reorder lcstrs rcstrs cstrs in
  List.fold_right (fun name ty -> Ua0.Ast.TyApp { name; ty }) cstrs_reindexed ty

let wr_function lcstrs rcstrs fn =
  let Ast.{ fn_name; tyvars; parameters; return_type; body } = fn in
  let fn_name = Util.FnIdent.prepend "wr_" fn_name in
  let body, parameters =
    List.fold_left_map
      (fun body ((variable, ty) as vt) ->
        let cstrs, ty = Util.Ty.prefix ty in
        let cstrs_reindexed = Ua0.Util.Cstrs.reorder lcstrs rcstrs cstrs in
        let keep_term_ident =
          let cmp = List.compare_length_with cstrs 1 in
          cmp <= 0 || List.equal Ast.TyDeclIdent.equal cstrs cstrs_reindexed
        in
        match keep_term_ident with
        | true -> (body, vt)
        | false ->
            let ty_new =
              List.fold_right
                (fun name ty -> Ua0.Ast.TyApp { name; ty })
                cstrs_reindexed ty
            in
            let variable_new = Util.TermIdent.prepend String.empty variable in
            let body =
              Scstr.
                (Term.(let_ variable (v variable_new, ty_new) body), snd body)
            in
            (body, (variable_new, ty_new)))
      body parameters
  in
  let return_type = (* Rev order *) ty_reindex rcstrs lcstrs return_type in
  Ast.{ fn_name; tyvars; parameters; return_type; body }
