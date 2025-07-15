(*
F.map subcells['a] = reindex[F, S] o subcells[F 'a] o reindex[S, F]   

F.map (G.map f) = reindex[F, G] o G.map(F.map f)

F.map (reindex[G, H]) o reindex[F, H] = reindex[FG, H]

reindex[F, G] o G.map (reindex[F, H])

*)

module B = struct
  module Idents = Set.Make (Ast.TermIdent)

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

    let should_wrap ty env =
      let prefix, _ = Util.Ty.prefix ty in
      List.equal Ast.TyDeclIdent.equal env.to_reindex prefix

    let should_reindex term env = Idents.mem term env.casts

    let retype ty env =
      let _, elt = Util.Ty.prefix ty in
      let () = assert (should_wrap ty env) in
      let new_prefix = destination env in
      List.fold_right (fun name ty -> Ast.TyApp { name; ty }) new_prefix elt

    let reindex term env =
      let open Scstr in
      LTerm.(Term.(funk (reindex env.re_lindex env.re_lindex (range [] term))))
  end

  let wrap env fun_decl =
    let Ast.{ fn_name; tyvars; parameters; return_type; body } = fun_decl in
    let fn_name = Util.FnIdent.prepend "w" fn_name in
    let body, parameters =
      List.fold_left_map
        (fun body (para, ty) ->
          let open Scstr in
          let npara = Util.TermIdent.prepend "w" para in
          let ty = Env.retype ty env in
          let reindexes =
            match Env.should_reindex para env with
            | true ->
                let term = Env.reindex Term.(v npara) env in
                Ast.TLet { variable = para; term; k = body }
            | false -> body
          in
          (reindexes, (npara, ty)))
        body parameters
    in
    let return_type = Env.retype return_type env in
    let body =
      let open Scstr in
      Term.(let' "tmp" body @@ fun tmp -> Env.reindex (v tmp) env)
    in
    Ast.{ fn_name; tyvars; parameters; return_type; body }
end
