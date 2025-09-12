let rec lu_term = function
  | Ast.TLet { variable; term; k } ->
      let lets, term = lu_term' term in
      let lets', k = lu_term' k in
      let lets = lets @ ((variable, term) :: lets') in
      (lets, fst k)
  | TLookup { lterm; index } ->
      let lets, lterm = lu_lterm' lterm in
      (lets, Ast.TLookup { lterm; index })
  | TThunk { lterm } ->
      let lets, lterm = lu_lterm' lterm in
      (lets, Ast.TThunk { lterm })
  | TLog { message; variables; k } ->
      let lets, k = lu_term' k in
      (lets, TLog { message; variables; k })
  | TOperator e ->
      let lets, e = lu_operator e in
      (lets, TOperator e)
  | TFnCall { fn_name; ty_resolve; args } ->
      let lets', args =
        List.fold_left_map
          (fun lets arg ->
            let lets', arg = lu_term' arg in
            let lets = lets' @ lets in
            (lets, arg))
          [] args
      in
      (lets', Ast.TFnCall { fn_name; ty_resolve; args })
  | (TFalse | TTrue | TVar _ | TFn _) as e -> ([], e)

and lu_operator = function
  | Ua0.Ast.ONot term ->
      let lets, term = lu_term' term in
      (lets, Ua0.Ast.ONot term)
  | OXor (lhs, rhs) ->
      let lets, lhs = lu_term' lhs in
      let lets', rhs = lu_term' rhs in
      (lets @ lets', OXor (lhs, rhs))
  | OAnd (lhs, rhs) ->
      let lets, lhs = lu_term' lhs in
      let lets', rhs = lu_term' rhs in
      (lets @ lets', OAnd (lhs, rhs))
  | OOr (lhs, rhs) ->
      let lets, lhs = lu_term' lhs in
      let lets', rhs = lu_term' rhs in
      (lets @ lets', OOr (lhs, rhs))

and lu_term' (term, ty) =
  let lets, term = lu_term term in
  (lets, (term, ty))

and lu_lterm = function
  | Ast.LLetPlus { variable; lterm; ands; term } ->
      let lets, lterm = lu_lterm' lterm in
      let lets, ands =
        List.fold_left_map
          (fun lets (variable, lterm) ->
            let lets', lterm = lu_lterm' lterm in
            let lets = lets' @ lets in
            (lets, (variable, lterm)))
          lets ands
      in
      let term_lets, term = lu_term' term in
      let term = lu_decls term_lets term in
      (lets, Ast.LLetPlus { variable; lterm; ands; term })
  | LConstructor { ty; terms } ->
      let lets', terms =
        List.fold_left_map
          (fun lets term ->
            let lets', term = lu_term' term in
            let lets = lets' @ lets in
            (lets, term))
          [] terms
      in
      (lets', Ast.LConstructor { ty; terms })
  | LRange { ty; term } ->
      let lets, term = lu_term' term in
      (lets, LRange { ty; term })
  | LReindex { lhs; rhs; lterm } ->
      let lets, lterm = lu_lterm' lterm in
      (lets, LReindex { lhs; rhs; lterm })
  | LCirc lterm ->
      let lets, lterm = lu_lterm' lterm in
      (lets, Ast.LCirc lterm)

and lu_lterm' (lterm, lty) =
  let lets, term = lu_lterm lterm in
  (lets, (term, lty))

and lu_decls lets k =
  List.fold_right
    (fun (variable, term) k -> (Ast.TLet { variable; term; k }, snd k))
    lets k

let lu_function fn =
  let Ast.{ fn_name; body; _ } = fn in
  let fn_name = Util.FnIdent.prepend "lu_" fn_name in
  let lets, body = lu_term' body in
  let body = lu_decls lets body in
  { fn with fn_name; body }
