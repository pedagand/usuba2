module Term = struct
  open Term

  let s sterm = Synth sterm
  let ann tm ty = Ann (tm, ty)
  let true' = True
  let false' = False
  let v variable = Var variable
  let vfn fn_ident = Fn { fn_ident }

  let log message variables k =
    let k = k () in
    Log { message; variables; k }

  let log_ message variables k = Log { message; variables; k }
  let lookup lterm index = Lookup { lterm; index }
  let ( .%() ) = lookup
  let let_ variable term k = Let { variable; term; k }

  let let' variable term k =
    let variable = Ident.TermIdent.fresh variable in
    Let { variable; term; k = k (v variable) }

  let fn_call ?resolve fn_name args =
    FnCall { fn_name = Left fn_name; ty_resolve = resolve; args }

  let v_call ?resolve variable_name args =
    FnCall { fn_name = Right variable_name; ty_resolve = resolve; args }

  let circ t = Circ t
  let lift tys func = Lift { tys; func }

  let reindex lhs rhs lterm =
    assert (lhs <> []);
    assert (rhs <> []);
    Reindex { lhs; rhs; lterm }

  let ( lxor ) lhs rhs = Operator (Xor (lhs, rhs))
  let ( land ) lhs rhs = Operator (And (lhs, rhs))
  let ( lor ) lhs rhs = Operator (Or (lhs, rhs))
  let lnot term = Operator (Not term)
  let cstr ty terms = Constructor { ty; terms }

  let let_plus variable lterm ands k =
    let variable = Ident.TermIdent.fresh variable in
    let ands =
      List.map
        (fun (v, term) ->
          let v = Ident.TermIdent.fresh v in
          (v, term))
        ands
    in
    let vand = List.map fst ands in
    let term = k variable vand in
    LetPlus { variable; lterm; ands; term }
end
