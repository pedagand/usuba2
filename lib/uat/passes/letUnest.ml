let rec lu_term = function
  | Ast.TLet { variable; term; k } -> 
    let _, term = lu_term' term in 
  failwith ""
  | (TFalse | TTrue | TVar _ | TFn _) as e -> [], e 
  | TLookup _ -> failwith ""
  | TThunk { lterm } -> failwith ""
  | TLog { message; variables; k } -> failwith ""
  | TOperator e -> failwith ""
  | TFnCall { fn_name; ty_resolve; args } -> failwith ""

and lu_term' _term = failwith ""

and lu_lterm = function
  | Ast.LLetPlus { variable; lterm; ands; term } -> failwith ""
  | LConstructor { ty; terms } -> failwith ""
  | LRange { ty; term } -> failwith ""
  | LReindex { lhs; rhs; lterm } -> failwith ""
  | LCirc term -> failwith ""

and lu_lterm' _lterm = failwith ""

let lu_function fn =
  let Ast.{ fn_name; body; _ } = fn in
  let fn_name = Util.FnIdent.prepend "lu_" fn_name in
  let body = lu_term' body in
  { fn with fn_name; body }
