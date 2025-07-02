open Ast

module Ty = struct
  let bool = TyBool
  let v v = TyVar v
  let app name ty = TyApp { name; ty }

  let fn tyvars parameters return_type =
    TyFun { tyvars; parameters; return_type }
end

module LTerm = struct
  let range ty term = LRange { ty; term }
  let cstr ty terms = LConstructor { ty; terms }
  let circ term = LCirc term

  let let_plus variable lterm ands k =
    let variable = TermIdent.fresh variable in
    let ands =
      List.map
        (fun (v, term) ->
          let v = TermIdent.fresh v in
          (v, term))
        ands
    in
    let vand = List.map fst ands in
    let term = k variable vand in
    LLetPlus { variable; lterm; ands; term }
end

module Term = struct
  let true' = TTrue
  let false' = TFalse
  let v variable = TVar variable
  let vfn tyresolve fn_ident = TFn { fn_ident; tyresolve }

  let log message variables k =
    let k = k () in
    TLog { message; variables; k }

  let log_ message variables k = TLog { message; variables; k }

  (* haha *)
  let funk lterm = TThunk { lterm }
  let lookup lterm index = TLookup { lterm; index }
  let ( .%() ) = lookup
  let let_ variable term k = TLet { variable; term; k }

  let let' variable term k =
    let variable = TermIdent.fresh variable in
    TLet { variable; term; k = k variable }

  let fn_call fn_name ty_resolve args =
    TFnCall { fn_name = Left fn_name; ty_resolve; args }

  let v_call variable_name ty_resolve args =
    TFnCall { fn_name = Right variable_name; ty_resolve; args }

  let ( lxor ) lhs rhs = TOperator (OXor (lhs, rhs))
  let ( land ) lhs rhs = TOperator (OAnd (lhs, rhs))
  let ( lor ) lhs rhs = TOperator (OOr (lhs, rhs))
  let lnot term = TOperator (ONot term)
end
