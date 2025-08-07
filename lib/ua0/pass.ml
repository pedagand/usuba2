(* make boolean operations as passed explicilty as function arguments *)
module ExplicitBoolFun = struct
  module BoolOperator = struct
    type t = BNot | BXor | BAnd | BOr

    let compare = Stdlib.compare
    let equal = Stdlib.( = )
  end

  let rec ebf_term booleans = function
    | Ast.TOperator operator -> ebf_operator booleans operator
    | TLet { variable; term; k } ->
        let term = ebf_term booleans term in
        let k = ebf_term booleans k in
        Ast.TLet { variable; term; k }
    | TLookup { lterm; index } ->
        let lterm = ebf_lterm booleans lterm in
        TLookup { lterm; index }
    | TLog { message; variables; k } ->
        let k = ebf_term booleans k in
        TLog { message; variables; k }
    | TFnCall { fn_name; ty_resolve; args } ->
        let args = List.map (ebf_term booleans) args in
        TFnCall { fn_name; ty_resolve; args }
    | TThunk { lterm } ->
        let lterm = ebf_lterm booleans lterm in
        TThunk { lterm }
    | (TFalse | TTrue | TVar _ | TFn _) as e -> e

  and ebf_operator booleans = function
    | Ast.ONot term ->
        let term = ebf_term booleans term in
        let term_name = List.assoc BoolOperator.BNot booleans in
        Ast.TFnCall
          { fn_name = Left term_name; ty_resolve = []; args = [ term ] }
    | Ast.OXor (lhs, rhs) ->
        let lhs = ebf_term booleans lhs in
        let rhs = ebf_term booleans rhs in
        let term_name = List.assoc BoolOperator.BXor booleans in
        TFnCall
          { fn_name = Left term_name; ty_resolve = []; args = [ lhs; rhs ] }
    | Ast.OAnd (lhs, rhs) ->
        let lhs = ebf_term booleans lhs in
        let rhs = ebf_term booleans rhs in
        let term_name = List.assoc BoolOperator.BAnd booleans in
        TFnCall
          { fn_name = Left term_name; ty_resolve = []; args = [ lhs; rhs ] }
    | Ast.OOr (lhs, rhs) ->
        let lhs = ebf_term booleans lhs in
        let rhs = ebf_term booleans rhs in
        let term_name = List.assoc BoolOperator.BOr booleans in
        TFnCall
          { fn_name = Left term_name; ty_resolve = []; args = [ lhs; rhs ] }

  and ebf_lterm booleans = function
    | Ast.LLetPlus { variable; lterm; ands; term } ->
        let lterm = ebf_lterm booleans lterm in
        let ands =
          List.map
            (fun (variable, lterm) ->
              let lterm = ebf_lterm booleans lterm in
              (variable, lterm))
            ands
        in
        let term = ebf_term booleans term in
        Ast.LLetPlus { variable; lterm; ands; term }
    | LConstructor { ty; terms } ->
        let terms = List.map (ebf_term booleans) terms in
        LConstructor { ty; terms }
    | LReindex { lhs; rhs; lterm } ->
        let lterm = ebf_lterm booleans lterm in
        LReindex { lhs; rhs; lterm }
    | LRange { ty; term } ->
        let term = ebf_term booleans term in
        LRange { ty; term }
    | LCirc lterm ->
        let lterm = ebf_lterm booleans lterm in
        LCirc lterm

  let ebf new_fn_name booleans fn_declaration =
    let Ast.{ body; _ } = fn_declaration in
    let body = ebf_term booleans body in
    { fn_declaration with fn_name = new_fn_name; body }
end
