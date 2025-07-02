module ConstProp = struct
  module Env = struct
    module Terms = Map.Make (Ast.TermIdent)

    type t = { terms : Ast.term Terms.t }
  end

  let term _env = function
    | (Ast.TFalse | TTrue) as e -> e
    | TVar _ -> failwith ""
    | TFn { fn_ident = _; tyresolve = _ } -> failwith ""
    | TLet { variable = _; term = _; k = _ } -> failwith ""
    | TLookup { lterm = _; index = _ } -> failwith ""
    | TThunk { lterm = _ } -> failwith ""
    | TLog { message = _; variables = _; k = _ } -> failwith ""
    | TOperator _ -> failwith ""
    | TFnCall { fn_name = _; ty_resolve = _; args = _ } -> failwith ""

  and lterm _env = function
    | Ast.LLetPlus { variable = _; lterm = _; ands = _; term = _ } ->
        failwith ""
    | LConstructor { ty = _; terms = _ } -> failwith ""
    | LRange { ty = _; term = _ } -> failwith ""
    | LCirc _ -> failwith ""

  and op _env = function
    | Ast.ONot _ -> failwith ""
    | OXor (_, _) -> failwith ""
    | OAnd (_, _) -> failwith ""
    | OOr (_, _) -> failwith ""
end
