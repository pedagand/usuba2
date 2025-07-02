module Ty = Scstr.Ty
module LTerm = Scstr.LTerm
module Term = Scstr.Term

module ConstProp = struct
  module Value = struct
    type t =
      | VTerm of Ast.TermIdent.t
      | VIndex of { cstr : Ast.TyDeclIdent.t; values : t Array.t; index : int }
      | VBool of bool
      | VOp of t Ast.operator
      | VArray of { cstr : Ast.TyDeclIdent.t; values : t Array.t }
      | VFn of { fn_ident : Ast.FnIdent.t; tyresolve : Ast.ty list }

    let simplify = function
      | VTerm _ -> failwith ""
      | VBool _ -> failwith ""
      | VFn { fn_ident; tyresolve } ->
          let () = ignore (fn_ident, tyresolve) in
          failwith ""
      | VIndex { cstr; values; index } ->
          let () = ignore (cstr, values, index) in
          failwith ""
      | VOp _ -> failwith ""
      | VArray { cstr; values } ->
          let () = ignore (cstr, values) in
          failwith ""

    let rec to_ast = function
      | VTerm term -> Term.v term
      | VIndex { cstr = _; values; index } ->
          let value = values.(index) in
          let ast = to_ast value in
          ast
      | VBool true -> Term.true'
      | VBool false -> Term.false'
      | VFn { fn_ident; tyresolve } -> Term.vfn tyresolve fn_ident
      | VOp op -> to_ast_op op
      | VArray { cstr = c; values } ->
          let values = Array.map to_ast values in
          let values = Array.to_list values in
          LTerm.(Term.(funk (cstr c values)))

    and to_ast_op = function
      | Ast.ONot value -> Term.lnot (to_ast value)
      | Ast.OAnd (lhs, rhs) ->
          let lhs = to_ast lhs in
          let rhs = to_ast rhs in
          Term.(lhs land rhs)
      | Ast.OOr (lhs, rhs) ->
          let lhs = to_ast lhs in
          let rhs = to_ast rhs in
          Term.(lhs lor rhs)
      | Ast.OXor (lhs, rhs) ->
          let lhs = to_ast lhs in
          let rhs = to_ast rhs in
          Term.(lhs lxor rhs)
  end

  module Env = struct
    module Terms = Map.Make (Ast.TermIdent)

    type t = { terms : Value.t Terms.t }

    let bind ident value env = { terms = Terms.add ident value env.terms }

    let value' ident env =
      match Terms.find_opt ident env.terms with
      | Some value -> value
      | None -> Value.VTerm ident

    let term_substitute v env =
      match Terms.find_opt v env.terms with
      | Some value -> Value.to_ast value
      | None -> Term.v v
  end

  let eval env = function
    | Ast.TFalse -> Value.VBool false
    | TTrue -> Value.VBool true
    | TFn { fn_ident; tyresolve } -> VFn { fn_ident; tyresolve }
    | TVar term -> Env.value' term env
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

  let rec term env = function
    | (Ast.TFalse | TTrue | TFn _) as e -> e
    | TVar term -> Env.term_substitute term env
    | TLet { variable; term = term'; k } ->
        let value = eval env term' in
        let env = Env.bind variable value env in
        let t = Value.to_ast value in
        Term.let_ variable t (term env k)
    | TLookup { lterm = _; index = _ } -> failwith ""
    | TThunk { lterm = _ } -> failwith ""
    | TLog { message = _; variables = _; k = _ } -> failwith ""
    | TOperator _ -> failwith ""
    | TFnCall { fn_name = _; ty_resolve = _; args = _ } -> failwith ""

  and _lterm _env = function
    | Ast.LLetPlus { variable = _; lterm = _; ands = _; term = _ } ->
        failwith ""
    | LConstructor { ty = _; terms = _ } -> failwith ""
    | LRange { ty = _; term = _ } -> failwith ""
    | LCirc _ -> failwith ""

  and _op _env = function
    | Ast.ONot _ -> failwith ""
    | OXor (_, _) -> failwith ""
    | OAnd (_, _) -> failwith ""
    | OOr (_, _) -> failwith ""
end
