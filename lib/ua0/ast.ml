module Ident () = struct
  type t = { id : int; pretty : string }

  let fresh =
    let c = ref 0 in
    fun pretty ->
      let () = incr c in
      { id = !c; pretty }

  let compare lhs rhs = Int.compare lhs.id rhs.id
  let equal lhs rhs = Int.equal lhs.id rhs.id
  let pp format { id = _; pretty } = Format.fprintf format "%s" pretty
end

module TermIdent = Ident ()
module LTermIdent = Ident ()
module TyIdent = Ident ()

type ty = TyBool | TyVar of TyIdent.t | TyTuple of { size : int; ty : ty }

type lterm =
  | LTLetPlus of {
      variable : TermIdent.t;
      lterm : lterm;
      ands : (TermIdent.t * lterm) list;
      term : term;
    }

and term =
  | TFalse
  | TTrue
  | TVar of TermIdent.t
  | TLet of { variable : TermIdent.t; term : term }
  | Tlookup of { lterm : lterm; index : int }
