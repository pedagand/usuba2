module Make () = struct
  module C = struct
    type t = { id : int; pretty : string }

    let compare lhs rhs = Int.compare lhs.id rhs.id
  end

  module Set = Set.Make (C)
  module Map = Map.Make (C)
  include C

  let fresh =
    let c = ref 0 in
    fun pretty ->
      let () = incr c in
      { id = !c; pretty }

  let equal lhs rhs = Int.equal lhs.id rhs.id
  let pp format { id; pretty } = Format.fprintf format "%s(%u)" pretty id
  let refresh prefix base = fresh @@ Format.asprintf "%s%a" prefix pp base
end

type pre =
  < ty_decl : string ; fn_ident : string ; ty_var : string ; term_id : string >

module TermIdent = Make ()
module TyIdent = Make ()
module TyDeclIdent = Make ()
module FnIdent = Make ()

type scoped =
  < ty_decl : TyDeclIdent.t
  ; fn_ident : FnIdent.t
  ; ty_var : TyIdent.t
  ; term_id : TermIdent.t >
