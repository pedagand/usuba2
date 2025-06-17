open Ast

module Ty = struct
  let bool = TyBool
  let v v = TyVar v
  let app name ty = TyApp { name; ty }
  let tuple size ty = TyTuple { size; ty }

  let fn tyvars parameters return_type =
    TyFun { tyvars; parameters; return_type }
end

module LTerm = struct
  let range ty term = LRange { ty; term }
end

module Term = struct
  let true' = TTrue
  let false' = TFalse
  let v variable = TVar variable

  (* haha *)
  let funk lterm = TThunk { lterm }
  let lookup lterm index = TLookup { lterm; index }
  let ( .%() ) = lookup

  let let' variable term k =
    let variable = TermIdent.fresh variable in
    TLet { variable; term; k = k variable }
end

let row = TyDeclIdent.fresh "row"
let col = TyDeclIdent.fresh "col"
let slice = TyDeclIdent.fresh "slice"
let keys = TyDeclIdent.fresh "keys"

let subcells, node_subcells =
  let subcells = FnIdent.fresh "subcell" in
  let alpha = TyIdent.fresh "'a" in
  let ty_slice = Ty.(app slice @@ v alpha) in
  let tslice = TermIdent.fresh "slice" in
  let node =
    NFun
      {
        fn_name = subcells;
        tyvars = [ alpha ];
        parameters = [ (tslice, ty_slice) ];
        return_type = ty_slice;
        body =
          LTerm.(
            Term.(
              let' "s0" (range [ slice ] (v tslice)).%(0) @@ fun _s0 ->
              let' "s1" (range [ slice ] (v tslice)).%(1) @@ fun _s1 ->
              let' "s2" (range [ slice ] (v tslice)).%(2) @@ fun _s2 ->
              let' "s3" (range [ slice ] (v tslice)).%(3) @@ fun _s3 ->
              failwith ""));
      }
  in
  (subcells, node)

let gift, node_gift =
  let gift = FnIdent.fresh "gift" in
  let ty_state = Ty.(app col @@ app row @@ app slice bool) in
  let ty_keys = Ty.app keys ty_state in
  let state = TermIdent.fresh "state" in
  let keys = TermIdent.fresh "keys" in
  let node =
    NFun
      {
        fn_name = gift;
        tyvars = [];
        parameters = [ (state, ty_state); (keys, ty_keys) ];
        return_type = ty_state;
        body =
          Term.(let' "state" (funk (failwith "")) @@ fun _state -> failwith "");
      }
  in
  (gift, node)

let ast =
  [
    NTy { tyvar = TyIdent.fresh "'a"; name = row; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = col; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = slice; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = keys; size = 28 };
    node_subcells;
    node_gift;
  ]
