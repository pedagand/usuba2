open Ast

module Ty = struct
  let bool = TyBool
  let app name ty = TyApp { name; ty }
  let tuple size ty = TyTuple { size; ty }

  let fn tyvars parameters return_type =
    TyFun { tyvars; parameters; return_type }
end

module LTerm = struct end

module Term = struct
  let true' = TTrue
  let false' = TFalse
  let v variable = TVar variable

  (* haha *)
  let funk lterm = TThunk { lterm }
  let lookup lterm index = TLookup { lterm; index }

  let let' variable term k =
    let variable = TermIdent.fresh variable in
    TLet { variable; term; k = k variable }
end

let row = TyDeclIdent.fresh "row"
let col = TyDeclIdent.fresh "col"
let slice = TyDeclIdent.fresh "slice"
let keys = TyDeclIdent.fresh "keys"
let gift = FnIdent.fresh "gift"

let gift =
  [
    NTy { tyvar = TyIdent.fresh "'a"; name = row; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = col; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = slice; size = 4 };
    NTy { tyvar = TyIdent.fresh "'a"; name = keys; size = 28 };
    (let ty_state = Ty.(app col @@ app row @@ app slice bool) in
     let ty_keys = Ty.app keys ty_state in
     let state = TermIdent.fresh "state" in
     let keys = TermIdent.fresh "keys" in
     NFun
       {
         fn_name = gift;
         tyvars = [];
         parameters = [ (state, ty_state); (keys, ty_keys) ];
         return_type = ty_state;
         body = Term.(let' "state" (failwith "") @@ fun _state -> failwith "");
       });
  ]
