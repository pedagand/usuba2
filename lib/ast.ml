module TermIdent = Ident.Make ()
module TyIdent = Ident.Make ()
module TyDeclIdent = Ident.Make ()
module FnIdent = Ident.Make ()

type 't sterm =
  | Var of 'term_id  (** [x ] *)
  | Fn of { fn_ident : 'fn_ident }  (** [&f] *)
  | Lookup of { lterm : 't sterm; index : int }  (** [l[i]] *)
  | Reindex of { lhs : 'ty_decl list; rhs : 'ty_decl list; lterm : 't sterm }
      (** [reindex[ F1 F2 ... | G1 G2 ... ](l)] *)
  | Circ of 't sterm  (** [circ(l)] *)
  | Lift of { tys : 'ty_decl list; func : 't sterm }  (** [lift[F ...](f)] *)
  | FnCall of {
      fn_name : ('fn_ident, 'term_id) Either.t;
      ty_resolve : 't Ty.t option;
      args : 't cterm list;
    }  (** [f.[ty](t1, t2, ...)] *)
  | Operator of 't cterm Operator.t
  | Ann of 't cterm * 't Ty.t
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

and 't cterm =
  | False  (** [false] *)
  | True  (** [true] *)
  | Constructor of { ty : 'ty_decl; terms : 't cterm list }
      (** [[t1; t2; ...]] *)
  (* XXX: [ty] not necessary here *)
  | Let of { variable : 'term_id; term : 't sterm; k : 't cterm }
      (** [let x = t1 in t2] *)
  | LetPlus of {
      variable : 'term_id;
      lterm : 't sterm;
      ands : ('term_id * 't sterm) list;
      term : 't cterm;
    }  (** [let+ x = l {and y1 = l1 and y2 = l2 ...}^? in t] *)
  | Log of { message : string; variables : 'term_id list; k : 't cterm }
  | Synth of 't sterm  (** [n] *)
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

type 'a term = 'a cterm

type 't fn_declaration_ = {
  fn_name : 'fn_ident;
  signature : 't Ty.signature;
  args : 'term_id list;
  body : 't term;
}
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >
(** [fn f [a](x1: ty1, x2: ty2, ...) ty = t] *)

(* Type decl only create alias. *)
type 't ty_declaration_ = {
  (* XXX: what's this `ty_var` doing here? *)
  tyvar : 'ty_var;
  name : 'ty_decl;
  size : int;
}
  constraint 't = < ty_decl : 'ty_decl ; ty_var : 'ty_var ; .. >
(** [type ty = tuple[i]] *)

type 't node_ = NFun of 't fn_declaration_ | NTy of 't ty_declaration_
type 't prog_ = 't node_ list

type pre =
  < ty_decl : string ; fn_ident : string ; ty_var : string ; term_id : string >

type pre_ty_declaration = pre ty_declaration_
type pre_fn_declaration = pre fn_declaration_
type pre_node = pre node_
type pre_prog = pre prog_

type scoped =
  < ty_decl : TyDeclIdent.t
  ; fn_ident : FnIdent.t
  ; ty_var : TyIdent.t
  ; term_id : TermIdent.t >

type ty_declaration = scoped ty_declaration_
type fn_declaration = scoped fn_declaration_
type node = scoped node_
type prog = scoped prog_
