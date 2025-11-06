type 't sterm_ =
  | Var of 'term_id  (** [x ] *)
  | Fn of { fn_ident : 'fn_ident }  (** [&f] *)
  | Lookup of { lterm : 't sterm_; index : int }  (** [l[i]] *)
  | Reindex of { lhs : 'ty_decl list; rhs : 'ty_decl list; lterm : 't sterm_ }
      (** [reindex[ F1 F2 ... | G1 G2 ... ](l)] *)
  | Circ of 't sterm_  (** [circ(l)] *)
  | Lift of { tys : 'ty_decl list; func : 't sterm_ }  (** [lift[F ...](f)] *)
  | FnCall of {
      fn_name : ('fn_ident, 'term_id) Either.t;
      ty_resolve : 't Ty.t option;
      args : 't cterm_ list;
    }  (** [f.[ty](t1, t2, ...)] *)
  | Operator of 't cterm_ Operator.t
  | Ann of 't cterm_ * 't Ty.t
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

and 't cterm_ =
  | False  (** [false] *)
  | True  (** [true] *)
  | Constructor of { ty : 'ty_decl; terms : 't cterm_ list }
      (** [[t1; t2; ...]] *)
  (* XXX: [ty] not necessary here *)
  | Let of { variable : 'term_id; term : 't sterm_; k : 't cterm_ }
      (** [let x = t1 in t2] *)
  | LetPlus of {
      variable : 'term_id;
      lterm : 't sterm_;
      ands : ('term_id * 't sterm_) list;
      prefix : 'ty_decl list;
      term : 't cterm_;
    }  (** [let+ x = l {and y1 = l1 and y2 = l2 ...}^? in t] *)
  | Log of { message : string; variables : 'term_id list; k : 't cterm_ }
  | Synth of 't sterm_  (** [n] *)
  constraint
    't =
    < ty_decl : 'ty_decl
    ; fn_ident : 'fn_ident
    ; ty_var : 'ty_var
    ; term_id : 'term_id >

type 'a t = 'a cterm_

let pps pp_var pp_ty_var pp_ty_decl pp_fn_ident =
  let pp_ty = Ty.pp_ pp_ty_var pp_ty_decl in
  let pp_decls format = Format.pp_print_list pp_ty_decl format in
  let pp_fn_name format =
    Format.pp_print_either ~left:pp_fn_ident ~right:pp_var format
  in
  let rec go format = function
    | False -> Format.fprintf format "false"
    | True -> Format.fprintf format "true"
    | Let { variable; term; k } ->
        Format.fprintf format "let %a = %a in %a" pp_var variable go_sterm_ term
          go k
    | LetPlus { variable; lterm; ands; prefix; term } ->
        let pp_and format (variable, lterm) =
          Format.fprintf format "and %a = %a" pp_var variable go_sterm_ lterm
        in
        let pp_ands = Format.pp_print_list pp_and in
        Format.fprintf format "let+ %a : %a _ = %a %a in %a" pp_var variable
          pp_decls prefix go_sterm_ lterm pp_ands ands go term
    | Constructor { ty; terms } ->
        Format.fprintf format "%a (%a)" pp_ty_decl ty pp_terms terms
    | Log { k; _ } -> go format k
    | Synth t -> go_sterm_ format t
  and go_sterm_ format = function
    | Var variable -> pp_var format variable
    | Fn { fn_ident; _ } -> pp_fn_ident format fn_ident
    | Lookup { lterm; index } ->
        Format.fprintf format "%a[%u]" go_sterm_ lterm index
    | Lift { tys; func } ->
        Format.fprintf format "lift[%a](%a)" pp_decls tys go_sterm_ func
    | Operator operation -> Operator.pp go format operation
    | Reindex { lhs; rhs; lterm } ->
        Format.fprintf format "reindex[%a | %a](%a)" pp_decls lhs pp_decls rhs
          go_sterm_ lterm
    | Circ lterm -> Format.fprintf format "circ(%a)" go_sterm_ lterm
    | FnCall { fn_name; ty_resolve; args } ->
        let pp_ty_resolve =
          Format.pp_print_option (fun format ty ->
              Format.fprintf format "[%a]" pp_ty ty)
        in
        Format.fprintf format "%a.%a(%a)" pp_fn_name fn_name pp_ty_resolve
          ty_resolve pp_args args
    | Ann (tm, ty) -> Format.fprintf format "(%a : %a)" go tm pp_ty ty
  and pp_terms format =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.fprintf format ", ")
      go format
  and pp_args format =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.fprintf format ", ")
      go format
  in
  (go, go_sterm_)

let pp_cterm_ pp_var pp_ty_var pp_ty_decl pp_fn_ident =
  fst (pps pp_var pp_ty_var pp_ty_decl pp_fn_ident)

let pp_sterm_ pp_var pp_ty_var pp_ty_decl pp_fn_ident =
  snd (pps pp_var pp_ty_var pp_ty_decl pp_fn_ident)

let pp =
  pp_cterm_ Ident.TermIdent.pp Ident.TyIdent.pp Ident.TyDeclIdent.pp
    Ident.FnIdent.pp

let pp_sterm =
  pp_sterm_ Ident.TermIdent.pp Ident.TyIdent.pp Ident.TyDeclIdent.pp
    Ident.FnIdent.pp

module S = struct
  let s sterm = Synth sterm
  let ann tm ty = Ann (tm, ty)
  let true' = True
  let false' = False
  let v variable = Var variable
  let vfn fn_ident = Fn { fn_ident }

  let log message variables k =
    let k = k () in
    Log { message; variables; k }

  let log_ message variables k = Log { message; variables; k }
  let lookup lterm index = Lookup { lterm; index }
  let ( .%() ) = lookup
  let let_ variable term k = Let { variable; term; k }

  let let' variable term k =
    let variable = Ident.TermIdent.fresh variable in
    Let { variable; term; k = k (v variable) }

  let fn_call ?resolve fn_name args =
    FnCall { fn_name = Left fn_name; ty_resolve = resolve; args }

  let v_call ?resolve variable_name args =
    FnCall { fn_name = Right variable_name; ty_resolve = resolve; args }

  let circ t = Circ t
  let lift tys func = Lift { tys; func }

  let reindex lhs rhs lterm =
    assert (lhs <> []);
    assert (rhs <> []);
    Reindex { lhs; rhs; lterm }

  let ( lxor ) lhs rhs = Operator (Xor (lhs, rhs))
  let ( land ) lhs rhs = Operator (And (lhs, rhs))
  let ( lor ) lhs rhs = Operator (Or (lhs, rhs))
  let lnot term = Operator (Not term)
  let cstr ty terms = Constructor { ty; terms }

  let let_plus variable prefix lterm ands k =
    let variable = Ident.TermIdent.fresh variable in
    let ands =
      List.map
        (fun (v, term) ->
          let v = Ident.TermIdent.fresh v in
          (v, term))
        ands
    in
    let vand = List.map fst ands in
    let term = k variable vand in
    LetPlus { variable; prefix; lterm; ands; term }
end
