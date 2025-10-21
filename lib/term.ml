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

type 'a t = 'a cterm

let pps pp_var pp_ty_var pp_ty_decl pp_fn_ident =
  let pp_ty = Ty.pp pp_ty_var pp_ty_decl in
  let pp_decls format = Format.pp_print_list pp_ty_decl format in
  let pp_fn_name format =
    Format.pp_print_either ~left:pp_fn_ident ~right:pp_var format
  in
  let rec go format = function
    | False -> Format.fprintf format "false"
    | True -> Format.fprintf format "true"
    | Let { variable; term; k } ->
        Format.fprintf format "let %a = %a in %a" pp_var variable go_sterm term
          go k
    | LetPlus { variable; lterm; ands; term } ->
        let pp_and format (variable, lterm) =
          Format.fprintf format "and %a = %a" pp_var variable go_sterm lterm
        in
        let pp_ands = Format.pp_print_list pp_and in
        Format.fprintf format "let+ %a = %a %a in %a" pp_var variable go_sterm
          lterm pp_ands ands go term
    | Constructor { ty; terms } ->
        Format.fprintf format "%a (%a)" pp_ty_decl ty pp_terms terms
    | Log { k; _ } -> go format k
    | Synth t -> go_sterm format t
  and go_sterm format = function
    | Var variable -> pp_var format variable
    | Fn { fn_ident; _ } -> pp_fn_ident format fn_ident
    | Lookup { lterm; index } ->
        Format.fprintf format "%a[%u]" go_sterm lterm index
    | Lift { tys; func } ->
        Format.fprintf format "lift[%a](%a)" pp_decls tys go_sterm func
    | Operator operation -> Operator.pp go format operation
    | Reindex { lhs; rhs; lterm } ->
        Format.fprintf format "reindex[%a | %a](%a)" pp_decls lhs pp_decls rhs
          go_sterm lterm
    | Circ lterm -> Format.fprintf format "circ(%a)" go_sterm lterm
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
  (go, go_sterm)

let pp_cterm pp_var pp_ty_var pp_ty_decl pp_fn_ident =
  fst (pps pp_var pp_ty_var pp_ty_decl pp_fn_ident)

let pp = pp_cterm

let pp_sterm pp_var pp_ty_var pp_ty_decl pp_fn_ident =
  snd (pps pp_var pp_ty_var pp_ty_decl pp_fn_ident)
