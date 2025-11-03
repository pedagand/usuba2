type 't t = private
  | Bool
  | Var of 'ty_var
  | App of 't spine
  | Fun of 't signature
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

and 't signature = {
  tyvars : 'ty_var option;
  parameters : 't t list;
  return_type : 't t;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

and 't spine = {
  names : 'ty_decl list;
  bty : 't t;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

type 't spines = {
  names : 'ty_decl list;
  btys : 't t list;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

val map :
  ('a -> 'c) ->
  ('b -> 'd) ->
  < ty_var : 'a ; ty_decl : 'b ; .. > t ->
  < ty_var : 'c ; ty_decl : 'd ; .. > t

val pp_ :
  (Format.formatter -> 'ty_var -> unit) ->
  (Format.formatter -> 'ty_decl -> unit) ->
  Format.formatter ->
  < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. > t ->
  unit

module S : sig
  val bool : 't t
  val v : 'ty_var -> < ty_var : 'ty_var ; .. > t
  val ( @ ) : 'ty_decl -> (< ty_decl : 'ty_decl ; .. > as 'b) t -> 'b t
  val apps : 'ty_decl list -> (< ty_decl : 'ty_decl ; .. > as 'b) t -> 'b t

  val fn :
    ?tyvars:'ty_var option ->
    (< ty_var : 'ty_var ; .. > as 'b) t list ->
    'b t ->
    'b t
end

val to_spine : 't t -> 't spine
val from_spine : 't spine -> 't t

(** Over scoped terms: *)

val pp : Format.formatter -> Ident.scoped t -> unit

val merges :
  Ident.scoped spine -> Ident.scoped spine list -> Ident.scoped spines

val take : Ident.TyDeclIdent.t list -> Ident.scoped t -> Ident.scoped t
val equal : Ident.scoped t -> Ident.scoped t -> bool
val bind : Ident.TyIdent.t -> Ident.scoped t -> Ident.scoped t -> Ident.scoped t

(**/*)

(* XXX: for test only *)
val merge : Ident.scoped spines -> Ident.scoped spine -> Ident.scoped spines
