type 't ty =
  | Bool
  | Var of 'ty_var
  | App of { name : 'ty_decl; ty : 't ty }
  | Fun of 't signature
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

and 't signature = {
  tyvars : 'ty_var option;
  parameters : 't ty list;
  return_type : 't ty;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

val pp :
  (Format.formatter -> 'ty_var -> unit) ->
  (Format.formatter -> 'ty_decl -> unit) ->
  Format.formatter ->
  < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. > ty ->
  unit
