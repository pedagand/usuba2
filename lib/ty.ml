type 't t =
  | Bool  (** [bool] *)
  | Var of 'ty_var  (** ['a] *)
  | App of { name : 'ty_decl; ty : 't t }  (** [tname ty] *)
  | Fun of 't signature  (** [['a]^? (ty1, ty2, ...) -> ty] *)
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

and 't signature = {
  tyvars : 'ty_var option;
  parameters : 't t list;
  return_type : 't t;
}
  constraint 't = < ty_var : 'ty_var ; ty_decl : 'ty_decl ; .. >

let pp pp_var pp_decl =
  let pp_var_opt format = Format.pp_print_option pp_var format in
  let rec go format = function
    | Bool -> Format.fprintf format "bool"
    | App { name; ty } -> Format.fprintf format "%a %a" pp_decl name go ty
    | Fun { tyvars; parameters; return_type } ->
        Format.fprintf format "fn %a(%a) -> %a" pp_var_opt tyvars gos parameters
          go return_type
    | Var name -> Format.fprintf format "%a" pp_var name
  and gos format =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
      go format
  in
  go
