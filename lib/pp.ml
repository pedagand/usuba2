open Ast

let pp_builtin format = function
  | BCirc -> Format.fprintf format "@circ"
  | BAntiCirc -> Format.fprintf format "@anti_circ"
  | BPure -> Format.fprintf format "@pure"

let rec pp_kind format = function
  | KType -> Format.fprintf format "*"
  | KArrow (parameters, return) ->
      Format.fprintf format "(%a) => %a" pp_kind parameters pp_kind return

let pp_tyvars format ty_vars =
  match ty_vars with
  | [] -> ()
  | _ :: _ as ty_vars ->
      let pp_list =
        Format.pp_print_list ~pp_sep:(fun format () ->
            Format.fprintf format ", ")
        @@ fun format (id, kind) ->
        Format.fprintf format "%a :: %a" TyIdent.pp id pp_kind kind
      in
      Format.fprintf format "%a. " pp_list ty_vars

let pp_tyvars' format ty_vars =
  match ty_vars with
  | [] -> ()
  | _ :: _ as ty_vars ->
      let pp_list =
        Format.pp_print_list
          ~pp_sep:(fun format () -> Format.fprintf format ", ")
          TyIdent.pp
      in
      Format.fprintf format "%a. " pp_list ty_vars

let rec pp_ty format = function
  | TyBool -> Format.fprintf format "bool"
  | TyApp { name; ty_args } ->
      Format.fprintf format "%a%a" pp_ty_opt_args ty_args TyDeclIdent.pp name
  | TyFun { ty_vars; parameters; return_type } ->
      Format.fprintf format "%a(%a) -> %a" pp_tyvars' ty_vars pp_tys parameters
        pp_ty return_type
  | TyVarApp { name; ty_args } ->
      Format.fprintf format "%a%a" pp_ty_opt_args ty_args TyIdent.pp name
  | TyTuple { size; ty } -> Format.fprintf format "%a tuple<%u>" pp_ty ty size

and pp_tys format =
  Format.pp_print_list
    ~pp_sep:(fun format () -> Format.pp_print_char format ',')
    pp_ty format

and pp_ty_args format ty_args =
  match ty_args with
  | [] -> ()
  | (TyFun _ as ty) :: [] -> Format.fprintf format "(%a) " pp_ty ty
  | ty :: [] -> Format.fprintf format "%a " pp_ty ty
  | _ :: _ as ty_args -> Format.fprintf format "(%a) " pp_tys ty_args

and pp_ty_opt_args format ty_args =
  match ty_args with
  | None -> ()
  | Some (TyFun _ as ty) -> Format.fprintf format "(%a) " pp_ty ty
  | Some ty -> Format.fprintf format "%a " pp_ty ty

let pp_op fmt format = function
  | Unot expression -> Format.fprintf format "! %a" fmt expression
  | BAnd (lhs, rhs) -> Format.fprintf format "%a and (%a)" fmt lhs fmt rhs
  | BOr (lhs, rhs) -> Format.fprintf format "%a or (%a)" fmt lhs fmt rhs
  | BXor (lhs, rhs) -> Format.fprintf format "%a xor (%a)" fmt lhs fmt rhs

let pp_indexing format indexing =
  let { name; index } = indexing in
  Format.fprintf format "%a(%u)" TyDeclIdent.pp name index

let rec pp_expression format = function
  | ETrue -> Format.fprintf format "1"
  | EFalse -> Format.fprintf format "0"
  | EVar id -> Format.fprintf format "%a" TermIdent.pp id
  | EFunVar id -> Format.fprintf format "%a" FnIdent.pp id
  | EIndexing { expression; indexing } ->
      Format.fprintf format "%a[%a]" pp_expression expression pp_indexing
        indexing
  | EOp op -> pp_op pp_expression format op
  | EBuiltinCall { builtin; ty_args; args } ->
      Format.fprintf format "%a%a(%a)" pp_builtin builtin pp_ty_args ty_args
        pp_expressions args
  | EFunctionCall { fn_name; ty_args; args } ->
      let pp_either =
        Format.pp_print_either ~left:FnIdent.pp ~right:TermIdent.pp
      in
      Format.fprintf format "%a%a(%a)" pp_either fn_name pp_ty_args ty_args
        pp_expressions args

and pp_expressions format =
  Format.pp_print_list
    ~pp_sep:(fun format () -> Format.pp_print_char format ',')
    pp_expression format

let pp_statement format = function
  | StDeclaration { variable; expression } ->
      Format.fprintf format "let %a = %a in" TermIdent.pp variable pp_expression
        expression
  | StConstructor { variable; ty; expressions } ->
      Format.fprintf format "let %a = %a {%a} in" TermIdent.pp variable pp_ty ty
        pp_expressions expressions
  | SLetPLus { variable; expression; ands } ->
      let pp_ands =
        Format.pp_print_list
          ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
          (fun format (id, expression) ->
            Format.fprintf format "and+ %a = %a" TermIdent.pp id pp_expression
              expression)
      in
      Format.fprintf format "let+ %a = %a %a in" TermIdent.pp variable
        pp_expression expression pp_ands ands

let pp_function_decl format decl =
  let {
    fn_name;
    ty_vars;
    parameters;
    return_type;
    body = { statements; expression };
  } =
    decl
  in
  let pp_args =
    Format.pp_print_list
      ~pp_sep:(fun format () -> Format.pp_print_string format ", ")
      (fun format (id, expression) ->
        Format.fprintf format "%a: %a" TermIdent.pp id pp_ty expression)
  in
  let pp_statements =
    Format.pp_print_list ~pp_sep:Format.pp_print_newline pp_statement
  in
  Format.fprintf format "def %a%a(%a) -> %a =%a%a%a%a" pp_tyvars ty_vars
    FnIdent.pp fn_name pp_args parameters pp_ty return_type
    Format.pp_print_newline () pp_statements statements Format.pp_print_newline
    () pp_expression expression

let pp_type_decl format type_decl =
  let { ty_vars; ty_name; definition } = type_decl in
  let pp_ty_args format ty_args =
    match ty_args with
    | [] -> ()
    | _ :: _ as ty_args ->
        let pp_list =
          Format.pp_print_list
            ~pp_sep:(fun format () -> Format.pp_print_char format ',')
            TyIdent.pp
        in
        Format.fprintf format "(%a) " pp_list ty_args
  in
  Format.fprintf format "type %a%a = %a" pp_ty_args ty_vars TyDeclIdent.pp
    ty_name pp_ty definition

let pp_node format = function
  | KnFundecl function_decl -> pp_function_decl format function_decl
  | KnTypedecl type_decl -> pp_type_decl format type_decl

let pp_module format =
  Format.pp_print_list
    ~pp_sep:(fun format () ->
      Format.(fprintf format "%a%a" pp_print_newline () pp_print_newline ()))
    pp_node format
