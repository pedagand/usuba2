module LTerm = Scstr.LTerm
module Term = Scstr.Term
module Ty = Value.Ty
module STy = Scstr.Ty

module Value = struct
  type t =
    | VBool of bool
    | VTerm of Ast.TermIdent.t
    | VArray of { cstr : Ast.TyDeclIdent.t; values : t Array.t }
    | VFunction of Ast.FnIdent.t * Ast.ty list
    | VOp of t Ast.operator
    | VIndex of { cstr : Ast.TyDeclIdent.t; values : t Array.t; index : int }

  let rec pp format = function
    | VBool true -> Format.fprintf format "1"
    | VBool false -> Format.fprintf format "0"
    | VArray { cstr = _; values = array } ->
        let pp_sep format () = Format.pp_print_string format ", " in
        Format.fprintf format "[%a]" (Format.pp_print_array ~pp_sep pp) array
    | VFunction (fn, tys) ->
        Format.fprintf format "%a%a" Ast.FnIdent.pp fn Pp.pp_tys tys
    | VTerm variable -> Format.fprintf format "%a" Ast.TermIdent.pp variable
    | VIndex { cstr = _; values; index } ->
        let value = Array.get values index in
        Format.fprintf format "%a" pp value
    | VOp op -> pp_op format op

  and pp_op format = function
    | Ast.ONot value -> Format.fprintf format "! %a" pp value
    | Ast.OAnd (lhs, rhs) -> Format.fprintf format "%a && %a" pp lhs pp rhs
    | Ast.OOr (lhs, rhs) -> Format.fprintf format "%a || %a" pp lhs pp rhs
    | Ast.OXor (lhs, rhs) -> Format.fprintf format "%a ^ %a" pp lhs pp rhs

  let true' = VBool true
  let false' = VBool false

  let rec not = function
    | VBool e -> VBool (Stdlib.not e)
    | (VTerm _ | VOp _) as t -> VOp (ONot t)
    | VIndex { cstr; values; index } ->
        let value = not values.(index) in
        let () = values.(index) <- value in
        VIndex { cstr; values; index }
    | VArray _ | VFunction _ -> failwith "not can only be applied to scalar."

  let ( lxor ) lhs rhs =
    match (lhs, rhs) with
    | VBool lhs, VBool rhs -> VBool (lhs <> rhs)
    | _, _ -> failwith "(lxor) can only be applied to two scalar"

  let ( land ) lhs rhs =
    match (lhs, rhs) with
    | VBool lhs, VBool rhs -> VBool (lhs && rhs)
    | _, _ -> failwith "(land) can only be applied to two scalar"

  let ( lor ) lhs rhs =
    match (lhs, rhs) with
    | VBool lhs, VBool rhs -> VBool (lhs || rhs)
    | _, _ -> failwith "(lor) can only be applied to two scalar"

  (*  let rec map2' f lhs rhs =
    match (lhs, rhs) with
    | VBool lhs, VBool rhs -> VBool (f lhs rhs)
    | VArray lhs, VArray rhs -> VArray (Array.map2 (map2' f) lhs rhs)
    | VBool _, VArray _ | VArray _, VBool _ | VFunction _, _ | _, VFunction _ ->
        assert false

  let rec map2 f lhs rhs =
    match (lhs, rhs) with
    | (VBool _ as lhs), (VBool _ as rhs) -> f lhs rhs
    | VArray lhs, VArray rhs -> VArray (Array.map2 (map2 f) lhs rhs)
    | VBool _, VArray _ | VArray _, VBool _ | VFunction _, _ | _, VFunction _ ->
        assert false*)

  let rec as_array = function
    | VArray { cstr = _; values = array } -> Some array
    | VIndex { cstr = _; values; index } -> as_array values.(index)
    | VBool _ | VFunction _ | VTerm _ | VOp _ -> None

  let rec as_function = function
    | VFunction (fn_ident, e) -> Some (fn_ident, e)
    | VIndex { cstr = _; values; index } -> as_function values.(index)
    | VArray _ | VBool _ | VTerm _ | VOp _ -> None

  let rec map' f = function
    | VBool b -> VBool (f b)
    | VArray { cstr; values } ->
        let values = Array.map (map' f) values in
        VArray { cstr; values }
    | VFunction _ -> assert false
    | _ -> failwith ""

  let rec get i = function
    | VArray { cstr = _; values } -> values.(i)
    | VIndex { cstr = _; values; index } -> get i values.(index)
    | VBool _ as v -> if i = 0 then v else assert false
    | VFunction _ -> assert false
    | _ -> failwith ""

  (*let rec pp format = function
  | VBool true -> Format.fprintf format "1"
  | VBool false -> Format.fprintf format "0"
  | VArray array ->
      let pp_sep format () = Format.pp_print_string format ", " in
      Format.fprintf format "[%a]" (Format.pp_print_array ~pp_sep pp) array
  | VFunction (fn, tys) ->
      let pp_none _format () = () in
      let pp_option =
        Format.pp_print_option ~none:pp_none @@ fun format tys ->
        Format.fprintf format "[%a]" Pp.pp_tys tys
      in
      Format.fprintf format "%a%a" Ast.FnIdent.pp fn pp_option tys*)

  let anticirc = function
    | VArray { cstr; values } as cir0 ->
        let cardinal = Array.length values in
        let circs =
          Array.init (cardinal - 1) @@ fun i ->
          let i = i + 1 in
          let value =
            Array.init cardinal (fun n ->
                let index = (n + i) mod cardinal in
                values.(index))
          in
          VArray { cstr; values = value }
        in
        let values = Array.append [| cir0 |] circs in
        VArray { cstr; values }
    | VBool _ | VFunction _ -> failwith ""
    | _ -> failwith ""

  let circ = function
    | VArray { cstr; values } as cir0 ->
        let cardinal = Array.length values in
        let circs =
          Array.init (cardinal - 1) @@ fun i ->
          let i = i + 1 in
          let value =
            Array.init cardinal (fun n ->
                let index = (cardinal + (n - i)) mod cardinal in
                values.(index))
          in
          VArray { cstr; values = value }
        in
        let values = Array.append [| cir0 |] circs in
        VArray { cstr; values }
    | VBool _ | VFunction _ | VTerm _ | VOp _ | VIndex _ -> failwith ""

  let as_bool = function
    | VBool s -> Some s
    | VFunction _ | VArray _ | VTerm _ | VOp _ | VIndex _ -> None

  let rec mapn' level f values =
    (*    let () = Format.eprintf "level = %u\n" level in*)
    match level with
    | [] -> f values
    | cstr :: cstrs ->
        (*        let () =
          List.iter (fun value -> Format.eprintf "%a\n" pp value) values
        in*)
        let first = List.nth values 0 in
        let length = first |> as_array |> Option.get |> Array.length in
        let values = Array.init length (fun i -> mapn'' cstrs i f values) in
        VArray { cstr; values }

  and mapn'' cstrs i f values =
    let values = List.map (fun value -> get i value) values in
    mapn' cstrs f values

  let tabulate cstr size f =
    let values = Array.init size f in
    VArray { cstr; values }
end

module Eval = struct
  let err fmt = Format.kasprintf failwith fmt
  let log fmt = Format.eprintf fmt

  module Env = struct
    module Functions = Map.Make (Ast.FnIdent)
    module Types = Map.Make (Ast.TyDeclIdent)
    module Variables = Map.Make (Ast.TermIdent)
    module TyVariables = Map.Make (Ast.TyIdent)

    type t = {
      current_function : Ast.FnIdent.t option;
      types : Ast.ty_declaration Types.t;
      functions : Ast.fn_declaration Functions.t;
      variables : (Value.t * Ty.ty) Variables.t;
      type_variables : Ty.ty TyVariables.t;
    }

    let init =
      {
        current_function = None;
        functions = Functions.empty;
        types = Types.empty;
        variables = Variables.empty;
        type_variables = TyVariables.empty;
      }

    let add_function (fn : Ast.fn_declaration) env =
      { env with functions = Functions.add fn.fn_name fn env.functions }

    let add_types (ty : Ast.ty_declaration) env =
      { env with types = Types.add ty.name ty env.types }

    let bind_variable variable value ty env =
      { env with variables = Variables.add variable (value, ty) env.variables }

    let type_declaration name env =
      match Types.find_opt name env.types with
      | None -> err "type %a not in env" Ast.TyDeclIdent.pp name
      | Some e -> e

    let fn_declaration name env =
      match Functions.find_opt name env.functions with
      | None -> err "function %a not in env" Ast.FnIdent.pp name
      | Some e -> e

    let rec range acc prefix ty env =
      match prefix with
      | [] -> Ty.lty (List.rev acc) ty
      | t :: q ->
          let name, size, ty =
            match ty with
            | Ty.TNamedTuple { name; size; ty } -> (name, size, ty)
            | TBool | TFun _ -> err "Not a named tuple."
          in
          let () =
            match Ast.TyDeclIdent.equal name t with
            | true -> ()
            | false ->
                err "range prefix = %a - ty = %a" Ast.TyDeclIdent.pp t
                  Ast.TyDeclIdent.pp name
          in
          range ((name, size) :: acc) q ty env

    let range prefix = range [] prefix

    let cstr_log name env =
      let decl = type_declaration name env in
      decl.size

    let clear_variables env = { env with variables = Variables.empty }
    let clear_tyvariables env = { env with type_variables = TyVariables.empty }

    let rec to_ty env = function
      | Ty.TBool -> Ast.TyBool
      | TNamedTuple { name; ty; size = _ } ->
          let ty = to_ty env ty in
          TyApp { name; ty }
      | TFun signature ->
          let signature = to_signature env signature in
          TyFun signature

    and to_signature env = function
      | { tyvars; parameters; return_type } ->
          let parameters = List.map (to_ty env) parameters in
          let return_type = to_ty env return_type in
          { tyvars; parameters; return_type }

    let rec of_ty env ty =
      match ty with
      | Ast.TyBool -> Ty.TBool
      | TyApp { name; ty } ->
          let Ast.{ size; _ } = type_declaration name env in
          let ty = of_ty env ty in
          Ty.TNamedTuple { name; size; ty }
      | TyFun signature ->
          let signature = of_signature signature env in
          Ty.TFun signature
      | TyVar variable -> (
          match TyVariables.find_opt variable env.type_variables with
          | None -> (
              match env.current_function with
              | None ->
                  err "Undefinied ty_variable : %a" Ast.TyIdent.pp variable
              | Some fn ->
                  err "%a : Undefinied ty_variable : %a" Ast.FnIdent.pp fn
                    Ast.TyIdent.pp variable)
          | Some ty -> ty)

    and of_signature signature env =
      let Ast.{ tyvars; parameters; return_type } : Ast.signature = signature in

      Ty.
        {
          tyvars;
          parameters = List.map (of_ty env) parameters;
          return_type = of_ty env return_type;
        }

    let init_tyvariables types env =
      let env = { env with type_variables = TyVariables.empty } in
      let type_variables =
        List.fold_left
          (fun tyvars (tyvar, ty) ->
            let ty = of_ty env ty in
            TyVariables.add tyvar ty tyvars)
          TyVariables.empty types
      in
      { env with type_variables }

    let init_variables parameters values env =
      let env = clear_variables env in
      List.fold_left2
        (fun env (term, ty) value ->
          let ty = of_ty env ty in
          bind_variable term value ty env)
        env parameters values

    let lookup variable env =
      match Variables.find_opt variable env.variables with
      | Some e -> e
      | None -> err "variable %a not in env" Ast.TermIdent.pp variable

    let signature fn_name tyresolve env =
      match Functions.find_opt fn_name env.functions with
      | Some fn_decl ->
          let env =
            List.fold_left2
              (fun env tyvar ty ->
                let ty = of_ty env ty in
                {
                  env with
                  type_variables = TyVariables.add tyvar ty env.type_variables;
                })
              env fn_decl.tyvars tyresolve
          in
          Ty.
            {
              tyvars = [];
              parameters =
                List.map (fun (_, ty) -> of_ty env ty) fn_decl.parameters;
              return_type = of_ty env fn_decl.return_type;
            }
      | None -> err "function %a not in env" Ast.FnIdent.pp fn_name
  end

  let rec ty_substitute types = function
    | Ast.TyBool -> Ast.TyBool
    | TyApp { name; ty } ->
        let ty = ty_substitute types ty in
        Ast.TyApp { name; ty }
    | TyFun signature ->
        let signature = ty_substitute_sig types signature in
        Ast.TyFun signature
    | TyVar variable as default ->
        types |> List.assoc_opt variable |> Option.value ~default

  and ty_substitute_sig types signature =
    let Ast.{ tyvars; parameters; return_type } : Ast.signature = signature in
    Ast.
      {
        tyvars;
        parameters = List.map (ty_substitute types) parameters;
        return_type = ty_substitute types return_type;
      }

  let rec eval_op env = function
    | Ast.ONot term ->
        let value, ty = eval_term env term in
        let () = assert (Ty.is_bool ty) in
        let value = Value.not value in
        (value, ty)
    | OXor (lhs, rhs) ->
        let lvalue, lty' = eval_term env lhs in
        let rvalue, rty = eval_term env rhs in
        let () = assert (Ty.(is_bool lty' && is_bool rty)) in
        let value = Value.( lxor ) lvalue rvalue in
        (value, lty')
    | OAnd (lhs, rhs) ->
        let lvalue, lty' = eval_term env lhs in
        let rvalue, rty = eval_term env rhs in
        let () = assert (Ty.(is_bool lty' && is_bool rty)) in
        let value = Value.( land ) lvalue rvalue in
        (value, lty')
    | OOr (lhs, rhs) ->
        let lvalue, lty' = eval_term env lhs in
        let rvalue, rty = eval_term env rhs in
        let () = assert (Ty.(is_bool lty' && is_bool rty)) in
        let value = Value.( lor ) lvalue rvalue in
        (value, lty')

  and eval_term env = function
    | Ast.TFalse -> (Value.VBool false, Ty.TBool)
    | TTrue -> (Value.VBool true, Ty.TBool)
    | TVar variable -> Env.lookup variable env
    | TFn { fn_ident; tyresolve } ->
        let signature = Env.signature fn_ident tyresolve env in
        (Value.VFunction (fn_ident, tyresolve), Ty.TFun signature)
    | TLet { variable; term; k } ->
        let value, ty = eval_term env term in
        let env = Env.bind_variable variable value ty env in
        eval_term env k
    | TOperator op -> eval_op env op
    | TThunk { lterm } ->
        let value, lty = eval_lterm env lterm in
        let ty = Ty.to_ty lty in
        (value, ty)
    | TLookup { lterm; index } ->
        let value, lty' = eval_lterm env lterm in
        let ty =
          match Ty.(elt @@ to_ty lty') with
          | None -> err "lookup: not a tuple type"
          | Some ty -> ty
        in
        let value = Value.get index value in
        (value, ty)
    | TLog { message; variables; k } ->
        let () = log "%s\n" message in
        let () =
          List.iter
            (fun variable ->
              let value, ty = Env.lookup variable env in
              let ty = Env.to_ty env ty in
              log "log: %a : %a = %a\n" Ast.TermIdent.pp variable Pp.pp_ty ty
                Value.pp value)
            variables
        in
        let () = log "\n" in
        eval_term env k
    | TFnCall { fn_name; ty_resolve; args } ->
        let args = List.map (fun term -> fst @@ eval_term env term) args in
        let fnident =
          match fn_name with
          | Either.Left fnident -> fnident
          | Right termident ->
              let value, _ = Env.lookup termident env in
              let e =
                match Value.as_function value with
                | None ->
                    err "id %a is not a function pointer: %a" Ast.TermIdent.pp
                      termident Value.pp value
                | Some (e, _) -> e
              in
              e
        in
        let fn_decl = Env.fn_declaration fnident env in
        let ty_resolve =
          List.map
            (fun ty ->
              let ty = Env.of_ty env ty in
              Env.to_ty env ty)
            ty_resolve
        in
        eval env fn_decl ty_resolve args

  and eval_lterm env = function
    | Ast.LLetPlus { variable; lterm; ands; term } ->
        let vvalue, vty = eval_lterm env lterm in
        let iprefix = Ty.view vty in
        let prefix = List.map fst iprefix in
        let ands =
          List.map
            (fun (variable, lterm) ->
              let value, aty = eval_lterm env lterm in
              let () =
                match Ty.lcstreq vty aty with
                | true -> ()
                | false -> err "let+: ands not same constructor"
              in
              (variable, (value, aty)))
            ands
        in
        let ands = (variable, (vvalue, vty)) :: ands in
        let values = List.map (fun (_, (v, _)) -> v) ands in
        let args =
          List.map
            (fun (name, (_v, lty)) ->
              let ty =
                match Ty.remove_prefix prefix (Ty.to_ty lty) with
                | Some ty -> ty
                | None ->
                    err "Wrong prefix prefix = [%a] - ty = \n"
                      (Format.pp_print_list Ast.TyDeclIdent.pp)
                      prefix
              in
              (name, ty))
            ands
        in

        let ret = ref None in
        let value =
          Value.mapn' prefix
            (fun values ->
              let env = Env.clear_variables env in
              let env =
                List.fold_left2
                  (fun env (indent, ty) value ->
                    Env.bind_variable indent value ty env)
                  env args values
              in
              let value, ty = eval_term env term in
              let () = if Option.is_none !ret then ret := Some ty in
              value)
            values
        in
        let ty_e =
          match !ret with None -> err "option is empty" | Some ty -> ty
        in
        let lty = Ty.lty iprefix ty_e in
        (value, lty)
    | LConstructor { ty = cstr; terms } ->
        let cstr_log = Env.cstr_log cstr env in
        let () = assert (List.compare_length_with terms cstr_log = 0) in
        let eterms, etypes = terms |> List.map (eval_term env) |> List.split in
        let ty_elt =
          match etypes with
          | [] -> err "Constructor with no args is forbidden"
          | t :: _ -> t
        in
        let ty = Ty.named_tuple cstr cstr_log ty_elt in
        let lty = Ty.lty [] ty in
        let terms = Array.of_list eterms in
        let v = Value.VArray { cstr; values = terms } in
        (v, lty)
    | LRange { ty; term } ->
        let value, t = eval_term env term in
        let lty = Env.range ty t env in
        (value, lty)
    | LCirc lterm ->
        let value, lty' = eval_lterm env lterm in
        let value = Value.circ value in
        let wrapper =
          match Ty.prefix lty' with
          | None -> err "Not a tuple type"
          | Some prefix -> prefix
        in
        let size = Env.cstr_log wrapper env in
        let lty = Ty.(named_tuple wrapper size (to_ty lty')) in
        let lty = Ty.lty [] lty in
        (value, lty)

  and eval env (fn : Ast.fn_declaration) ty_args args =
    let Ast.
          {
            fn_name = current_function;
            tyvars;
            parameters;
            return_type = _;
            body;
          } =
      fn
    in
    let types = List.combine tyvars ty_args in
    let env = Env.init_tyvariables types env in
    let env = Env.init_variables parameters args env in
    let env = { env with current_function = Some current_function } in
    eval_term env body
end

module ConstProp = struct
  module Functions = Map.Make (Ast.FnIdent)
  module Types = Map.Make (Ast.TyDeclIdent)

  module Value = struct
    type t =
      | VTerm of Ast.TermIdent.t
      | VBool of bool
      | VOp of t Ast.operator
      | VIndex of { cstr : Ast.TyDeclIdent.t; values : t Array.t; index : int }
      | VArray of { cstr : Ast.TyDeclIdent.t; values : t Array.t }
      | VFn of { fn_ident : Ast.FnIdent.t; tyresolve : Ast.ty list }

    let simplify = function
      | VTerm _ -> failwith ""
      | VBool _ -> failwith ""
      | VFn { fn_ident; tyresolve } ->
          let () = ignore (fn_ident, tyresolve) in
          failwith ""
      | VIndex { cstr; values; index } ->
          let () = ignore (cstr, values, index) in
          failwith ""
      | VOp _ -> failwith ""
      | VArray { cstr; values } ->
          let () = ignore (cstr, values) in
          failwith ""

    let rec to_ast = function
      | VTerm term -> Term.v term
      | VIndex { cstr = _; values; index } ->
          let value = values.(index) in
          let ast = to_ast value in
          ast
      | VBool true -> Term.true'
      | VBool false -> Term.false'
      | VFn { fn_ident; tyresolve } -> Term.vfn tyresolve fn_ident
      | VOp op -> to_ast_op op
      | VArray { cstr = c; values } ->
          let values = Array.map to_ast values in
          let values = Array.to_list values in
          LTerm.(Term.(funk (cstr c values)))

    and to_ast_op = function
      | Ast.ONot value -> Term.lnot (to_ast value)
      | Ast.OAnd (lhs, rhs) ->
          let lhs = to_ast lhs in
          let rhs = to_ast rhs in
          Term.(lhs land rhs)
      | Ast.OOr (lhs, rhs) ->
          let lhs = to_ast lhs in
          let rhs = to_ast rhs in
          Term.(lhs lor rhs)
      | Ast.OXor (lhs, rhs) ->
          let lhs = to_ast lhs in
          let rhs = to_ast rhs in
          Term.(lhs lxor rhs)
  end

  module Env = struct
    module Terms = Map.Make (Ast.TermIdent)

    type t = {
      functions : Ast.fn_declaration Functions.t;
      types : Ast.ty_declaration Types.t;
      terms : (Value.t * Ty.ty) Terms.t;
    }

    let bind ident value env =
      { env with terms = Terms.add ident value env.terms }

    let value' ident env =
      match Terms.find_opt ident env.terms with
      | Some (value, _) -> value
      | None -> Value.VTerm ident

    let term_substitute v env =
      match Terms.find_opt v env.terms with
      | Some (value, _) -> Value.to_ast value
      | None -> Term.v v
  end

  let eval_term env = function
    | Ast.TFalse -> Value.VBool false
    | TTrue -> Value.VBool true
    | TFn { fn_ident; tyresolve } -> VFn { fn_ident; tyresolve }
    | TVar term -> Env.value' term env
    | TLet { variable; term; k } ->
        let () = ignore (variable, term, k) in
        failwith ""
    (*        let value = eval_term env term in
        let env = Env.bind variable value env in
        eval_term env k*)
    | TLookup { lterm = _; index = _ } -> failwith ""
    | TThunk { lterm = _ } -> failwith ""
    | TLog { message = _; variables = _; k = _ } -> failwith ""
    | TOperator _ -> failwith ""
    | TFnCall { fn_name = _; ty_resolve = _; args = _ } -> failwith ""

  and lterm_eval _env = function
    | Ast.LLetPlus { variable = _; lterm = _; ands = _; term = _ } ->
        failwith ""
    | LConstructor { ty = _; terms = _ } -> failwith ""
    | LRange { ty = _; term = _ } -> failwith ""
    | LCirc _ -> failwith ""

  and op_eval _env = function
    | Ast.ONot _ -> failwith ""
    | OXor (_, _) -> failwith ""
    | OAnd (_, _) -> failwith ""
    | OOr (_, _) -> failwith ""

  let rec term env = function
    | (Ast.TFalse | TTrue | TFn _) as e -> e
    | TVar term -> Env.term_substitute term env
    | TLet { variable; term = term'; k } ->
        let () = ignore (variable, term', k) in
        failwith ""
    (*        let value = eval_term env term' in
        let env = Env.bind variable value env in
        let t = Value.to_ast value in
        Term.let_ variable t (term env k)*)
    | TLookup { lterm = lt; index } ->
        let ltvalue = lterm_eval env lt in
        let lterm = Value.to_ast ltvalue in
        LTerm.(Term.(lookup (range [] lterm) index))
    | TThunk { lterm = lt } ->
        let ltvalue = lterm_eval env lt in
        Value.to_ast ltvalue
    | TLog { message; variables; k } ->
        let value = eval_term env k in
        let k = Value.to_ast value in
        Term.log_ message variables k
    | TOperator _ -> failwith ""
    | TFnCall { fn_name = _; ty_resolve = _; args = _ } -> failwith ""

  and lterm env = function
    | Ast.LLetPlus { variable = _; lterm = _; ands = _; term = _ } ->
        failwith ""
    | LConstructor { ty = _; terms = _ } -> failwith ""
    | LRange { ty; term = t } ->
        let term = term env t in
        LTerm.range ty term
    | LCirc _ -> failwith ""

  and _op _env = function
    | Ast.ONot _ -> failwith ""
    | OXor (_, _) -> failwith ""
    | OAnd (_, _) -> failwith ""
    | OOr (_, _) -> failwith ""
end
