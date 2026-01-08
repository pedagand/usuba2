let err fmt = Format.kasprintf failwith fmt
let log fmt = Format.eprintf fmt
let uncons l = match l with [] -> None | x :: xs -> Some (x, xs)

module Env = struct
  module Functions = Map.Make (Ident.FnIdent)
  module Types = Map.Make (Ident.TyDeclIdent)
  module Variables = Map.Make (Ident.TermIdent)
  module TyVariables = Map.Make (Ident.TyIdent)

  type t = {
    types : Prog.tydecl Types.t;
    functions : (Value.t list -> Value.t) Functions.t;
    variables : Value.t Variables.t;
  }

  let init =
    {
      functions = Functions.empty;
      types = Types.empty;
      variables = Variables.empty;
    }

  let pp format env =
    let () =
      Variables.iter
        (fun variable _ ->
          Format.fprintf format "%a - " Ident.TermIdent.pp variable)
        env.variables
    in
    ()

  let add_function (fn : Ident.FnIdent.t) (f : Value.t list -> Value.t) env =
    { env with functions = Functions.add fn f env.functions }

  let add_types (ty : Prog.tydecl) env =
    { env with types = Types.add ty.name ty env.types }

  let bind_variable variable value env =
    { env with variables = Variables.add variable value env.variables }

  let type_declaration name env =
    match Types.find_opt name env.types with
    | None -> err "type %a not in env" Ident.TyDeclIdent.pp name
    | Some e -> e

  let fn_declaration name env =
    match Functions.find_opt name env.functions with
    | None -> err "function %a not in env" Ident.FnIdent.pp name
    | Some e -> e

  let cstr_log name env =
    let decl = type_declaration name env in
    decl.size

  let naperian cstr env = Value.naperian (cstr_log cstr env)

  let naperian_compose lhs rhs env =
    Value.naperian_compose (naperian lhs env) (naperian rhs env)

  let naperians cstrs env =
    let cstr, cstrs = Option.get @@ uncons cstrs in
    let n0 = naperian cstr env in
    List.fold_left
      (fun nap cstr -> Value.naperian_compose nap (naperian cstr env))
      n0 cstrs

  let clear_variables env = { env with variables = Variables.empty }

  let bind_variables parameters values env =
    let env = clear_variables env in
    List.fold_left2
      (fun env var value -> bind_variable var value env)
      env parameters values

  let lookup variable env =
    match Variables.find_opt variable env.variables with
    | Some e -> e
    | None ->
        err "variable %a not in env\nenv = %a\n" Ident.TermIdent.pp variable pp
          env

  let let_variables_of_variables variables =
    match variables with
    | [] -> failwith "try lifting with no arguments"
    | x :: xs -> (x, xs)
end

let reduce_op = function
  | Operator.Not v -> Value.not v
  | Xor (l, r) -> Value.(l lxor r)
  | And (l, r) -> Value.(l land r)
  | Or (l, r) -> Value.(l lor r)

let rec eval_sterm env = function
  | Term.Var variable -> Env.lookup variable env
  | Fn { fn_ident } ->
      let origin = Format.asprintf "%a" Ident.FnIdent.pp fn_ident in
      let value = Env.fn_declaration fn_ident env in
      Value.VFunction { origin; value }
  | Lookup { lterm; index } ->
      let value = eval_sterm env lterm in
      let value = Value.get index value in
      value
  | Reindex { lhs; rhs; lterm } ->
      let nap_lhs = Env.naperians lhs env in
      let nap_rhs = Env.naperians rhs env in
      let value = eval_sterm env lterm in
      let value = Value.reindex_lr nap_lhs nap_rhs value in
      value
  | Circ sterm ->
      let value = eval_sterm env sterm in
      let value = Value.circ value in
      value
  | Lift { tys; func } ->
      let value = eval_sterm env func in
      let origin, value =
        match value with
        | Value.VFunction f -> (f.origin, f.value)
        | VBool _ | VArray _ -> assert false
      in
      let value = Value.mapn' (List.length tys) value in
      let origin =
        Format.asprintf "lift[%a](%s)"
          (Format.pp_print_list
             ~pp_sep:(fun format () -> Format.fprintf format ", ")
             Ident.TyDeclIdent.pp)
          tys origin
      in
      Value.VFunction { origin; value }
  | FnCall { fn; args; dicts; _ } ->
      let f = Value.as_function (eval_sterm env fn) in
      let args = List.map (eval_cterm env) args in
      let dicts = List.map (eval_cterm env) dicts in
      (* HACK: pass dicts values with regulars arguments *)
      f (dicts @ args)
  | Operator operator ->
      let _, r =
        Operator.traverse
          (fun env term -> (env, eval_cterm env term))
          env operator
      in
      reduce_op r
  | Ann (cterm, _) -> eval_cterm env cterm

and eval_cterm env = function
  | Term.False -> Value.VBool false
  | True -> Value.VBool true
  | Constructor { terms; _ } ->
      let vs = List.map (eval_cterm env) terms in
      let v = Value.VArray (Array.of_list vs) in
      v
  | Let { variable; term; k } ->
      let value = eval_sterm env term in
      let env = Env.bind_variable variable value env in
      eval_cterm env k
  | LetPlus { variable; prefix; lterm; ands; term } ->
      let vvalue = eval_sterm env lterm in
      let ands =
        List.map
          (fun (variable, lterm) ->
            let value = eval_sterm env lterm in
            (variable, value))
          ands
      in
      let ands = (variable, vvalue) :: ands in
      let args = List.map (fun (a, _) -> a) ands in
      let values = List.map (fun (_, v) -> v) ands in
      let level = List.length prefix in
      Value.mapn' level
        (fun values ->
          let env =
            List.fold_left2
              (fun env indent value -> Env.bind_variable indent value env)
              env args values
          in
          eval_cterm env term)
        values
  | Log { message; variables; k } ->
      let () = ignore (message, variables) in
      eval_cterm env k
  | Synth sterm -> eval_sterm env sterm

let eval_node env (fn : Prog.fndecl) vals =
  (* HACK: pass dicts values with regulars arguments (part2) *)
  let env = Env.bind_variables (fn.ops @ fn.args) vals env in
  eval_cterm env fn.body

let eval_node env = function
  | Prog.NTy tydel -> Env.add_types tydel env
  | Prog.NFun fn_decl ->
      Env.add_function fn_decl.fn_name (eval_node env fn_decl) env

let eval prog =
  let env = List.fold_left eval_node Env.init prog in
  env.Env.functions
