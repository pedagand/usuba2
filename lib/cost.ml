(*module Symbolical = struct
  type t = Var of Ident.TermIdent.t | Op of t Operator.t

  let lnot e = Op (Operator.Not e)
  let ( land ) lhs rhs = Op (Operator.And (lhs, rhs))
  let ( lor ) lhs rhs = Op (Operator.Or (lhs, rhs))
  let ( lxor ) lhs rhs = Op (Operator.Xor (lhs, rhs))
end

module type Boolean = sig
  type t

  val lnot : t -> t
  val ( land ) : t -> t -> t
  val ( lor ) : t -> t -> t
  val ( lxor ) : t -> t -> t
end

module Make (B : Boolean) = struct
  type t =
    | Bool of B.t
    | Array of t Array.t
    | Function of { origin : string; value : t list -> int * t }

  let get i = function Array array -> array.(i) | _ -> assert false

  let tabulate size f =
    let array = Array.init size f in
    Array array

  let as_array = function Array array -> array | _ -> assert false
  let not = function Bool e -> Bool (B.lnot e) | _ -> assert false

  let ( lxor ) lhs rhs =
    match (lhs, rhs) with
    | Bool lhs, Bool rhs -> Bool (B.( lxor ) lhs rhs)
    | _, _ -> assert false

  let ( land ) lhs rhs =
    match (lhs, rhs) with
    | Bool lhs, Bool rhs -> Bool (B.( land ) lhs rhs)
    | _, _ -> assert false

  let ( lor ) lhs rhs =
    match (lhs, rhs) with
    | Bool lhs, Bool rhs -> Bool (B.( lor ) lhs rhs)
    | _, _ -> assert false

  let circ = function
    | Array values as cir0 ->
        let cardinal = Array.length values in
        let circs =
          Array.init (cardinal - 1) @@ fun i ->
          let i = i + 1 in
          let value =
            Array.init cardinal (fun n ->
                let index = (cardinal + (n - i)) mod cardinal in
                values.(index))
          in
          Array value
        in
        Array (Array.append [| cir0 |] circs)
    | _ -> assert false

  let rec mapn' level f values =
    (*    let () = Format.eprintf "level = %u\n" level in*)
    match level with
    | 0 -> f values
    | level ->
        (*        let () =
          List.iter (fun value -> Format.eprintf "%a\n" pp value) values
        in*)
        let first = List.nth values 0 in
        let length = first |> as_array |> Array.length in
        let array = Array.init length (fun i -> mapn'' level i f values) in
        Array array

  and mapn'' level i f values =
    let values = List.map (fun value -> get i value) values in
    mapn' (level - 1) f values

  module type S = sig
    val n : int
  end

  module type SNaperian = sig
    type idx

    val tabulate : (idx -> t) -> t
    val lookup : t -> idx -> t
  end

  module Naperian (S : S) : SNaperian = struct
    type idx = int

    let tabulate f = tabulate S.n f
    let lookup s i = as_array s |> Fun.flip Array.get i
  end

  module NaperianCompose (F : SNaperian) (G : SNaperian) : SNaperian = struct
    type idx = F.idx * G.idx

    let lookup fgs (i, j) = G.lookup (F.lookup fgs i) j
    let tabulate f = F.tabulate (fun i -> G.tabulate (fun j -> f (i, j)))
  end

  let naperian n =
    (module Naperian (struct
      let n = n
    end) : SNaperian)

  let naperian_compose f g =
    (module NaperianCompose ((val f : SNaperian)) ((val g : SNaperian))
    : SNaperian)

  (** [L R 'a -> R L 'a] *)
  let reindex_lr lhs rhs value =
    let module L = (val lhs : SNaperian) in
    let module R = (val rhs : SNaperian) in
    R.tabulate (fun c -> L.tabulate (fun r -> R.lookup (L.lookup value r) c))

  let reduce_op o =
    let o =
      match o with
      | Operator.Not v -> not v
      | Xor (l, r) -> l lxor r
      | And (l, r) -> l land r
      | Or (l, r) -> l lor r
    in
    (1, o)
end

module Val = Make (Symbolical)

let err fmt = Format.kasprintf failwith fmt
let log fmt = Format.eprintf fmt
let uncons l = match l with [] -> None | x :: xs -> Some (x, xs)

module Env = struct
  module Functions = Map.Make (Ident.FnIdent)
  module Types = Map.Make (Ident.TyDeclIdent)
  module Variables = Map.Make (Ident.TermIdent)
  module TyVariables = Map.Make (Ident.TyIdent)

  type t = {
    current_function : Ident.FnIdent.t option;
    types : Prog.tydecl Types.t;
    functions : (Val.t list -> int * Val.t) Functions.t;
    variables : Val.t Variables.t;
    type_variables : Prog.ty TyVariables.t;
  }

  let init =
    {
      current_function = None;
      functions = Functions.empty;
      types = Types.empty;
      variables = Variables.empty;
      type_variables = TyVariables.empty;
    }

  let pp format env =
    let () =
      Variables.iter
        (fun variable _ ->
          Format.fprintf format "%a - " Ident.TermIdent.pp variable)
        env.variables
    in
    ()

  let add_function (fn : Ident.FnIdent.t) f env =
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

  let naperian cstr env = Val.naperian (cstr_log cstr env)

  let naperian_compose lhs rhs env =
    Val.naperian_compose (naperian lhs env) (naperian rhs env)

  let naperians cstrs env =
    let cstr, cstrs = Option.get @@ uncons cstrs in
    let n0 = naperian cstr env in
    List.fold_left
      (fun nap cstr -> Val.naperian_compose nap (naperian cstr env))
      n0 cstrs

  let clear_variables env = { env with variables = Variables.empty }
  let clear_tyvariables env = { env with type_variables = TyVariables.empty }

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

let rec eval_sterm env = function
  | Term.Var variable -> (0, Env.lookup variable env)
  | Fn { fn_ident } ->
      let origin = Format.asprintf "%a" Ident.FnIdent.pp fn_ident in
      let value = Env.fn_declaration fn_ident env in
      (0, Val.Function { origin; value })
  | Lookup { lterm; index } ->
      let cost, value = eval_sterm env lterm in
      let value = Val.get index value in
      (cost, value)
  | Reindex { lhs; rhs; lterm } ->
      let nap_lhs = Env.naperians lhs env in
      let nap_rhs = Env.naperians rhs env in
      let cost, value = eval_sterm env lterm in
      let value = Val.reindex_lr nap_lhs nap_rhs value in
      (cost, value)
  | Circ sterm ->
      let cost, value = eval_sterm env sterm in
      let value = Val.circ value in
      (cost, value)
  | Lift { tys; func } ->
      let cost, value = eval_sterm env func in
      let origin, value =
        match value with
        | Val.Function f -> (f.origin, f.value)
        | Bool _ | Array _ -> assert false
      in
      let value = Val.mapn' (List.length tys) value in
      let origin =
        Format.asprintf "lift[%a](%s)"
          (Format.pp_print_list
             ~pp_sep:(fun format () -> Format.fprintf format ", ")
             Ident.TyDeclIdent.pp)
          tys origin
      in
      (cost, Value.VFunction { origin; value })
  | FnCall { fn; args; dicts; _ } ->
      let cost, fn = eval_sterm env fn in
      let f = Value.as_function fn in
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
  | Term.False -> (0, Value.VBool false)
  | True -> (0, Value.VBool true)
  | Constructor { terms; _ } ->
      let cost, vs =
        List.fold_left_map
          (fun cost term ->
            let c, t = eval_cterm env term in
            (cost + c, t))
          0 terms
      in
      let v = Value.VArray (Array.of_list vs) in
      (cost, v)
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
  env.Env.functions*)
