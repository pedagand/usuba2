open Alcotest
open Ua0

let alpha = Ident.TyIdent.fresh "'a"
let x = Ident.TermIdent.fresh "x"
let y = Ident.TermIdent.fresh "y"
let z = Ident.TermIdent.fresh "z"
let u = Ident.TermIdent.fresh "u"
let w = Ident.TermIdent.fresh "w"

(* let var_undef = Ident.TermIdent.fresh "_" *)
let f = Ident.FnIdent.fresh "f"
let _F = Ident.TyDeclIdent.fresh "F"
let _G = Ident.TyDeclIdent.fresh "G"
let _H = Ident.TyDeclIdent.fresh "H"

(* let g = Ident.FnIdent.fresh "g" *)
(* let fn_undef = Ident.FnIdent.fresh "_" *)

let ty_f =
  Ty.
    {
      tyvars = Some alpha;
      parameters = Ty.S.[ bool; v alpha ];
      return_type = Ty.S.v alpha;
    }

let def_f =
  Prog.{ fn_name = f; signature = ty_f; args = [ x; y ]; body = Synth (Var y) }

let env0 =
  let open Ua0.Typecheck.Env in
  empty |> add_variable x Ty.S.bool
  |> add_type { tyvar = alpha; name = _F; size = 4 }
  |> add_variable y Ty.S.(v alpha)
  |> add_type { tyvar = alpha; name = _G; size = 4 }
  |> add_type { tyvar = alpha; name = _H; size = 2 }
  |> add_variable z Ty.S.(apps [ _F; _G ] bool)
  |> add_variable u Ty.S.(apps [ _F; _G; _H ] (v alpha))
  |> add_variable w Ty.S.(_G @ bool)
  |> add_function def_f

type ctx = Env0

let ctx_to_string = function Env0 -> "env0"
let ctx_of = function Env0 -> env0
let ty = Alcotest.testable Ty.pp Ty.equal

let check_typesynth ctx tm expected_ty =
  let name =
    Format.asprintf "`%a` has type `%a` in %s" Term.pp_sterm tm Ty.pp
      expected_ty (ctx_to_string ctx)
  in
  check ty name (Ua0.Typecheck.typesynth (ctx_of ctx) tm) expected_ty

let fail_typesynth ctx tm =
  let name =
    Format.asprintf "`%a` is ill-typed in %s" Term.pp_sterm tm
      (ctx_to_string ctx)
  in
  match_raises name
    (function
      | Failure _ | Invalid_argument _ | Typecheck.Ill_typed -> true
      | _ -> false)
    (fun _ -> ignore (Ua0.Typecheck.typesynth (ctx_of ctx) tm))

let check_typecheck ctx tm ty =
  let name =
    Format.asprintf "`%a` accepts type `%a` in %s" Term.pp tm Ty.pp ty
      (ctx_to_string ctx)
  in
  check unit name (Ua0.Typecheck.typecheck (ctx_of ctx) ty tm) ()

let fail_typecheck ctx tm ty =
  let name =
    Format.asprintf "`%a : %a` is ill-typed in %s" Term.pp tm Ty.pp ty
      (ctx_to_string ctx)
  in
  match_raises name
    (function
      | Failure _ | Invalid_argument _ | Typecheck.Ill_typed -> true
      | _ -> false)
    (fun _ -> ignore (Ua0.Typecheck.typecheck (ctx_of ctx) ty tm))

let () =
  let open Scstr in
  run "typesynth"
    [
      ( "Var",
        [
          test_case "in-Bool" `Quick (fun () ->
              check_typesynth Env0 Term.(v x) Ty.S.bool);
          test_case "in-Var" `Quick (fun () ->
              check_typesynth Env0 Term.(v y) Ty.S.(v alpha));
          test_case "in-App" `Quick (fun () ->
              check_typesynth Env0 Term.(v z) Ty.S.(apps [ _F; _G ] bool));
        ] );
      ( "Fn",
        [
          test_case "in" `Quick (fun () ->
              check_typesynth Env0
                Term.(vfn f)
                Ty.S.(fn ~tyvars:(Some alpha) ty_f.parameters ty_f.return_type));
        ] );
      ( "Lookup",
        [
          test_case "in range" `Quick (fun () ->
              check_typesynth Env0 Term.((v z).%(2)) Ty.S.(_G @ bool));
          test_case "out of range" `Quick (fun () ->
              fail_typesynth Env0 Term.((v z).%(4)));
          test_case "not Naperian" `Quick (fun () ->
              fail_typesynth Env0 Term.((v x).%(2)));
        ] );
      ( "Operator",
        [
          test_case "xor" `Quick (fun () ->
              check_typesynth Env0 Term.(s (v x) lxor s (v x)) Ty.S.bool);
          test_case "no ad-hoc polymorphism" `Quick (fun () ->
              fail_typesynth Env0 Term.(s (v x) lxor s (v y)));
        ] );
      ( "FnCall",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0
                Term.(fn_call ~resolve:Ty.S.(v alpha) f [ s (v x); s (v y) ])
                Ty.S.(v alpha));
          test_case "well-typed instanciated" `Quick (fun () ->
              check_typesynth Env0
                Term.(fn_call ~resolve:Ty.S.bool f [ s (v x); s (v x) ])
                Ty.S.bool);
          test_case "no arguments" `Quick (fun () ->
              fail_typesynth Env0 Term.(fn_call ~resolve:Ty.S.(v alpha) f []));
          test_case "insufficiently applied" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.S.(v alpha) f [ s (v x) ]));
          test_case "wrong args" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.S.(v alpha) f [ s (v y); s (v x) ]));
          test_case "ill-typed instanciation" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.S.bool f [ s (v x); s (v y) ]));
        ] );
      ( "Ann",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0 Term.(ann true' Ty.S.bool) Ty.S.bool);
          test_case "ill-typed" `Quick (fun () ->
              fail_typesynth Env0 Term.(ann (s (vfn f)) Ty.S.bool));
        ] );
      ( "Circ",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0
                Term.(circ (v z))
                Ty.S.(apps [ _F; _F; _G ] bool));
          test_case "not applicative" `Quick (fun () ->
              fail_typesynth Env0 Term.(circ (v x)));
        ] );
      ( "Reindex",
        [
          test_case "reindex F / G over bool" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F ] [ _G ] (v z))
                Ty.S.(apps [ _G; _F ] bool));
          test_case "reindex F / G over H alpha" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F ] [ _G ] (v u))
                Ty.S.(apps [ _G; _F; _H ] (v alpha)));
          test_case "reindex F.G / H over alpha" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F; _G ] [ _H ] (v u))
                Ty.S.(apps [ _H; _F; _G ] (v alpha)));
          test_case "reindex F / G.H over alpha" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F ] [ _G; _H ] (v u))
                Ty.S.(apps [ _G; _H; _F ] (v alpha)));
          test_case "not applicative" `Quick (fun () ->
              fail_typesynth Env0 Term.(reindex [ _F ] [ _G ] (v x)));
          test_case "lhs mismatch" `Quick (fun () ->
              fail_typesynth Env0 Term.(reindex [ _G ] [ _G ] (v z)));
          test_case "rhs mismatch" `Quick (fun () ->
              fail_typesynth Env0 Term.(reindex [ _F ] [ _F ] (v z)));
        ] );
      ( "Lift",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0
                Term.(lift [ _F; _G ] (vfn f))
                Ty.S.(
                  fn ~tyvars:(Some alpha)
                    [ _F @ _G @ bool; _F @ _G @ v alpha ]
                    (_F @ _G @ v alpha)));
          test_case "not applicative" `Quick (fun () ->
              fail_typesynth Env0 Term.(circ (v x)));
        ] );
      (*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
      ( "True/False",
        [
          test_case "true well-typed" `Quick (fun () ->
              check_typecheck Env0 Term.true' Ty.S.bool);
          test_case "false well-typed" `Quick (fun () ->
              check_typecheck Env0 Term.false' Ty.S.bool);
          test_case "ill-typed" `Quick (fun () ->
              fail_typecheck Env0 Term.true' Ty.S.(v alpha));
        ] );
      ( "Constructor",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typecheck Env0
                Term.(cstr _F [ true'; false'; true'; true' ])
                Ty.S.(_F @ bool));
          test_case "ill-typed" `Quick (fun () ->
              fail_typecheck Env0
                Term.(cstr _F [ true'; false'; true'; true' ])
                Ty.S.(v alpha));
          test_case "arity checked" `Quick (fun () ->
              fail_typecheck Env0
                Term.(cstr _F [ false'; true'; true' ])
                Ty.S.(_F @ bool));
        ] );
      ( "Let",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typecheck Env0
                Term.(
                  let' "a" (s (v x) lxor s (v x)) (fun a -> s (s a land s a)))
                Ty.S.bool);
          test_case "ill-typed argument" `Quick (fun () ->
              fail_typecheck Env0
                Term.(
                  let' "a" (s (v x) lxor s (v y)) (fun a -> s (s a land s a)))
                Ty.S.bool);
          test_case "ill-typed application" `Quick (fun () ->
              fail_typecheck Env0
                Term.(let' "a" (v y) (fun a -> s (s a land s a)))
                Ty.S.bool);
          test_case "rejecting wrong type" `Quick (fun () ->
              fail_typecheck Env0
                Term.(let' "a" (v y) (fun _a -> s (v x)))
                Ty.S.(v alpha));
        ] );
      ( "Let+",
        [
          test_case "well-typed functor" `Quick (fun () ->
              check_typecheck Env0
                Term.(let_plus "a" (v z) [] (fun _a _ -> true'))
                Ty.S.(_F @ bool));
          test_case "well-typed monoidal functor" `Quick (fun () ->
              check_typecheck Env0
                Term.(
                  let_plus "a" (v z)
                    [ ("b", v u); ("c", v z) ]
                    (fun _a bs ->
                      match bs with [ _x; y ] -> s (v y) | _ -> assert false))
                Ty.S.(apps [ _F; _G ] bool));
          test_case "well-typed monoidal functor" `Quick (fun () ->
              check_typecheck Env0
                Term.(
                  let_plus "a" (v z)
                    [ ("b", v u); ("c", v z) ]
                    (fun _a bs ->
                      match bs with [ x; _y ] -> s (v x) | _ -> assert false))
                Ty.S.(apps [ _F; _G; _H ] (v alpha)));
          test_case "incompatible arg / product monoidal" `Quick (fun () ->
              fail_typecheck Env0
                Term.(let_plus "a" (v z) [ ("b", v w) ] (fun _a _ -> true'))
                Ty.S.(_F @ bool));
          test_case "incompatible arg / product monoidal (dual)" `Quick
            (fun () ->
              fail_typecheck Env0
                Term.(let_plus "a" (v z) [ ("b", v w) ] (fun _a _ -> true'))
                Ty.S.(_G @ bool));
          test_case "incompatible product / product monoidal" `Quick (fun () ->
              fail_typecheck Env0
                Term.(
                  let_plus "a" (v z)
                    [ ("b", v z); ("c", v w) ]
                    (fun _a _ -> true'))
                Ty.S.(_F @ bool));
        ] );
    ]
