open Alcotest
open Ua0

let alpha = Prog.TyIdent.fresh "'a"
let x = Prog.TermIdent.fresh "x"
let y = Prog.TermIdent.fresh "y"
let z = Prog.TermIdent.fresh "z"
let u = Prog.TermIdent.fresh "u"
let w = Prog.TermIdent.fresh "w"
let var_undef = Prog.TermIdent.fresh "_"
let f = Prog.FnIdent.fresh "f"
let _F = Prog.TyDeclIdent.fresh "F"
let _G = Prog.TyDeclIdent.fresh "G"
let _H = Prog.TyDeclIdent.fresh "H"

(* let g = Prog.FnIdent.fresh "g" *)
let fn_undef = Prog.FnIdent.fresh "_"

let ty_f =
  Ty.
    {
      tyvars = Some alpha;
      parameters = [ Bool; Var alpha ];
      return_type = Var alpha;
    }

let def_f =
  Prog.{ fn_name = f; signature = ty_f; args = [ x; y ]; body = Synth (Var y) }

let env0 =
  let open Ua0.Typecheck.Env in
  empty |> add_variable x Ty.Bool
  |> add_type { tyvar = alpha; name = _F; size = 4 }
  |> add_variable y Ty.(Var alpha)
  |> add_type { tyvar = alpha; name = _G; size = 4 }
  |> add_type { tyvar = alpha; name = _H; size = 2 }
  |> add_variable z (App { name = _F; ty = App { name = _G; ty = Bool } })
  |> add_variable u
       (App
          {
            name = _F;
            ty = App { name = _G; ty = App { name = _H; ty = Var alpha } };
          })
  |> add_variable w (App { name = _G; ty = Bool })
  |> add_function def_f

type ctx = Env0

let ctx_to_string = function Env0 -> "env0"
let ctx_of = function Env0 -> env0
let ty = Alcotest.testable Prog.pp_ty Util.Ty.equal

let check_typesynth ctx tm expected_ty =
  let name =
    Format.asprintf "`%a` has type `%a` in %s" Prog.pp_sterm tm Prog.pp_ty
      expected_ty (ctx_to_string ctx)
  in
  check ty name (Ua0.Typecheck.typesynth (ctx_of ctx) tm) expected_ty

let fail_typesynth ctx tm =
  let name =
    Format.asprintf "`%a` is ill-typed in %s" Prog.pp_sterm tm
      (ctx_to_string ctx)
  in
  match_raises name
    (function
      | Failure _ | Invalid_argument _ | Typecheck.IllTyped -> true | _ -> false)
    (fun _ -> ignore (Ua0.Typecheck.typesynth (ctx_of ctx) tm))

let check_typecheck ctx tm ty =
  let name =
    Format.asprintf "`%a` accepts type `%a` in %s" Prog.pp_cterm tm Prog.pp_ty
      ty (ctx_to_string ctx)
  in
  check unit name (Ua0.Typecheck.typecheck (ctx_of ctx) ty tm) ()

let fail_typecheck ctx tm ty =
  let name =
    Format.asprintf "`%a : %a` is ill-typed in %s" Prog.pp_cterm tm Prog.pp_ty
      ty (ctx_to_string ctx)
  in
  match_raises name
    (function
      | Failure _ | Invalid_argument _ | Typecheck.IllTyped -> true | _ -> false)
    (fun _ -> ignore (Ua0.Typecheck.typecheck (ctx_of ctx) ty tm))

let () =
  let open Scstr in
  run "typesynth"
    [
      ( "Var",
        [
          test_case "in-Bool" `Quick (fun () ->
              check_typesynth Env0 Term.(v x) Ty.bool);
          test_case "in-Var" `Quick (fun () ->
              check_typesynth Env0 Term.(v y) Ty.(v alpha));
          test_case "in-App" `Quick (fun () ->
              check_typesynth Env0 Term.(v z) Ty.(_F @ _G @ bool));
          test_case "unbound" `Quick (fun () ->
              fail_typesynth Env0 Term.(v var_undef));
        ] );
      ( "Fn",
        [
          test_case "in" `Quick (fun () ->
              check_typesynth Env0
                Term.(vfn f)
                Ty.(fn ~tyvars:alpha ty_f.parameters ty_f.return_type));
          test_case "unbound" `Quick (fun () ->
              fail_typesynth Env0 Term.(vfn fn_undef));
        ] );
      ( "Lookup",
        [
          test_case "in range" `Quick (fun () ->
              check_typesynth Env0 Term.((v z).%(2)) Ty.(_G @ bool));
          test_case "out of range" `Quick (fun () ->
              fail_typesynth Env0 Term.((v z).%(4)));
          test_case "not Naperian" `Quick (fun () ->
              fail_typesynth Env0 Term.((v x).%(2)));
        ] );
      ( "Operator",
        [
          test_case "xor" `Quick (fun () ->
              check_typesynth Env0 Term.(s (v x) lxor s (v x)) Ty.bool);
          test_case "no ad-hoc polymorphism" `Quick (fun () ->
              fail_typesynth Env0 Term.(s (v x) lxor s (v y)));
        ] );
      ( "FnCall",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0
                Term.(fn_call ~resolve:Ty.(v alpha) f [ s (v x); s (v y) ])
                Ty.(v alpha));
          test_case "well-typed instanciated" `Quick (fun () ->
              check_typesynth Env0
                Term.(fn_call ~resolve:Ty.bool f [ s (v x); s (v x) ])
                Ty.bool);
          test_case "no arguments" `Quick (fun () ->
              fail_typesynth Env0 Term.(fn_call ~resolve:Ty.(v alpha) f []));
          test_case "insufficiently applied" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.(v alpha) f [ s (v x) ]));
          test_case "wrong args" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.(v alpha) f [ s (v y); s (v x) ]));
          test_case "ill-typed instanciation" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.bool f [ s (v x); s (v y) ]));
        ] );
      ( "Ann",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0 Term.(ann true' Ty.bool) Ty.bool);
          test_case "ill-typed" `Quick (fun () ->
              fail_typesynth Env0 Term.(ann (s (vfn fn_undef)) Ty.bool));
        ] );
      ( "Circ",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0 Term.(circ (v z)) Ty.(_F @ _F @ _G @ bool));
          test_case "not applicative" `Quick (fun () ->
              fail_typesynth Env0 Term.(circ (v x)));
        ] );
      ( "Reindex",
        [
          test_case "reindex F / G over bool" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F ] [ _G ] (v z))
                Ty.(_G @ _F @ bool));
          test_case "reindex F / G over H alpha" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F ] [ _G ] (v u))
                Ty.(_G @ _F @ _H @ v alpha));
          test_case "reindex F.G / H over alpha" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F; _G ] [ _H ] (v u))
                Ty.(_H @ _F @ _G @ v alpha));
          test_case "reindex F / G.H over alpha" `Quick (fun () ->
              check_typesynth Env0
                Term.(reindex [ _F ] [ _G; _H ] (v u))
                Ty.(_G @ _H @ _F @ v alpha));
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
                Ty.(
                  fn ~tyvars:alpha
                    [ _F @ _G @ bool; _F @ _G @ v alpha ]
                    (_F @ _G @ v alpha)));
          test_case "not applicative" `Quick (fun () ->
              fail_typesynth Env0 Term.(circ (v x)));
        ] );
      (*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
      ( "True/False",
        [
          test_case "true well-typed" `Quick (fun () ->
              check_typecheck Env0 Term.true' Ty.bool);
          test_case "false well-typed" `Quick (fun () ->
              check_typecheck Env0 Term.false' Ty.bool);
          test_case "ill-typed" `Quick (fun () ->
              fail_typecheck Env0 Term.true' Ty.(v alpha));
        ] );
      ( "Constructor",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typecheck Env0
                Term.(cstr _F [ true'; false'; true'; true' ])
                Ty.(_F @ bool));
          test_case "ill-typed" `Quick (fun () ->
              fail_typecheck Env0
                Term.(cstr _F [ true'; false'; true'; true' ])
                Ty.(v alpha));
          test_case "arity checked" `Quick (fun () ->
              fail_typecheck Env0
                Term.(cstr _F [ false'; true'; true' ])
                Ty.(_F @ bool));
        ] );
      ( "Let",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typecheck Env0
                Term.(
                  let' "a" (s (v x) lxor s (v x)) (fun a -> s (s a land s a)))
                Ty.(bool));
          test_case "ill-typed argument" `Quick (fun () ->
              fail_typecheck Env0
                Term.(
                  let' "a" (s (v x) lxor s (v y)) (fun a -> s (s a land s a)))
                Ty.(bool));
          test_case "ill-typed application" `Quick (fun () ->
              fail_typecheck Env0
                Term.(let' "a" (v y) (fun a -> s (s a land s a)))
                Ty.(bool));
          test_case "rejecting wrong type" `Quick (fun () ->
              fail_typecheck Env0
                Term.(let' "a" (v y) (fun _a -> s (v x)))
                Ty.(v alpha));
        ] );
      ( "Let+",
        [
          test_case "well-typed functor" `Quick (fun () ->
              check_typecheck Env0
                Term.(let_plus "a" (v z) [] (fun _a _ -> true'))
                Ty.(_F @ bool));
          test_case "well-typed monoidal functor" `Quick (fun () ->
              check_typecheck Env0
                Term.(
                  let_plus "a" (v z)
                    [ ("b", v u); ("c", v z) ]
                    (fun _a bs ->
                      match bs with [ _x; y ] -> s (v y) | _ -> assert false))
                Ty.(_F @ _G @ bool));
          test_case "well-typed monoidal functor" `Quick (fun () ->
              check_typecheck Env0
                Term.(
                  let_plus "a" (v z)
                    [ ("b", v u); ("c", v z) ]
                    (fun _a bs ->
                      match bs with [ x; _y ] -> s (v x) | _ -> assert false))
                Ty.(_F @ _G @ _H @ v alpha));
          test_case "incompatible arg / product monoidal" `Quick (fun () ->
              fail_typecheck Env0
                Term.(let_plus "a" (v z) [ ("b", v w) ] (fun _a _ -> true'))
                Ty.(_F @ bool));
          test_case "incompatible arg / product monoidal (dual)" `Quick
            (fun () ->
              fail_typecheck Env0
                Term.(let_plus "a" (v z) [ ("b", v w) ] (fun _a _ -> true'))
                Ty.(_G @ bool));
          test_case "incompatible product / product monoidal" `Quick (fun () ->
              fail_typecheck Env0
                Term.(
                  let_plus "a" (v z)
                    [ ("b", v z); ("c", v w) ]
                    (fun _a _ -> true'))
                Ty.(_F @ bool));
        ] );
    ]
