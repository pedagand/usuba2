open Alcotest
open Ua0

let alpha = Ast.TyIdent.fresh "'a"
let x = Ast.TermIdent.fresh "x"
let y = Ast.TermIdent.fresh "y"
let z = Ast.TermIdent.fresh "z"
let var_undef = Ast.TermIdent.fresh "_"
let f = Ast.FnIdent.fresh "f"
let _F = Ast.TyDeclIdent.fresh "F"
let _G = Ast.TyDeclIdent.fresh "G"

(* let g = Ast.FnIdent.fresh "g" *)
let fn_undef = Ast.FnIdent.fresh "_"

let ty_f =
  Ast.
    {
      fn_name = f;
      signature =
        {
          tyvars = Some alpha;
          parameters = [ Ast.Ty.Bool; Ast.Ty.Var alpha ];
          return_type = Ast.Ty.Var alpha;
        };
      args = [ x; y ];
      body = Synth (Var y);
    }

let env0 =
  let open Ua0.Typecheck.Env in
  empty |> add_variable x Ast.Ty.Bool
  |> add_variable y Ast.Ty.(Var alpha)
  |> add_variable z (App { name = _F; ty = App { name = _G; ty = Bool } })
  |> add_function ty_f

type ctx = Env0

let ctx_to_string = function Env0 -> "env0"
let ctx_of = function Env0 -> env0
let ty = Alcotest.testable Ua0.Pp.pp_ty Util.Ty.equal

let check_typesynth ctx tm expected_ty =
  let name =
    Format.asprintf "`%a` has type `%a` in %s" Pp.pp_sterm tm Pp.pp_ty
      expected_ty (ctx_to_string ctx)
  in
  check ty name (Ua0.Typecheck.typesynth (ctx_of ctx) tm) expected_ty

let fail_typesynth ctx tm =
  let name =
    Format.asprintf "`%a` is ill-typed in %s" Pp.pp_sterm tm (ctx_to_string ctx)
  in
  match_raises name
    (function
      | Failure _ | Invalid_argument _ | Typecheck.IllTyped -> true | _ -> false)
    (fun _ -> ignore (Ua0.Typecheck.typesynth (ctx_of ctx) tm))

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
                Ty.(
                  fn ~tyvars:alpha ty_f.signature.parameters
                    ty_f.signature.return_type));
          test_case "unbound" `Quick (fun () ->
              fail_typesynth Env0 Term.(vfn fn_undef));
        ] );
      ( "Lookup",
        [
          test_case "in range" `Quick (fun () ->
              check_typesynth Env0 Term.((v z).%(2)) Ty.(_G @ bool));
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
          test_case "no arguments" `Quick (fun () ->
              fail_typesynth Env0 Term.(fn_call ~resolve:Ty.(v alpha) f []));
          test_case "insufficiently applied" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.(v alpha) f [ s (v x) ]));
          test_case "wrong args" `Quick (fun () ->
              fail_typesynth Env0
                Term.(fn_call ~resolve:Ty.(v alpha) f [ s (v y); s (v x) ]));
        ] );
      ( "Ann",
        [
          test_case "well-typed" `Quick (fun () ->
              check_typesynth Env0 Term.(ann true' Ty.bool) Ty.bool);
          test_case "ill-typed" `Quick (fun () ->
              fail_typesynth Env0 Term.(ann (s (vfn fn_undef)) Ty.bool));
        ] );
    ]
