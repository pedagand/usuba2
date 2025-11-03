open Alcotest
open Ua0

let ty = Alcotest.testable Prog.pp_ty Ty.equal
let tydecl = Alcotest.testable Ident.TyDeclIdent.pp Ident.TyDeclIdent.equal
let alpha = Ident.TyIdent.fresh "'a"
let beta = Ident.TyIdent.fresh "'b"
let _F = Ident.TyDeclIdent.fresh "F"
let _G = Ident.TyDeclIdent.fresh "G"
let _H = Ident.TyDeclIdent.fresh "H"
let ty1 = Ty.S.(apps [ _F; _G; _H ] (v alpha))

let check_equal ty1 ty2 expected =
  let name =
    Format.asprintf "equal %a %a is %b" Prog.pp_ty ty1 Prog.pp_ty ty2 expected
  in
  check bool name (Ty.equal ty1 ty2) expected

let () =
  run "util"
    [
      ( "Ty",
        [
          test_case "equal" `Quick (fun () ->
              check_equal Ty.S.bool Ty.S.bool true);
          test_case "equal" `Quick (fun () ->
              check_equal Ty.S.(v alpha) Ty.S.(v alpha) true);
          test_case "equal" `Quick (fun () ->
              check_equal
                Ty.S.(apps [ _F; _G ] (v alpha))
                Ty.S.(_F @ _G @ v alpha)
                true);
          test_case "equal" `Quick (fun () ->
              check_equal Ty.S.(apps [ _G; _H ] bool) Ty.S.(_G @ _H @ bool) true);
          test_case "equal" `Quick (fun () ->
              check_equal
                Ty.S.(fn ~tyvars:(Some alpha) [ v alpha ] (v alpha))
                Ty.S.(fn ~tyvars:(Some beta) [ v beta ] (v beta))
                true);
          test_case "not equal" `Quick (fun () ->
              check_equal Ty.S.(v alpha) Ty.S.(v beta) false);
          test_case "not equal" `Quick (fun () ->
              check_equal Ty.S.(bool) Ty.S.(v alpha) false);
          test_case "to_spine" `Quick (fun () ->
              check
                (pair (list tydecl) ty)
                "to_spine (F (G (H alpha))) = [F; G; H], alpha"
                (let r = Ua0.Ty.to_spine ty1 in
                 (r.names, r.bty))
                ([ _F; _G; _H ], Ty.S.(v alpha)));
          test_case "from_spine" `Quick (fun () ->
              check ty "from_spine ([F; G; H], alpha) = F (G (H alpha))"
                (Ua0.Ty.from_spine
                   { names = [ _F; _G; _H ]; bty = Ty.S.(v alpha) })
                ty1);
          test_case "merge" `Quick (fun () ->
              check
                (pair (list tydecl) (list ty))
                "merge ([F; G; H], [alpha; bool]) ([F], beta)"
                (let r =
                   Ty.(
                     merge
                       { names = [ _F; _G; _H ]; btys = S.[ v alpha; bool ] }
                       { names = [ _F ]; bty = S.(v beta) })
                 in
                 (r.names, r.btys))
                ( [ _F ],
                  [
                    Ty.S.(apps [ _G; _H ] (v alpha));
                    Ty.S.(apps [ _G; _H ] bool);
                    Ty.S.(v beta);
                  ] ));
        ] );
    ]
