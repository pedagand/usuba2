let ty = Alcotest.testable Ua0.Ty.pp Ua0.Ty.equal

let () =
  let open Alcotest in
  run "passes"
    [
      ( "Ty",
        [
          test_case "ty" `Quick (fun () ->
              let a = "'a" in
              let env0, _a = Ua0.Pass.Idents.Env.(empty |> add_tyvar a) in
              let f a = Ua0.Ty.S.(fn ~tyvars:a [ v a ] (v a)) in
              Alcotest.(check @@ Alcotest.neg ty)
                "'a shouldn't be the one within the env" (f _a)
                (Ua0.Pass.Idents.ty env0 (f a)));
          test_case "ty" `Quick (fun () ->
              let a = "'a" in
              let env0, _a = Ua0.Pass.Idents.Env.(empty |> add_tyvar a) in
              let f a = Ua0.Ty.S.(fn ~tyvars:a [ v a ] (v a)) in
              Alcotest.(check @@ Alcotest.neg ty)
                "'a shouldn't be the one within the env" (f _a)
                (Ua0.Pass.Idents.ty env0 (f a)));
        ] );
    ]
