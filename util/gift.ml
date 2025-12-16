module Make (B : Ua0.Value.Boolean with type t = bool) = struct
  module Value = Ua0.Value.Make (B)

  module RowsCols = struct
    let tabulate f =
      Value.tabulate 4 @@ fun c ->
      Value.tabulate 4 @@ fun r -> f (r, c)

    let lookup rc (r, c) =
      let value = Value.get c rc in
      Value.get r value
  end

  let round_constants =
    List.map (Bits.of_int ~pad:16)
      [
        0x80_01L;
        0x80_03L;
        0x80_07L;
        0x80_0FL;
        0x80_1FL;
        0x80_3EL;
        0x80_3DL;
        0x80_3BL;
        0x80_37L;
        0x80_2FL;
        0x80_1EL;
        0x80_3CL;
        0x80_39L;
        0x80_33L;
        0x80_27L;
        0x80_0EL;
        0x80_1DL;
        0x80_3AL;
        0x80_35L;
        0x80_2BL;
        0x80_16L;
        0x80_2CL;
        0x80_18L;
        0x80_30L;
        0x80_21L;
        0x80_02L;
        0x80_05L;
        0x80_0BL;
        0x80_17L;
        0x80_2EL;
        0x80_1CL;
        0x80_38L;
        0x80_31L;
        0x80_23L;
        0x80_06L;
        0x80_0DL;
        0x80_1BL;
        0x80_36L;
        0x80_2DL;
        0x80_1AL;
        0x80_34L;
        0x80_29L;
        0x80_12L;
        0x80_24L;
        0x80_08L;
        0x80_11L;
        0x80_22L;
        0x80_04L;
      ]

  let bools_of_rows_cols rows_cols =
    List.rev @@ List.init 16
    @@ fun index ->
    let r = index / 4 in
    let c = index mod 4 in
    RowsCols.lookup rows_cols (r, c)

  let to_slice spec =
    let slices =
      List.init 4 @@ fun zindex ->
      let zslice = bools_of_rows_cols spec in
      List.map (fun z -> z |> Value.get zindex |> Value.as_bool) zslice
    in
    match slices with
    | [ s0; s1; s2; s3 ] -> (s0, s1, s2, s3)
    | _ -> assert false

  let spec_tabulate bools =
    RowsCols.tabulate @@ fun (r, c) ->
    Value.tabulate 4 @@ fun z ->
    let bit_index = 63 - ((16 * r) + (c * 4) + z) in
    let bool = List.nth bools bit_index in
    Bool bool

  let ( >>> ) list n =
    let length = List.length list in
    List.init length @@ fun index ->
    (* Avoid having the module negative *)
    let index = (index - n + length) mod length in
    List.nth list index

  let[@warning "-8"] update_key_state [ w0; w1; w2; w3; w4; w5; w6; w7 ] =
    let w0' = w6 >>> 2 in
    let w1' = w7 >>> 12 in
    let w2' = w0 in
    let w3' = w1 in
    let w4' = w2 in
    let w5' = w3 in
    let w6' = w4 in
    let w7' = w5 in
    [ w0'; w1'; w2'; w3'; w4'; w5'; w6'; w7' ]

  let[@warning "-8"] extract_key [ _; _; _; _; _; _; w6; w7 ] =
    let u = w6 in
    let v = w7 in
    (u, v)

  let precompute_keys keys =
    let iter = List.init 27 Fun.id in
    let _, pkeys =
      List.fold_left_map
        (fun previous _ ->
          let new_key = update_key_state previous in
          let couple = extract_key new_key in
          (new_key, couple))
        keys iter
    in
    let first = extract_key keys in
    first :: pkeys

  let slice_of_bools bools =
    let () = assert (List.length bools = 16) in
    RowsCols.tabulate @@ fun (r, c) ->
    let index = 15 - ((r * 4) + c) in
    Value.Bool (List.nth bools index)

  let uvs key =
    key |> precompute_keys
    |> List.map (fun (u, v) -> (slice_of_bools u, slice_of_bools v))
    |> List.split

  let transpose_inverse_block (s0, s1, s2, s3) =
    let ( .%() ) = List.nth in
    let ( lsl ) b n =
      let b = Bool.to_int b in
      b lsl n
    in

    let half_length = 8 in
    List.init half_length (fun i ->
        let i = 2 * i in
        let b0 = s3.%(i) in
        let b4 = s3.%(i + 1) in

        let b1 = s2.%(i) in
        let b5 = s2.%(i + 1) in

        let b2 = s1.%(i) in
        let b6 = s1.%(i + 1) in

        let b3 = s0.%(i) in
        let b7 = s0.%(i + 1) in

        let s =
          (b0 lsl 7) + (b1 lsl 6) + (b2 lsl 5) + (b3 lsl 4) + (b4 lsl 3)
          + (b5 lsl 2) + (b6 lsl 1) + Bool.to_int b7
        in

        Char.chr s)

  let transpose_inverse block =
    let block = transpose_inverse_block block in
    [ block ]

  let pp format =
    List.iter (fun cipher ->
        let () =
          List.iter
            (fun c -> Format.fprintf format "%02x " @@ Char.code c)
            cipher
        in
        Format.fprintf format "\n")

  let _pp_value format value =
    let slices = to_slice value in
    let chars = transpose_inverse slices in
    pp format chars

  let _cs value =
    let slices = to_slice value in
    let chars = transpose_inverse slices in
    pp Format.err_formatter chars

  let uvconsts key =
    let key = ListUtil.chunks 16 key in
    let us, vs = uvs key in
    let bottom = List.map (Value.map' (Fun.const B.false')) us in
    let consts =
      List.init (List.length us) @@ fun index ->
      let bconst = List.nth round_constants index in
      slice_of_bools bconst
    in
    let values =
      List.map
        (fun values -> Value.Array (Array.of_list values))
        [ us; vs; bottom; consts ]
    in
    let values =
      Value.mapn' 3
        (function
          | [ u; v; b; c ] ->
              let v = Value.Array [| v; u; b; c |] in
              (*              let () = Format.eprintf "%a\n" Ua0.Value.pp v in*)
              v
          | _ -> assert false)
        values
    in
    values |> Value.as_array |> Array.to_list
end
