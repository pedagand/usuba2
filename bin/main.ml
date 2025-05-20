let () = Printexc.print_backtrace stderr
let () = Printexc.record_backtrace true

module RowsCols = struct
  let tabulate f =
    Usuba2.Eval.Value.tabulate 4 @@ fun c ->
    Usuba2.Eval.Value.tabulate 4 @@ fun r -> f (r, c)

  let lookup rc (r, c) =
    let value = Usuba2.Eval.Value.get c rc in
    Usuba2.Eval.Value.get r value
end

module Gift = struct
  let round_constants =
    List.map
      (Usuba2.Util.Bits.of_int ~pad:16)
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

  let spec_tabulate bools =
    RowsCols.tabulate @@ fun (r, c) ->
    Usuba2.Eval.Value.tabulate 4 @@ fun z ->
    let bit_index = 63 - ((16 * r) + (c * 4) + z) in
    let bool = List.nth bools bit_index in
    VBool bool

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
    VBool (List.nth bools index)

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
      List.map
        (fun z ->
          z
          |> Usuba2.Eval.Value.get zindex
          |> Usuba2.Eval.Value.as_bool |> Option.get)
        zslice
    in
    match slices with
    | [ s0; s1; s2; s3 ] -> (s0, s1, s2, s3)
    | _ -> assert false

  let uvs key =
    key |> precompute_keys
    |> List.map (fun (u, v) -> (slice_of_bools u, slice_of_bools v))
    |> List.split

  let uvconsts key =
    let key = Usuba2.Util.ListUtil.chunks 16 key in
    let us, vs = uvs key in
    let bottom = List.map (Usuba2.Eval.Value.map' (Fun.const false)) us in
    let consts =
      List.init (List.length us) @@ fun index ->
      let bconst = List.nth round_constants index in
      slice_of_bools bconst
    in
    Usuba2.Eval.mapn
      (function
        | [ u; v; b; c ] -> Usuba2.Eval.Value.Varray [| u; v; b; c |]
        | _ -> assert false)
      [ us; vs; bottom; consts ]

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

  let pp =
    List.iter (fun cipher ->
        let () =
          List.iter (fun c -> Format.eprintf "%02x " @@ Char.code c) cipher
        in
        print_newline ())

  (*    List.map2 (RowsCols.map2 (fun (u, v) const -> (u, v, const))) uv consts *)
end

let keys = Queue.create ()
let texts = Queue.create ()

let spec =
  Arg.align
    [
      ("-k", Arg.String (Fun.flip Queue.add keys), "<keyfile> path to the key");
    ]

let pos_args = Fun.flip Queue.add texts
let usage = Printf.sprintf "%s [-k <keyfile>]... PLAINTEXT..." Sys.argv.(0)
let () = Arg.parse spec pos_args usage

let eval keys texts =
  let () = assert (Queue.length keys = Queue.length texts) in
  let kps =
    Seq.map2
      (fun k t ->
        let k = Usuba2.Util.Common.file_to_bools k in
        let t = Usuba2.Util.Common.file_to_bools t in
        (k, t))
      (Queue.to_seq keys) (Queue.to_seq texts)
  in

  let kps =
    Seq.map
      (fun (k, t) ->
        let state = Gift.spec_tabulate t in
        let keys = Gift.uvconsts k in
        (state, keys))
      kps
  in

  Seq.find_map
    (fun (state, keys) ->
      let keys = Array.of_list keys in
      let () = assert (Array.length keys = 28) in

      Usuba2.Eval.eval Usuba2.Gift.gift Usuba2.Gift.fngift []
        [ state; Varray keys ])
    kps

let print module' = Format.printf "%a\n" Usuba2.Pp.pp_module module'

let main () =
  match Queue.is_empty texts with
  | true -> print Usuba2.Gift.gift
  | false -> (
      match eval keys texts with
      | None -> Printf.eprintf "evaluation None\n"
      | Some (value, _) ->
          let slices = Gift.to_slice value in
          let chars = Gift.transpose_inverse slices in
          Gift.pp chars)

let () = main ()
