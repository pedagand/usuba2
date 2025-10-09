module StringUtil = struct
  let rec chunks current acc n s =
    match s with
    | [] -> acc
    | t :: q -> (
        let s = Printf.sprintf "%s%c" current t in
        match String.length s with
        | l when l = n -> chunks String.empty (s :: acc) n q
        | _ -> chunks s acc n q)

  (** [chunks n s] sépare [s] en une liste de [n] strings *)
  let chunks ?(rev = false) n s =
    let s = chunks String.empty [] n (List.of_seq @@ String.to_seq s) in
    if rev then s else List.rev s
end

module ListUtil = struct
  let rec chunks current acc n s =
    match s with
    | [] -> current :: acc
    | t :: q -> (
        match List.length current with
        | l when l = n -> chunks [ t ] (current :: acc) n q
        | _ ->
            let current = current @ [ t ] in
            chunks current acc n q)

  (** [chunks n s] sépare [s] en une liste de chaque liste ou chaque sous liste
      est de longeur [n]. *)
  let chunks ?(rev = false) n l =
    let s = chunks [] [] n l in
    if rev then s else List.rev s
end

module Io = struct
  let read_all_chan ch = really_input_string ch (in_channel_length ch)
  let read_all string = In_channel.with_open_bin string read_all_chan
end

module Bits = struct
  let of_int64 ?pad n =
    let ( mod ) = Int64.unsigned_rem in
    let ( / ) = Int64.unsigned_div in
    let rec aux n list =
      let quotient = n / 2L in
      let res = n mod 2L in
      if quotient = 0L then res :: list else aux quotient (res :: list)
    in
    let list = aux n [] in
    let length = List.length list in
    match pad with
    | None -> list
    | Some padding ->
        let leading = max 0 (padding - length) in
        List.init leading (fun _ -> 0L) @ list

  let of_int ?pad n = List.map (Int64.equal 1L) @@ of_int64 ?pad n
end

module Common = struct
  let from_hex_string s =
    s |> String.to_seq
    |> Seq.filter (Fun.negate @@ ( = ) ' ')
    |> String.of_seq |> StringUtil.chunks 2
    |> List.map (fun s ->
           let s = "0x" ^ s in
           Bits.of_int ~pad:8 @@ Int64.of_string s)
    |> List.flatten

  let file_to_bools file =
    let content = Io.read_all file in
    from_hex_string content
end
