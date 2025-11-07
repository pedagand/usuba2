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

let from_hex_string s =
  s |> String.to_seq
  |> Seq.filter (Fun.negate @@ ( = ) ' ')
  |> String.of_seq |> chunks 2
  |> List.map (fun s ->
      let s = "0x" ^ s in
      Bits.of_int ~pad:8 @@ Int64.of_string s)
  |> List.flatten
