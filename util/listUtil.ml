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
