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
