module Make () = struct
  type t = { id : int; pretty : string }

  let fresh =
    let c = ref 0 in
    fun pretty ->
      let () = incr c in
      { id = !c; pretty }

  let compare lhs rhs = Int.compare lhs.id rhs.id
  let equal lhs rhs = Int.equal lhs.id rhs.id
  let pp format { id; pretty } = Format.fprintf format "%s(%u)" pretty id
  let refresh prefix base = fresh @@ Format.asprintf "%s%a" prefix pp base
end
