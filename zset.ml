module IntSet = Set.Make (struct
  let compare = compare

  type t = int
end)
