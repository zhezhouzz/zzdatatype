module Array = struct
  include Array

  let fold_lefti f default arr =
    let _, r =
      fold_left (fun (idx, r) x -> (idx + 1, f r idx x)) (0, default) arr
    in
    r

  let mean_opt (f : 'a -> float) (l : 'a array) =
    if length l == 0 then None
    else
      let r = fold_left (fun sum x -> sum +. f x) 0.0 l in
      Some (r /. (float_of_int @@ length l))

  let meani_opt (f : int -> 'a -> float) (l : 'a array) =
    if length l == 0 then None
    else
      let r = fold_lefti (fun sum i x -> sum +. f i x) 0.0 l in
      Some (r /. (float_of_int @@ length l))

  let set_multi (f : int -> 'a) (i : int) (j : int) (arr : 'a array) =
    let rec aux idx =
      if idx >= j then () else set arr idx (f i);
      aux (idx + 1)
    in
    aux i
end

module BoolVec = struct
  type t = { cur : int; arr : bool array }

  let init_as_min n = { cur = n - 1; arr = Array.init n (fun _ -> false) }

  let increase { cur; arr } =
    let rec aux cur =
      if cur < 0 then None
      else if arr.(cur) then
        let () = arr.(cur) <- false in
        aux (cur - 1)
      else
        let () = arr.(cur) <- true in
        Some { cur = Array.length arr - 1; arr }
    in
    aux cur

  let to_list { arr; _ } = Array.to_list arr
end

module Bitarray = struct
  type t = { len : int; buf : bytes }

  let create len =
    let x = false in
    let init = if x = true then '\255' else '\000' in
    let buf = Bytes.make ((len / 8) + 1) init in
    { len; buf }

  let get t i =
    let ch = int_of_char (Bytes.get t.buf @@ (i lsr 3)) in
    let mask = 1 lsl (i land 7) in
    ch land mask <> 0

  let set t i b =
    let index = i lsr 3 in
    let ch = int_of_char (Bytes.get t.buf index) in
    let mask = 1 lsl (i land 7) in
    let new_ch = if b then ch lor mask else ch land lnot mask in
    Bytes.set t.buf index @@ char_of_int new_ch

  let equal ba1 ba2 =
    if ba1.len != ba2.len then false else Bytes.equal ba1.buf ba2.buf

  (* HACK: hash will fial when bitarray with different length mixed up *)
  let hash { buf; _ } = Hashtbl.hash (Bytes.to_string buf)

  let to_bool_list { len; buf } =
    List.init len (fun idx -> get { len; buf } idx)

  let to_bool_array { len; buf } =
    Array.init len (fun idx -> get { len; buf } idx)

  let of_bool_list l =
    let ba = create @@ List.length l in
    List.iteri (fun idx v -> set ba idx v) l;
    ba

  let init len f =
    let ba = create len in
    let rec aux idx =
      if idx >= len then ba
      else (
        set ba idx (f idx);
        aux idx)
    in
    aux 0
end
