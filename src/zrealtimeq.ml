open Sexplib.Std

type stream_cell = Nil | Cons of int * stream [@@deriving sexp]

and stream = stream_cell Lazy.t [@@deriving sexp]

let ( !$ ) = Lazy.force

exception Empty

let rec to_list x = match !$x with Nil -> [] | Cons (x, st) -> x :: to_list st

let rec of_list = function
  | [] -> lazy Nil
  | h :: t -> lazy (Cons (h, of_list t))

let rec ( ++ ) s1 s2 =
  lazy
    (match s1 with
    | (lazy Nil) -> Lazy.force s2
    | (lazy (Cons (hd, tl))) -> Cons (hd, tl ++ s2))

let rec take n s =
  lazy
    (if n = 0 then Nil
    else
      match s with
      | (lazy Nil) -> Nil
      | (lazy (Cons (hd, tl))) -> Cons (hd, take (n - 1) tl))

let rec drop n s =
  lazy
    (match (n, s) with
    | 0, _ -> !$s
    | _, (lazy Nil) -> Nil
    | _, (lazy (Cons (_, tl))) -> !$(drop (n - 1) tl))

let reverse s =
  let rec reverse' acc s =
    lazy
      (match s with
      | (lazy Nil) -> !$acc
      | (lazy (Cons (hd, tl))) -> !$(reverse' (lazy (Cons (hd, acc))) tl))
  in
  reverse' (lazy Nil) s

type t = stream * int list * stream [@@deriving sexp]

open Zlist

let flatten (a, b, c) = to_list a @ b @ to_list c

let length l = List.length @@ flatten l

let to_string (a, b, c) =
  Printf.sprintf "%s | %s | %s"
    (IntList.to_string @@ to_list a)
    (IntList.to_string b)
    (IntList.to_string @@ to_list c)

let compare (a1, b1, c1) (a2, b2, c2) =
  let tmp = List.compare compare (to_list a1) (to_list a2) in
  if tmp != 0 then tmp
  else
    let tmp = List.compare compare b1 b2 in
    if tmp != 0 then tmp else List.compare compare (to_list c1) (to_list c2)

let eq t1 t2 = compare t1 t2 == 0

let empty = (lazy Nil, [], lazy Nil)

let is_empty = function (lazy Nil), _, _ -> true | _ -> false

let rec rotate = function
  | (lazy Nil), y :: _, a -> lazy (Cons (y, a))
  | (lazy (Cons (x, xs))), y :: ys, a ->
      lazy (Cons (x, rotate (xs, ys, lazy (Cons (y, a)))))
  | _, [], _ -> raise @@ failwith "impossible_pat: rotate"

let exec = function
  | f, r, (lazy (Cons (_, s))) -> (f, r, s)
  | f, r, (lazy Nil) ->
      let f' = rotate (f, r, lazy Nil) in
      (f', [], f')

let snoc (f, r, s) x = exec (f, x :: r, s)

let head (f, _, _) =
  match f with (lazy Nil) -> raise Empty | (lazy (Cons (x, _))) -> x

let tail = function
  | (lazy Nil), _, _ -> raise Empty
  | (lazy (Cons (_, f))), r, s -> exec (f, r, s)
