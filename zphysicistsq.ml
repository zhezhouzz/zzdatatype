open Sexplib.Std

type t = int list * int * int list Lazy.t * int * int list [@@deriving sexp]

let ( !$ ) = Lazy.force

exception Empty

open Zlist

let to_string (a, len1, b, len2, c) =
  Printf.sprintf "{%s | %i | %s | %i | %s}" (IntList.to_string a) len1
    (IntList.to_string @@ !$b) len2 (IntList.to_string c)

let flatten (a, len1, b, len2, c) = a @ [ len1 ] @ Lazy.force b @ [ len2 ] @ c

let length l = List.length @@ flatten l

let compare t1 t2 = List.compare compare (flatten t1) (flatten t2)

let eq t1 t2 = compare t1 t2 == 0

let empty = ([], 0, lazy [], 0, [])

let is_empty (_, lenf, _, _, _) = lenf = 0

let checkw = function [], lenf, f, lenr, r -> (!$f, lenf, f, lenr, r) | q -> q

let check ((_, lenf, f, lenr, r) as q) =
  if lenr <= lenf then checkw q
  else
    let f' = !$f in
    checkw (f', lenf + lenr, lazy (f' @ List.rev r), 0, [])

let snoc (w, lenf, f, lenr, r) x = check (w, lenf, f, lenr + 1, x :: r)

let head = function [], _, _, _, _ -> raise Empty | x :: _, _, _, _, _ -> x

let tail = function
  | [], _, _, _, _ -> raise Empty
  | _ :: w, lenf, f, lenr, r -> check (w, lenf - 1, lazy (List.tl !$f), lenr, r)
