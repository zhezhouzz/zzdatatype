open Sexplib.Std

type t = E | T of int * t list [@@deriving sexp]

exception Empty

let empty = E

open Zlist

let rec deep = function
  | E -> 0
  | T (_, l) -> (
      match IntList.max_opt @@ List.map deep l with
      | None -> 1
      | Some x -> 1 + x)

let rec mem x = function
  | E -> false
  | T (x', ts) -> Int.equal x x' || List.exists (mem x) ts

let hd x = function E -> false | T (x', _) -> Int.equal x x'

let rec last x = function
  | E -> false
  | T (x', []) -> Int.equal x x'
  | T (_, ts) -> List.exists (last x) ts

let rec flatten t =
  match t with E -> [] | T (x, l) -> x :: (List.concat @@ List.map flatten l)

let to_string l =
  let len = 1 + deep l in
  let arr = Array.init len (fun _ -> "") in
  let update idx str = arr.(idx) <- arr.(idx) ^ str in
  let update_below idx str =
    List.iter (fun i -> update i str)
    @@ List.init (len - idx) (fun x -> idx + x)
  in
  let rec aux idx t =
    match t with
    | E -> update idx "()"
    | T (x, l) ->
        update_below idx "{";
        update idx (Printf.sprintf "%i, " x);
        List.iter (fun t -> aux (idx + 1) t) l;
        update_below idx "}"
  in
  aux 0 l;
  Array.fold_left
    (fun res str -> Printf.sprintf "%s\n%s" res str)
    (Printf.sprintf "flatten:%s\n" @@ IntList.to_string @@ flatten l)
    arr

let rec formal_layout t =
  match t with
  | E -> "PLeaf"
  | T (x, l) -> Printf.sprintf "PNode (%i, %s)" x (formal_layout_l l)

and formal_layout_l = function
  | [] -> "PNil"
  | h :: t ->
      Printf.sprintf "PCons (%s, %s)" (formal_layout h) (formal_layout_l t)

let compare t1 t2 =
  let rec aux t1 t2 =
    match (t1, t2) with
    | E, E -> 0
    | E, _ -> -1
    | _, E -> 1
    | T (x1, l1), T (x2, l2) ->
        let tmp = compare x1 x2 in
        if tmp != 0 then tmp else List.compare aux l1 l2
  in
  aux t1 t2

let eq t1 t2 = compare t1 t2 == 0

let is_empty = function E -> true | _ -> false

let merge h1 h2 =
  match (h1, h2) with
  | _, E -> h1
  | E, _ -> h2
  | T (x, hs1), T (y, hs2) ->
      if x <= y then T (x, h2 :: hs1) else T (y, h1 :: hs2)

let insert x h = merge (T (x, [])) h

let rec merge_pairs = function
  | [] -> E
  | [ h ] -> h
  | h1 :: h2 :: hs -> merge (merge h1 h2) (merge_pairs hs)

let find_min = function E -> raise Empty | T (x, _) -> x

let delete_min = function E -> raise Empty | T (_, hs) -> merge_pairs hs

let pairinghp x =
  let rec check_list = function
    | [] -> true
    | E :: _ -> false
    | h :: t -> check_tree h && check_list t
  and check_tree = function E -> true | T (_, l) -> check_list l in
  check_tree x

let fold_left f default t =
  let rec aux res = function
    | E -> res
    | T (x, l) -> List.fold_left (fun res t -> aux res t) (f res x) l
  in
  aux default t

let pairinghp_sort t =
  let f res x =
    match res with
    | false, _ -> res
    | true, None -> (true, Some x)
    | true, Some prev -> if prev < x then (true, Some x) else (false, None)
  in
  let b, _ = fold_left f (true, None) t in
  b

let max_opt t =
  fold_left
    (fun opt x' -> match opt with None -> Some x' | Some x -> Some (max x x'))
    None t

let min_opt t =
  fold_left
    (fun opt x' -> match opt with None -> Some x' | Some x -> Some (min x x'))
    None t

(* let mem t x = fold_left (fun opt x' -> opt || x == x') false t *)

let single x = T (x, [])

let drop_bottom t =
  let rec aux t =
    match t with
    | E -> E
    | T (_, []) -> E
    | T (x, l) ->
        let l' =
          List.filter_map
            (fun x -> match aux x with E -> None | x -> Some x)
            l
        in
        T (x, l')
  in
  aux t

let append_to_left_most_label y t =
  let rec aux = function
    | E -> T (y, [])
    | T (x, []) -> T (x, [ T (y, []) ])
    | T (x, h :: t) -> T (x, aux h :: t)
  in
  aux t

let append_to_right_most_label y t =
  let rec aux = function
    | E -> T (y, [])
    | T (x, []) -> T (x, [ T (y, []) ])
    | T (x, l) -> (
        match List.rev l with
        | [] -> raise @@ failwith "never happen"
        | h :: t -> T (x, List.rev (aux h :: t)))
  in
  aux t
