open Sexplib.Std

type elem = int [@@deriving sexp]

type tree = Node of int * elem * elem list * tree list [@@deriving sexp]

type t = tree list [@@deriving sexp]

exception Empty

open Zlist

let is_single_tree = function Node (_, _, _, t) -> List.length t == 0

let deep = List.length

let deep_tree = function Node (_, _, _, l) -> 1 + deep l

let rec mem x = function
  | [] -> false
  | Node (_, x', xs', t) :: t' ->
      Int.equal x x' || List.exists (Int.equal x) xs' || mem x t || mem x t'

let hd x = function [] -> false | Node (_, x', _, _) :: _ -> Int.equal x x'

let rec last x = function
  | [] -> false
  | [ Node (_, _, xs', []) ] -> List.exists (Int.equal x) xs'
  | Node (_, _, _, _) :: t' -> last x t'

let rec max_deep l =
  let aux = function Node (_, _, _, l) -> 1 + max_deep l in
  match IntList.max_opt @@ List.map aux l with None -> 0 | Some x -> x

let rec formal_layout l =
  match l with
  | [] -> "SkNil"
  | Node (r, x, l, l') :: t ->
      Printf.sprintf "SkCons (SkNode (%i, %i, %s, %s), %s)" r x
        (Printf.sprintf "[%s]" (IntList.to_string l))
        (formal_layout l') (formal_layout t)

let flatten_ input =
  let rtab = Hashtbl.create 40000 in
  let xtab = Hashtbl.create 40000 in
  let update tab x = if Hashtbl.mem tab x then () else Hashtbl.add tab x () in
  let rec aux t =
    match t with
    | [] -> ()
    | _ ->
        let ts =
          List.fold_left
            (fun ts tr ->
              match tr with
              | Node (r, x, l, t) ->
                  let () = update rtab r in
                  let () = List.iter (update xtab) (x :: l) in
                  t :: ts)
            [] t
        in
        List.iter aux ts
  in
  let () = aux input in
  (Hashtbl.to_seq_keys rtab, Hashtbl.to_seq_keys xtab)

let flatten t =
  (* let _ = Printf.printf "flatten\n" in *)
  let x, y = flatten_ t in
  let x = List.of_seq x in
  let y = List.of_seq y in
  (* Printf.printf "flatten end(%i, %i)\n" (List.length x) (List.length y); *)
  x @ y

let to_string l =
  match l with
  | [] -> "_"
  | _ ->
      let len = max_deep l in
      let arr = Array.init len (fun _ -> "") in
      let update idx str = arr.(idx) <- arr.(idx) ^ str in
      let update_below idx str =
        List.iter (fun i -> update i str)
        @@ List.init (len - idx) (fun x -> idx + x)
      in
      let rec aux idx t =
        match t with
        | Node (r, x, l, lt) ->
            update_below idx "{";
            update idx (Printf.sprintf "%i:%i~[%s] " r x @@ IntList.to_string l);
            List.iter (fun t -> aux (idx + 1) t) lt;
            update_below idx "}"
      in
      List.iter (fun t -> aux 0 t) l;
      (* let elems = flatten l in *)
      (* let _ = *)
      (*   Printf.printf "%s\n" *)
      (*   @@ Printf.sprintf "flatten:%s\n" *)
      (*   @@ IntList.to_string elems *)
      (* in *)
      (* let _ = raise @@ failwith "end" in *)
      let s =
        Array.fold_left
          (fun res str -> Printf.sprintf "%s\n%s" res str)
          "" (* (Printf.sprintf "flatten:%s\n" @@ IntList.to_string elems) *)
          arr
      in
      (* let _ = raise @@ failwith "end" in *)
      s

let compare t1 t2 =
  let rec aux t1 t2 =
    match (t1, t2) with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | Node (r1, x1, l1, y1) :: t1, Node (r2, x2, l2, y2) :: t2 ->
        let tmp = compare r1 r2 in
        if tmp != 0 then tmp
        else
          let tmp = compare x1 x2 in
          if tmp != 0 then tmp
          else
            let tmp = List.compare compare l1 l2 in
            if tmp != 0 then tmp
            else
              let tmp = aux y1 y2 in
              if tmp != 0 then tmp else aux t1 t2
  in
  aux t1 t2

let eq t1 t2 = compare t1 t2 == 0

let empty = []

let is_empty ts = ts = []

let rank (Node (r, _, _, _)) = r

let root (Node (_, x, _, _)) = x

let link (Node (r, x1, xs1, c1) as t1) (Node (_, x2, xs2, c2) as t2) =
  if x1 <= x2 then Node (r + 1, x1, xs1, t2 :: c1)
  else Node (r + 1, x2, xs2, t1 :: c2)

let skew_link x t1 t2 =
  let (Node (r, y, ys, c)) = link t1 t2 in
  if x <= y then Node (r, x, y :: ys, c) else Node (r, y, x :: ys, c)

let rec ins_tree t = function
  | [] -> [ t ]
  | t' :: ts ->
      if rank t < rank t' then t :: t' :: ts else ins_tree (link t t') ts

let rec merge_trees ts1 ts2 =
  match (ts1, ts2) with
  | _, [] -> ts1
  | [], _ -> ts2
  | t1 :: ts1', t2 :: ts2' ->
      if rank t1 < rank t2 then t1 :: merge_trees ts1' ts2
      else if rank t2 < rank t1 then t2 :: merge_trees ts1 ts2'
      else ins_tree (link t1 t2) (merge_trees ts1' ts2')

let normalize = function [] -> [] | t :: ts -> ins_tree t ts

let insert x = function
  | t1 :: t2 :: rest as ts ->
      if rank t1 = rank t2 then skew_link x t1 t2 :: rest
      else Node (0, x, [], []) :: ts
  | ts -> Node (0, x, [], []) :: ts

let merge ts1 ts2 = merge_trees (normalize ts1) (normalize ts2)

let rec remove_min_tree = function
  | [] -> raise Empty
  | [ t ] -> (t, [])
  | t :: ts ->
      let t', ts' = remove_min_tree ts in
      if root t <= root t' then (t, ts) else (t', t :: ts')

let find_min ts = root (fst (remove_min_tree ts))

let delete_min ts =
  let Node (_, _, xs, ts1), ts2 = remove_min_tree ts in
  let rec insert_all ts = function
    | [] -> ts
    | x :: xs' -> insert_all (insert x ts) xs'
  in
  insert_all (merge (List.rev ts1) ts2) xs

let rec num_node = function
  | [] -> 0
  | Node (_, _, _, ts') :: ts -> 1 + num_node ts' + num_node ts

let if_complete_list l =
  (* letlet len = List.length l in () = Printf.printf "_complete_list? %s\n" @@ IntList.to_string l in *)
  let len = List.length l in
  let arr = Array.init (List.length l) (fun _ -> false) in
  let b =
    List.fold_left
      (fun b i ->
        (* let i = i - 1 in *)
        if not b then false
        else if i < 0 || i >= len then false
        else if arr.(i) then false
        else (
          arr.(i) <- true;
          true))
      true l
  in
  if not b then false else Array.for_all (fun x -> x) arr

let rec binomial_complete_tree = function
  | Node (0, _, [], []) -> true
  | Node (0, _, _, _) -> false
  | Node (num_nodes, _, xs, ts) ->
      (* let _ = Printf.printf "num_nodes = %i\n" num_nodes in *)
      if List.length ts != num_nodes || List.length xs > num_nodes then false
      else if
        let if_comp = if_complete_list @@ List.map rank ts in
        (* let () = Printf.printf "_complete_list? %b\n" if_comp in *)
        if_comp
      then List.for_all binomial_complete_tree ts
      else false

let flatten_node t = List.of_seq @@ snd @@ flatten_ t

let fold_left f default input =
  let rec aux res t =
    match t with
    | [] -> res
    | _ ->
        let res', ts =
          List.fold_left
            (fun (res, ts) tr ->
              match tr with
              | Node (_, x, l, t) -> (List.fold_left f res (x :: l), t :: ts))
            (res, []) t
        in
        aux res' (List.concat ts)
  in
  aux default input

(* let mem t x = fold_left (fun b x' -> b || x == x') false t *)

let max_opt t =
  fold_left
    (fun opt x' -> match opt with None -> Some x' | Some x -> Some (max x x'))
    None t

let min_opt t =
  fold_left
    (fun opt x' -> match opt with None -> Some x' | Some x -> Some (min x x'))
    None t

let t_head = function Node (r, x, _, _) -> (r, x)

let t_head_l = function Node (r, x, xs, _) -> (r, x, xs)

let t_head_update t x = match t with Node (r, _, xs, l) -> Node (r, x, xs, l)

let t_head_l_update t x l =
  match t with Node (r, _, xs, _) -> Node (r, x, xs, l)

let skewhp ts =
  let rec to_binary res = function
    | 0 -> res
    | 1 -> true :: res
    | 2 -> true :: false :: res
    | 3 -> true :: true :: res
    | n ->
        let n' = n / 2 in
        let r = n - (n' * 2) in
        let b =
          if r == 1 then true
          else if r == 0 then false
          else raise @@ failwith "bad divide"
        in
        to_binary (b :: res) n'
  in
  let bl = List.rev @@ to_binary [] @@ num_node ts in
  (* let () = Printf.printf "bl: %s\n" @@ List.split_by_comma string_of_bool bl in *)
  (* let _ = raise @@ failwith "skewhp" in *)
  let bl = List.filter_mapi (fun idx b -> if b then Some idx else None) bl in
  (* let () = Printf.printf "bl: %s\n" @@ IntList.to_string bl in *)
  if List.length ts != List.length bl then false
  else
    let rs = List.map rank ts in
    if List.eq ( == ) bl rs then List.for_all binomial_complete_tree ts
    else false
