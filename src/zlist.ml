module Array = Zarray.Array

module List = struct
  include List

  let spf = Printf.sprintf
  let nth_opt l x = try nth_opt l x with _ -> None
  let destruct_opt = function [] -> None | h :: t -> Some (h, t)

  let update_opt l idx x =
    if List.length l <= idx || idx < 0 then None
    else
      let arr = Array.of_list l in
      Array.set arr idx x;
      Some (Array.to_list arr)

  let substract eq a b = List.filter (fun x -> not (List.exists (eq x) b)) a

  let slow_rm_dup eq a =
    let rec aux res = function
      | [] -> res
      | h :: t ->
          if List.exists (eq h) res then aux res t else aux (res @ [ h ]) t
    in
    aux [] a

  let mid_partition l =
    let mid = length l / 2 in
    let rec aux left l =
      if List.length left >= mid then (left, l)
      else match l with [] -> (left, []) | h :: t -> aux (l @ [ h ]) t
    in
    aux [] l

  let alter_partition l =
    let rec aux (l, r, flag) = function
      | [] -> (l, r)
      | h :: t ->
          if flag then aux (l @ [ h ], r, not flag) t
          else aux (l, r @ [ h ], not flag) t
    in
    aux ([], [], true) l

  let compare e_compare l1 l2 =
    let rec aux l1 l2 =
      match (l1, l2) with
      | [], [] -> 0
      | [], _ :: _ -> -1
      | _ :: _, [] -> 1
      | h1 :: t1, h2 :: t2 ->
          let c = e_compare h1 h2 in
          if c != 0 then c else aux t1 t2
    in
    aux l1 l2

  let last_destruct_opt l =
    match rev l with [] -> None | last :: l -> Some (rev l, last)

  let check_sorted judge l =
    match l with
    | [] -> true
    | h :: t ->
        let rec aux previous l =
          match l with
          | [] -> true
          | h :: t -> if judge previous h then aux h t else false
        in
        aux h t

  let split_by sp f l =
    match
      List.fold_left
        (fun r x ->
          match r with
          | None -> Some (spf "%s" (f x))
          | Some r -> Some (spf "%s%s%s" r sp (f x)))
        None l
    with
    | None -> ""
    | Some r -> r

  let split_by_comma f l =
    match
      List.fold_left
        (fun r x ->
          match r with
          | None -> Some (spf "%s" (f x))
          | Some r -> Some (spf "%s, %s" r (f x)))
        None l
    with
    | None -> ""
    | Some r -> r

  let is_empty = function [] -> true | _ -> false

  let replace_exn l idx elem =
    let rec aux l n =
      match (l, n) with
      | [], _ ->
          raise @@ failwith
          @@ spf "[%s]:replace_exn(%i) within %i" __FILE__ n (List.length l)
      | _ :: t, 0 -> elem :: t
      | h :: t, n -> h :: aux t (n - 1)
    in
    aux l idx

  let replace_opt l idx elem =
    if idx >= List.length l || idx < 0 then None
    else
      try Some (replace_exn l idx elem)
      with e ->
        Printf.printf "should not happen in replace_opt\n";
        raise e

  let swap_exn l idx idx' =
    let v, v' =
      try (List.nth l idx, List.nth l idx')
      with _ ->
        raise @@ failwith
        @@ spf "[%s:]swap_exn(%i, %i) within %i" __FILE__ idx idx'
             (List.length l)
    in
    replace_exn (replace_exn l idx v') idx' v

  let swap_opt l idx idx' =
    (* let _ = Printf.printf "len(l) = %i; idx = %i; idx' = %i\n" (List.length l) idx idx' in *)
    if List.length l <= idx || List.length l <= idx' || idx < 0 || idx' < 0 then
      None
    else
      try Some (swap_exn l idx idx')
      with e ->
        Printf.printf "should not happen in swap_opt\n";
        raise e

  let eq compare l1 l2 =
    let rec aux = function
      | [], [] -> true
      | h1 :: t1, h2 :: t2 -> if compare h1 h2 then aux (t1, t2) else false
      | _, _ -> false
    in
    aux (l1, l2)

  let find info f l =
    match find_opt f l with
    | None -> raise @@ failwith @@ spf "[%s:]%s" __FILE__ info
    | Some v -> v

  let order eq l u v =
    let rec aux = function
      | [] -> false
      | h :: t -> if eq u h then List.exists (fun x -> eq x v) t else aux t
    in
    aux l

  let for_alli f l =
    let rec aux i = function
      | [] -> true
      | h :: t -> if f h i then aux (i + 1) t else false
    in
    aux 0 l

  let fold_lefti f default l =
    let rec aux r i = function [] -> r | h :: t -> aux (f r i h) (i + 1) t in
    aux default 0 l

  let mean_exn (f : 'a -> float) (l : 'a list) =
    if length l == 0 then raise @@ failwith @@ spf "[%s]:never happen" __FILE__
    else
      let r = fold_left (fun sum x -> sum +. f x) 0.0 l in
      r /. (float_of_int @@ length l)

  let mean_opt (f : 'a -> float) (l : 'a list) =
    if length l == 0 then None
    else
      let r = fold_left (fun sum x -> sum +. f x) 0.0 l in
      Some (r /. (float_of_int @@ length l))

  let meani_opt (f : int -> 'a -> float) (l : 'a list) =
    if length l == 0 then None
    else
      let r = fold_lefti (fun sum i x -> sum +. f i x) 0.0 l in
      Some (r /. (float_of_int @@ length l))

  let find_index_opt f l =
    fold_lefti
      (fun r i x ->
        match r with Some _ -> r | None -> if f x then Some i else None)
      None l

  let find_index info f l =
    match find_index_opt f l with
    | None -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ info
    | Some i -> i

  let first l =
    match l with
    | [] -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ "list_first"
    | h :: _ -> h

  let last l =
    let l = List.rev l in
    match l with
    | [] -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ "list_last"
    | h :: _ -> h

  let lastb l e =
    let l = List.rev l in
    match l with [] -> false | h :: _ -> h == e

  let to_string f l =
    fold_lefti
      (fun res i a -> if i == 0 then res ^ f a else res ^ "," ^ f a)
      "" l

  let rec element_unique f l e =
    match l with
    | [] -> None
    | h :: t -> if f e h then Some t else element_unique f t e

  let once f l e =
    match element_unique f l e with
    | None -> false
    | Some t -> (
        match element_unique f t e with None -> true | Some _ -> false)

  let rec double_exists f l =
    match l with
    | [] -> false
    | h :: t -> (
        match element_unique f t h with
        | None -> double_exists f t
        | Some _ -> true)

  let rec check_list_unique eq l =
    let rec aux e = function
      | [] -> true
      | h :: t -> if eq e h then false else aux e t
    in
    match l with
    | [] -> true
    | h :: t -> if aux h t then check_list_unique eq t else false

  let remove_elt compare e l =
    let rec go l acc =
      match l with
      | [] -> List.rev acc
      | x :: xs when compare e x -> go xs acc
      | x :: xs -> go xs (x :: acc)
    in
    go l []

  let remove_duplicates l =
    let s = Zset.IntSet.add_seq (List.to_seq l) Zset.IntSet.empty in
    List.of_seq @@ Zset.IntSet.to_seq s

  let interset compare l1 l2 =
    let rec aux r = function
      | [] -> r
      | h :: t ->
          if exists (fun y -> compare h y) l2 then aux (h :: r) t else aux r t
    in
    aux [] l1

  (* let remove_duplicates_eq l = remove_duplicates (fun x y -> x == y) l *)

  let inner_layout l split default =
    match l with
    | [] -> default
    | h :: t -> List.fold_left (fun res x -> res ^ split ^ x) h t

  let flatten_forall = remove_duplicates

  let combination num_all num_choose =
    let rec aux prefix rest_num rest_elems =
      if rest_num > List.length rest_elems then []
      else if rest_num == 0 then [ prefix ]
      else if rest_num == 1 then
        List.fold_left (fun r x -> (x :: prefix) :: r) [] rest_elems
      else
        match rest_elems with
        | [] -> []
        | h :: t -> aux (h :: prefix) (rest_num - 1) t @ aux prefix rest_num t
    in
    let elems = List.init num_all (fun x -> x) in
    aux [] num_choose elems

  let combination_l l num_choose =
    let c = combination (List.length l) num_choose in
    List.map (fun ids -> List.map (fun id -> List.nth l id) ids) c

  let combination_l_all l =
    let len = List.length l in
    let rec aux num_choose result =
      if num_choose > len then result
      else aux (num_choose + 1) (result @ combination_l l num_choose)
    in
    aux 0 []

  let c_n_2 l =
    let rec aux l =
      match l with [] -> [] | h :: t -> map (fun x -> (h, x)) t @ aux t
    in
    aux l

  let permutation l =
    let insert_all_positions x l =
      let rec aux prev acc l =
        match l with
        | [] -> (prev @ [ x ]) :: acc |> List.rev
        | hd :: tl as l -> aux (prev @ [ hd ]) ((prev @ [ x ] @ l) :: acc) tl
      in
      aux [] [] l
    in
    let rec aux = function
      | [] -> []
      | [ hd ] -> [ [ hd ] ]
      | hd :: tl ->
          List.fold_left
            (fun acc p -> acc @ insert_all_positions hd p)
            [] (aux tl)
    in
    aux l

  let cross l0 l1 =
    if List.length l0 == 0 || List.length l1 == 0 then []
    else
      let rec aux i j res =
        if j >= List.length l1 then aux (i + 1) 0 res
        else if i >= List.length l0 then res
        else aux i (j + 1) ((List.nth l0 i, List.nth l1 j) :: res)
      in
      aux 0 0 []

  let match_snoc l =
    let l = List.rev l in
    match l with
    | [] -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ "match_snoc: []"
    | h :: t -> (List.rev t, h)

  (* let union compare l0 l1 = remove_duplicates compare (l0 @ l1) *)

  let shape_reverse ll =
    let nth l id =
      try List.nth l id with
      | Failure _ -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ "shape_reverse"
      | Invalid_argument _ ->
          raise @@ failwith @@ spf "[%s]:%s" __FILE__ "shape_reverse"
    in
    List.init (List.length ll) (fun i -> List.map (fun l -> nth l i) ll)

  let choose_list_list ll =
    if List.exists (fun l -> List.length l == 0) ll then []
    else
      let one_lists, others = List.partition (fun l -> List.length l == 1) ll in
      let others = Array.of_list (List.map Array.of_list others) in
      let one_list = List.flatten one_lists in
      let n = Array.length others in
      let idx_max = Array.init n (fun i -> Array.length others.(i)) in
      let idx = Array.init n (fun _ -> 0) in
      let rec increase i =
        if i >= n then None
        else if idx.(i) + 1 >= idx_max.(i) then (
          Array.set idx i 0;
          increase (i + 1))
        else (
          Array.set idx i (idx.(i) + 1);
          Some ())
      in
      let rec aux r =
        let a = List.init n (fun i -> others.(i).(idx.(i))) in
        match increase 0 with None -> a :: r | Some _ -> aux (a :: r)
      in
      List.map (fun l -> one_list @ l) (aux [])

  let choose_list_list_order ll =
    if List.exists (fun l -> List.length l == 0) ll then []
    else
      let others = Array.of_list (List.map Array.of_list ll) in
      let n = Array.length others in
      let idx_max = Array.init n (fun i -> Array.length others.(i)) in
      let idx = Array.init n (fun _ -> 0) in
      let rec increase i =
        if i >= n then None
        else if idx.(i) + 1 >= idx_max.(i) then (
          Array.set idx i 0;
          increase (i + 1))
        else (
          Array.set idx i (idx.(i) + 1);
          Some ())
      in
      let rec aux r =
        let a = List.init n (fun i -> others.(i).(idx.(i))) in
        match increase 0 with None -> a :: r | Some _ -> aux (a :: r)
      in
      aux []

  let choose_list_list_order_fold f default ll =
    if List.exists (fun l -> List.length l == 0) ll then default
    else
      let others = Array.of_list (List.map Array.of_list ll) in
      let n = Array.length others in
      let idx_max = Array.init n (fun i -> Array.length others.(i)) in
      let idx = Array.init n (fun _ -> 0) in
      let rec increase i =
        if i >= n then None
        else if idx.(i) + 1 >= idx_max.(i) then (
          Array.set idx i 0;
          increase (i + 1))
        else (
          Array.set idx i (idx.(i) + 1);
          Some ())
      in
      let rec aux r =
        let a = List.init n (fun i -> others.(i).(idx.(i))) in
        match increase 0 with None -> f r a | Some _ -> aux (f r a)
      in
      aux default

  (* duplicate *)
  let choose_n l n =
    let rec aux r n =
      if n == 0 then r
      else
        aux
          (List.flatten @@ List.map (fun e -> List.map (fun r -> e :: r) r) l)
          (n - 1)
    in
    if n < 0 then
      raise @@ failwith @@ spf "[%s]:%s" __FILE__ "choose_n_eq: bad n"
    else if n == 0 then [ [] ]
    else aux (List.map (fun x -> [ x ]) l) (n - 1)

  let choose_n_neq l n =
    let arr = Array.of_list l in
    let len = Array.length arr in
    let used = Array.make len false in
    let res = ref [] in
    let rec aux curidx rest_len prefix =
      if rest_len == 0 then res := prefix :: !res
      else if curidx >= len then ()
      else
        match used.(curidx) with
        | true -> aux (curidx + 1) rest_len prefix
        | false ->
            used.(curidx) <- true;
            aux 0 (rest_len - 1) (curidx :: prefix);
            used.(curidx) <- false;
            aux (curidx + 1) rest_len prefix
    in
    aux 0 n [];
    List.map (fun idxs -> List.map (fun idx -> arr.(idx)) idxs) !res

  let choose_n_eq l n = choose_n (remove_duplicates l) n

  let choose_eq_all l =
    List.flatten @@ List.init (List.length l + 1) (fun n -> choose_n_eq l n)

  let sublist l ~start_included:s ~end_excluded:e =
    let rec aux r i l =
      if i >= e then r
      else
        match l with
        | [] -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ "sublist"
        | h :: t ->
            if i >= s then aux (r @ [ h ]) (i + 1) t else aux r (i + 1) t
    in
    aux [] 0 l

  let filter_mapi f l =
    fold_lefti
      (fun r i x -> match f i x with None -> r | Some y -> r @ [ y ])
      [] l

  let lookup eq x l =
    let rec aux i = function
      | [] -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ "List.lookup"
      | h :: t -> if eq x h then i else aux (i + 1) t
    in
    aux 0 l

  let nth l i =
    match List.nth_opt l i with
    | Some v -> v
    | None -> raise @@ failwith @@ spf "[%s]:%s" __FILE__ "List.nth"

  let power_set_b n =
    let rec aux (cur : bool t t) n : bool t t =
      if n <= 0 then cur
      else
        aux
          (map (fun l -> true :: l) cur @ map (fun l -> false :: l) cur)
          (n - 1)
    in
    aux [ [ true ]; [ false ] ] (n - 1)

  let power_set_b_fold f default n =
    let vec = Array.init n (fun _ -> false) in
    let rec to_zero idx =
      if idx < 0 then ()
      else (
        Array.set vec idx false;
        to_zero (idx - 1))
    in
    let rec incr idx =
      if idx >= n then false
      else if vec.(idx) then incr (idx + 1)
      else (
        Array.set vec idx true;
        to_zero (idx - 1);
        (* Printf.printf "vec[0] = %b; vec[1] = %b\n" vec.(0) vec.(1); *)
        true)
    in
    let rec aux r =
      let r = f r vec in
      if incr 0 then aux r else r
    in
    aux default
end

module StrList = struct
  let eq l1 l2 = List.eq String.equal l1 l2
  let to_string l = List.to_string (fun x -> x) l
  let search errinfo l a = List.find errinfo (fun (k, _) -> String.equal k a) l
end

module IntList = struct
  let spf = Printf.sprintf
  let exists x l = List.exists (fun a -> a == x) l
  let contain l0 l1 = List.for_all (fun x -> exists x l1) l0

  let rec keep_ord l0 l1 =
    let rec aux a b = function
      | [] -> false
      | h :: t -> if h == a then exists b t else aux a b t
    in
    let rec aux2 a = function [] -> true | h :: t -> aux a h l1 && aux2 a t in
    match l0 with [] -> true | h :: t -> aux2 h t && keep_ord t l1

  let forall_ge l = List.for_alli (fun h i -> h >= i) l
  let forall_gt l = List.for_alli (fun h i -> h > i) l
  let forall_eq l = List.for_alli (fun h i -> h == i) l
  let eq l0 l1 = List.eq (fun x y -> x == y) l0 l1
  let sum = List.fold_left (fun sum x -> sum + x) 0

  let to_string l =
    List.fold_lefti
      (fun res i a ->
        if i == 0 then res ^ string_of_int a else res ^ ";" ^ string_of_int a)
      "" l

  let max_opt l =
    let rec aux m = function
      | [] -> m
      | h :: t -> if h > m then aux h t else aux m t
    in
    match l with [] -> None | h :: t -> Some (aux h t)

  let min_opt l =
    let rec aux m = function
      | [] -> m
      | h :: t -> if h < m then aux h t else aux m t
    in
    match l with [] -> None | h :: t -> Some (aux h t)

  let bigger_range l =
    match (min_opt l, max_opt l) with
    | None, None -> (-1, 1)
    | Some s, Some e -> (s - 1, e + 1)
    | _, _ -> raise @@ failwith "never happen"

  let of_range (s, e) =
    let len = e - s + 1 in
    List.init len (fun i -> i + s)

  let is_strict_sort (l : int list) =
    let l' = List.sort_uniq compare l in
    List.eq ( == ) l l'

  let is_unique (l : int list) =
    let l' = List.sort_uniq compare l in
    List.length l == List.length l'
end
