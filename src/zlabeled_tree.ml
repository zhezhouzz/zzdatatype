module List = Zlist.List
module Tree = Ztree.Tree

module LabeledTree = struct
  type ('a, 'b) t = Leaf | Node of ('b * 'a * ('a, 'b) t * ('a, 'b) t)
  [@@deriving sexp]

  let spf = Printf.sprintf

  let rank = function Leaf -> 0 | Node (r, _, _, _) -> r

  let makeT x a b =
    if rank a >= rank b then Node (rank b + 1, x, a, b)
    else Node (rank a + 1, x, b, a)

  let rec map f = function
    | Leaf -> Leaf
    | Node (label, x, a, b) -> Node (label, f x, map f a, map f b)

  let deep t =
    let rec aux = function
      | Leaf -> 0
      | Node (_, _, l, r) ->
          let ln = aux l in
          let rn = aux r in
          if ln > rn then ln + 1 else rn + 1
    in
    (* Printf.printf "ti: len: %i\n" @@ aux t; *)
    aux t

  let rec size = function Leaf -> 0 | Node (_, _, a, b) -> 1 + size a + size b

  let flip tr =
    match tr with Leaf -> Leaf | Node (label, a, b, c) -> Node (label, a, c, b)

  let rec rec_flip tr =
    match tr with
    | Leaf -> Leaf
    | Node (label, a, b, c) -> Node (label, a, rec_flip c, rec_flip b)

  let rotation_right_opt tr =
    match tr with
    | Leaf -> Some Leaf
    | Node (labelx, x, Node (labely, y, a, b), c) ->
        Some (Node (labely, y, a, Node (labelx, x, b, c)))
    | _ -> None

  let rotation_left_opt tr =
    match tr with
    | Leaf -> Some Leaf
    | Node (labelx, x, a, Node (labely, y, b, c)) ->
        Some (Node (labely, y, Node (labelx, x, a, b), c))
    | _ -> None

  let rec append_to_left_most_label label x tr =
    match tr with
    | Leaf -> Node (label, x, Leaf, Leaf)
    | Node (labely, y, a, b) ->
        Node (labely, y, append_to_left_most_label label x a, b)

  let rec append_to_right_most_label label x tr =
    match tr with
    | Leaf -> Node (label, x, Leaf, Leaf)
    | Node (labely, y, a, b) ->
        Node (labely, y, a, append_to_right_most_label label x b)

  let max_opt (e_compare : 'a -> 'a -> int) (t1 : ('a, 'b) t) : ('b * 'a) option
      =
    let rec aux max_e = function
      | Leaf -> max_e
      | Node (label, a, b, c) ->
          let max_e =
            match max_e with
            | None -> Some (label, a)
            | Some (_, max_e') ->
                if e_compare a max_e' > 0 then Some (label, a) else max_e
          in
          aux (aux max_e b) c
    in
    aux None t1

  let min_opt e_compare t1 = max_opt (fun x y -> ~-(e_compare x y)) t1

  let rec from_tree label t =
    match t with
    | Tree.Leaf -> Leaf
    | Tree.Node (a, l, r) ->
        Node (label, a, from_tree label l, from_tree label r)

  let fold f default t =
    let rec aux res t =
      match t with
      | Leaf -> res
      | Node (label, e, l, r) -> aux (aux (f default label e) l) r
    in
    aux default t

  let rb_balance_ t =
    let nfalse = ref None in
    let update i =
      match !nfalse with
      | None ->
          nfalse := Some i;
          true
      | Some i' -> if i == i' then true else false
    in
    let rec aux idx = function
      | Leaf -> update idx
      | Node (label, _, l, r) ->
          let idx = if label then idx else idx + 1 in
          aux idx l && aux idx r
    in
    (aux 0 t, !nfalse)

  let rb_balance t = fst @@ rb_balance_ t

  let rb_balance2 t1 t2 =
    let a1, b1 = rb_balance_ t1 in
    let a2, b2 = rb_balance_ t2 in
    a1 && a2 && b1 == b2

  let leftists t =
    let rec aux = function
      | Leaf -> Some 0
      | Node (label, _, l, r) -> (
          match aux l with
          | None -> None
          | Some ll -> (
              if label != ll + 1 then None
              else match aux r with None -> None | Some _ -> Some label))
    in
    match aux t with None -> false | Some _ -> true

  let exists f t =
    let rec aux before t =
      if before then true
      else
        match t with
        | Leaf -> false
        | Node (_, e, l, r) -> if f e then true else aux (aux before l) r
    in
    aux false t

  let exists_withlabel f t =
    let rec aux before t =
      if before then true
      else
        match t with
        | Leaf -> false
        | Node (label, e, l, r) ->
            if f label e then true else aux (aux before l) r
    in
    aux false t

  let formal_layout flabel f tr =
    let rec aux = function
      | Leaf -> "Leaf"
      | Node (label, a, Leaf, Leaf) ->
          spf "LNodeS (%s, %s)" (flabel label) (f a)
      | Node (label, a, l, r) ->
          Printf.sprintf "LNode (%s, %s, %s, %s)" (flabel label) (f a) (aux l)
            (aux r)
    in
    aux tr

  let layout flabel f tr =
    let rec aux = function
      | Leaf -> "."
      | Node (label, a, Leaf, Leaf) ->
          Printf.sprintf "{%s, %s,}" (flabel label) (f a)
      | Node (label, a, l, r) ->
          Printf.sprintf "{%s, %s, %s, %s}" (flabel label) (f a) (aux l) (aux r)
    in
    aux tr

  let rec leaf eq t u =
    let nochild l r = match (l, r) with Leaf, Leaf -> true | _, _ -> false in
    match t with
    | Leaf -> false
    | Node (_, a, l, r) -> (eq a u && nochild l r) || leaf eq l u || leaf eq r u

  let rec node eq t u =
    let haschild l r =
      match (l, r) with
      | Node (_, _, _, _), _ | _, Node (_, _, _, _) -> true
      | _, _ -> false
    in
    match t with
    | Leaf -> false
    | Node (_, a, l, r) ->
        (eq a u && haschild l r) || node eq l u || node eq r u

  let left_child eq t u v =
    let rec aux before t =
      if before then true
      else
        match t with
        | Leaf -> false
        | Node (_, a, l, r) ->
            if eq a u && exists (fun x -> eq x v) l then true
            else aux (aux false l) r
    in
    aux false t

  let right_child eq t u v =
    let rec aux before t =
      if before then true
      else
        match t with
        | Leaf -> false
        | Node (_, a, l, r) ->
            if eq a u && exists (fun x -> eq x v) r then true
            else aux (aux false l) r
    in
    aux false t

  let parallel_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (_, _, l, r) ->
          (exists (fun x -> eq x u) l && exists (fun x -> eq x v) r)
          || aux l || aux r
    in
    aux t

  let left_adj_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (_, x, Node (_, y, _, _), _) when eq x u && eq y v -> true
      | Node (_, _, l, r) -> aux l || aux r
    in
    aux t

  let right_adj_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (_, x, _, Node (_, y, _, _)) when eq x u && eq y v -> true
      | Node (_, _, l, r) -> aux l || aux r
    in
    aux t

  let parallel_adj_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (_, _, Node (_, x, _, _), Node (_, y, _, _)) when eq x u && eq y v
        ->
          true
      | Node (_, _, l, r) -> aux l || aux r
    in
    aux t

  let eq lcompare compare t1 t2 =
    let rec aux = function
      | Leaf, Leaf -> true
      | Node (lab1, a1, l1, r1), Node (lab2, a2, l2, r2) ->
          lcompare lab1 lab2 && compare a1 a2 && aux (l1, l2) && aux (r1, r2)
      | _, _ -> false
    in
    aux (t1, t2)

  let rec flatten = function
    | Leaf -> []
    | Node (_, a, l, r) -> a :: (flatten l @ flatten r)

  let flatten_forall t = List.remove_duplicates (flatten t)

  (* let union l0 l1 = List.union (fun x y -> x == y) l0 l1 *)

  let once f tr e =
    let l = flatten tr in
    List.once f l e

  let compare e_compare t1 t2 =
    let rec aux t1 t2 =
      match (t1, t2) with
      | Leaf, Leaf -> 0
      | Leaf, Node _ -> -1
      | Node _, Leaf -> 1
      | Node (_, a1, l1, r1), Node (_, a2, l2, r2) ->
          let c = e_compare a1 a2 in
          if c != 0 then c
          else
            let c = aux l1 l2 in
            if c != 0 then c else aux r1 r2
    in
    aux t1 t2

  let last t i =
    let rec aux = function
      | Leaf -> false
      | Node (_, x, Leaf, Leaf) -> x == i
      | Node (_, x, l, r) -> x == i || aux l || aux r
    in
    aux t

  let drop_bottom tr =
    let depth = deep tr in
    let rec aux d = function
      | Leaf -> Leaf
      | Node (label, x, l, r) ->
          if depth == d + 1 then Leaf
          else Node (label, x, aux (d + 1) l, aux (d + 1) r)
    in
    aux 0 tr

  let is_strict_sort t =
    let rec aux (lower, upper) = function
      | Leaf -> true
      | Node (_, x, l, r) ->
          let b =
            match (lower, upper) with
            | None, None -> true
            | Some lower, None -> x > lower
            | None, Some upper -> x < upper
            | Some lower, Some upper -> x > lower && x < upper
          in
          b && aux (lower, Some x) l && aux (Some x, upper) r
    in
    aux (None, None) t

  let is_rb_alt t =
    let rec aux label = function
      | Leaf -> true
      | Node (label', _, l, r) -> (
          match (label, label') with
          | true, true -> false
          | _, _ -> aux label' l && aux label' r)
    in
    match t with
    | Leaf -> true
    | Node (_, _, l, r) -> aux false l && aux false r
end
