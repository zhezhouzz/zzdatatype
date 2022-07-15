module List = Zlist.List

module Tree = struct
  type 'a t = Leaf | Node of ('a * 'a t * 'a t) [@@deriving sexp]

  let rec map f = function
    | Leaf -> Leaf
    | Node (x, a, b) -> Node (f x, map f a, map f b)

  let destruct_opt = function Leaf -> None | Node (x, a, b) -> Some (x, a, b)

  let add_to_bottom_left x tr =
    let rec aux = function
      | Leaf -> (1, Node (x, Leaf, Leaf))
      | Node (y, l, r) ->
          let ll, l' = aux l in
          let lr, r' = aux r in
          if lr < ll then (lr + 1, Node (y, l, r'))
          else (ll + 1, Node (y, l', r))
    in
    snd @@ aux tr

  let add_to_bottom_right x tr =
    let rec aux = function
      | Leaf -> (1, Node (x, Leaf, Leaf))
      | Node (y, l, r) ->
          let ll, l' = aux l in
          let lr, r' = aux r in
          if ll < lr then (ll + 1, Node (y, l', r))
          else (lr + 1, Node (y, l, r'))
    in
    snd @@ aux tr

  let deep t =
    let rec aux = function
      | Leaf -> 0
      | Node (_, l, r) ->
          let ln = aux l in
          let rn = aux r in
          if ln > rn then ln + 1 else rn + 1
    in
    aux t

  let drop_bottom tr =
    let depth = deep tr in
    let rec aux d = function
      | Leaf -> Leaf
      | Node (x, l, r) ->
          if depth == d + 1 then Leaf else Node (x, aux (d + 1) l, aux (d + 1) r)
    in
    aux 0 tr

  let rec size = function Leaf -> 0 | Node (_, a, b) -> 1 + size a + size b

  let flip tr = match tr with Leaf -> Leaf | Node (a, b, c) -> Node (a, c, b)

  let rec rec_flip tr =
    match tr with
    | Leaf -> Leaf
    | Node (a, b, c) -> Node (a, rec_flip c, rec_flip b)

  let rotation_right_opt tr =
    match tr with
    | Leaf -> Some Leaf
    | Node (x, Node (y, a, b), c) -> Some (Node (y, a, Node (x, b, c)))
    | _ -> None

  let rotation_left_opt tr =
    match tr with
    | Leaf -> Some Leaf
    | Node (x, a, Node (y, b, c)) -> Some (Node (y, Node (x, a, b), c))
    | _ -> None

  let rec append_to_left_most x tr =
    match tr with
    | Leaf -> Node (x, Leaf, Leaf)
    | Node (y, a, b) -> Node (y, append_to_left_most x a, b)

  let rec append_to_right_most x tr =
    match tr with
    | Leaf -> Node (x, Leaf, Leaf)
    | Node (y, a, b) -> Node (y, a, append_to_right_most x b)

  let max_opt (e_compare : 'a -> 'a -> int) t1 =
    let rec aux max_e = function
      | Leaf -> max_e
      | Node (a, b, c) ->
          let max_e =
            match max_e with
            | None -> a
            | Some max_e -> if e_compare a max_e > 0 then a else max_e
          in
          aux (aux (Some max_e) b) c
    in
    aux None t1

  let min_opt e_compare t1 = max_opt (fun x y -> ~-(e_compare x y)) t1

  let exists f t =
    let rec aux = function
      | [] -> false
      | Leaf :: t -> aux t
      | Node (x, l, r) :: t -> if f x then true else aux (l :: r :: t)
    in
    aux [ t ]

  let spf = Printf.sprintf

  let formal_layout f tr =
    let rec aux = function
      | Leaf -> "Leaf"
      | Node (a, Leaf, Leaf) -> spf "NodeS %s" (f a)
      | Node (a, l, r) ->
          Printf.sprintf "Node (%s, %s, %s)" (f a) (aux l) (aux r)
    in
    aux tr

  let layout f tr =
    let rec aux = function
      | Leaf -> "."
      | Node (a, Leaf, Leaf) -> f a
      | Node (a, l, r) -> Printf.sprintf "{%s, %s, %s}" (aux l) (f a) (aux r)
    in
    aux tr

  let leaf eq t u =
    let rec aux = function
      | [] -> false
      | Leaf :: t -> aux t
      | Node (x, Leaf, Leaf) :: t -> if eq x u then true else aux t
      | Node (_, Leaf, r) :: t -> aux (r :: t)
      | Node (_, l, Leaf) :: t -> aux (l :: t)
      | Node (_, l, r) :: t -> aux (l :: r :: t)
    in
    aux [ t ]

  let node eq t u =
    let rec aux = function
      | [] -> false
      | Leaf :: t -> aux t
      | Node (_, Leaf, Leaf) :: t -> aux t
      | Node (x, Leaf, r) :: t -> if eq x u then true else aux (r :: t)
      | Node (x, l, Leaf) :: t -> if eq x u then true else aux (l :: t)
      | Node (x, l, r) :: t -> if eq x u then true else aux (l :: r :: t)
    in
    aux [ t ]

  let left_child eq t u v =
    let rec aux = function
      | [] -> false
      | Leaf :: t -> aux t
      | Node (x, l, r) :: t ->
          if eq x u && exists (fun x -> eq x v) l then true
          else aux (l :: r :: t)
    in
    aux [ t ]

  let right_child eq t u v =
    let rec aux = function
      | [] -> false
      | Leaf :: t -> aux t
      | Node (x, l, r) :: t ->
          if eq x u && exists (fun x -> eq x v) r then true
          else aux (l :: r :: t)
    in
    aux [ t ]

  let parallel_child eq t u v =
    let rec aux = function
      | [] -> false
      | Leaf :: t -> aux t
      | Node (_, l, r) :: t ->
          if exists (fun x -> eq x u) l && exists (fun x -> eq x v) r then true
          else aux (l :: r :: t)
    in
    aux [ t ]

  let left_adj_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (x, Node (y, _, _), _) when eq x u && eq y v -> true
      | Node (_, l, r) -> aux l || aux r
    in
    aux t

  let right_adj_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (x, _, Node (y, _, _)) when eq x u && eq y v -> true
      | Node (_, l, r) -> aux l || aux r
    in
    aux t

  let parallel_adj_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (_, Node (x, _, _), Node (y, _, _)) when eq x u && eq y v -> true
      | Node (_, l, r) -> aux l || aux r
    in
    aux t

  let complete t u =
    let rec aux incompeletes = function
      | _, Leaf -> raise @@ failwith "never happen"
      | 0, Node (_, Leaf, Leaf) -> raise @@ failwith "never happen"
      | 1, Node (_, Leaf, Leaf) -> incompeletes
      | _, Node (x, Leaf, Leaf) -> x :: incompeletes
      | n, Node (x, Leaf, r) -> aux (x :: incompeletes) (n - 1, r)
      | n, Node (x, l, Leaf) -> aux (x :: incompeletes) (n - 1, l)
      | n, Node (_, l, r) -> aux (aux incompeletes (n - 1, l)) (n - 1, r)
    in
    List.exists (fun x -> x == u) @@ aux [] (deep t, t)

  let eq compare t1 t2 =
    let rec aux = function
      | Leaf, Leaf -> true
      | Node (a1, l1, r1), Node (a2, l2, r2) ->
          if compare a1 a2 then if aux (l1, l2) then aux (r1, r2) else false
          else false
      | _, _ -> false
    in
    aux (t1, t2)

  let rec flatten = function
    | Leaf -> []
    | Node (a, l, r) -> a :: (flatten l @ flatten r)

  let flatten_forall t = List.remove_duplicates (flatten t)

  let once f tr e =
    let l = flatten tr in
    List.once f l e

  let compare e_compare t1 t2 =
    let rec aux t1 t2 =
      match (t1, t2) with
      | Leaf, Leaf -> 0
      | Leaf, Node _ -> -1
      | Node _, Leaf -> 1
      | Node (a1, l1, r1), Node (a2, l2, r2) ->
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
      | Node (x, Leaf, Leaf) -> x == i
      | Node (x, l, r) -> x == i || aux l || aux r
    in
    aux t

  let is_strict_sort t =
    let rec aux (lower, upper) = function
      | Leaf -> true
      | Node (x, l, r) ->
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

  let is_prefix t1 t2 =
    let rec aux = function
      | Leaf, _ -> true
      | Node (_, _, _), Leaf -> false
      | Node (x1, l1, r1), Node (x2, l2, r2) ->
          x1 == x2 && aux (l1, l2) && aux (r1, r2)
    in
    aux (t1, t2)

  let is_children_diff t =
    let rec aux = function
      | Leaf | Node (_, Leaf, _) | Node (_, _, Leaf) -> true
      | Node (_, Node (x1, l1, r1), Node (x2, l2, r2)) ->
          x1 != x2 && aux l1 && aux r1 && aux l2 && aux r2
    in
    aux t
end
