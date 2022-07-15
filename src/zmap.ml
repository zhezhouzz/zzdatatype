module List = Zlist.List

module MyMap (Ord : Map.OrderedType) = struct
  include Map.Make (Ord)

  let spf = Printf.sprintf

  let find info m k =
    match find_opt k m with
    | None -> raise @@ failwith @@ spf "%s:%s" __MODULE__ info
    | Some v -> v

  let find_opt m k = find_opt k m

  let to_value_list m = fold (fun _ v l -> v :: l) m []

  let to_key_list m = fold (fun k _ l -> k :: l) m []

  let to_kv_list m = fold (fun k v l -> (k, v) :: l) m []

  let from_kv_list l = List.fold_left (fun m (k, v) -> add k v m) empty l

  let from_klist_vlist_consistent_exn kl vl =
    if List.length kl != List.length vl then
      raise
      @@ failwith
           (spf "[%s]; then number keys and values has different" __MODULE__)
    else
      List.fold_left
        (fun m (k, v) ->
          match find_opt m k with
          | Some v' ->
              if Ord.compare v v' == 0 then m
              else
                raise
                @@ failwith
                     (spf "[%s]; the key has different values" __MODULE__)
          | None -> add k v m)
        empty
      @@ List.combine kl vl

  let force_update_list m l =
    List.fold_left (fun m (k, v) -> update k (fun _ -> Some v) m) m l
end

module IntMap = MyMap (struct
  type t = int

  let compare = compare
end)

module StrMap = MyMap (String)

module IntListMap = MyMap (struct
  type t = int list

  let compare = List.compare compare
end)
