module TreeTailCall = struct
  open Ztree.Tree

  let deep tree =
    let rec aux m = function
      | [] -> m
      | (depth, Leaf) :: t -> aux (max depth m) t
      | (depth, Node (_, l, r)) :: t ->
          aux m ((depth + 1, l) :: (depth + 1, r) :: t)
    in
    aux 0 [ (0, tree) ]
end

module LabeledTreeTailCall = struct
  open Zlabeled_tree.LabeledTree

  let deep tree =
    let rec aux m = function
      | [] -> m
      | (depth, Leaf) :: t -> aux (max depth m) t
      | (depth, Node (_, _, l, r)) :: t ->
          aux m ((depth + 1, l) :: (depth + 1, r) :: t)
    in
    let r = aux 0 [ (0, tree) ] in
    (* Printf.printf "deep: %i\n" r; *)
    r
end

module BinomialhpTailCall = struct
  open Zbinomialhp

  let deep_ tree =
    match Zlist.IntList.max_opt @@ List.map rank tree with
    | None -> List.length tree
    | Some x -> max x @@ List.length tree

  let deep tree =
    (* let _ = Printf.printf "deep\n" in *)
    let x = deep_ tree in
    (* let _ = Printf.printf "deep: %i\n" x in *)
    x
end

module SkewhpTailCall = struct
  open Zskewhp

  let deep_ tree =
    match Zlist.IntList.max_opt @@ List.map rank tree with
    | None -> List.length tree
    | Some x -> max x @@ List.length tree

  let deep t =
    (* let _ = Printf.printf "deep\n" in *)
    let x = deep_ t in
    (* Printf.printf "deep end\n"; *)
    x
end

module PairinghpTailCall = struct
  open Zpairinghp

  let deep tree =
    let rec aux m = function
      | [] -> m
      | (depth, E) :: t ->
          (* let _ = Printf.printf "E; depth: %i; m: %i\n" depth m in *)
          aux (max depth m) t
      | (depth, T (_, [])) :: t -> aux (max depth m) t
      | (depth, T (_, ls)) :: t ->
          (* let _ = *)
          (*   Printf.printf "len(ls) = %i; depth: %i\n" (List.length ls) depth *)
          (* in *)
          let ls = List.map (fun x -> (depth + 1, x)) ls in
          aux m (ls @ t)
    in
    let r = aux 0 [ (0, tree) ] in
    (* Printf.printf "deep: %i\n" r; *)
    r
end
