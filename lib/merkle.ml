type tree = Leaf of string * string | Node of tree * tree * string
type path = Left of string | Right of string

type t = {
  len : int;
  tree: tree
}

let hash s = Sha256.to_hex (Sha256.string s)

let rec print_str_list = function
| [] -> Printf.printf "\n"
| h::t -> Printf.printf "%s " h;print_str_list t

let construct leaves = 
  let len = List.length leaves in
  let rec aux leaves i =
    if i = 1 then
      let r = hash (List.hd leaves) in
      Leaf(List.hd leaves, r), List.tl leaves, r
    else begin
      let left_tree,remaining,l_root = aux leaves (i /2) in
      let right_tree,r_remaining,r_root = aux remaining (i - i /2) in
      let r = hash (String.concat "" [l_root; r_root]) in
      Node(left_tree, right_tree, r), r_remaining, r
    end
  in
  let tree,_,_ = aux leaves len in 
  {len=len;tree=tree;}
  
let _root t = match t with
  | Leaf(_,k) -> k
  | Node(_,_,k) -> k

let root t = _root t.tree

let get_authentication_path tree i = 
  let rec aux path t i = match t.tree with
    | Leaf(_,_) when i = 0 -> path
    | Node(l,r,_) -> 
      if i >= t.len/2 then begin
        Printf.printf "Left\n";
        aux (Left((_root l))::path) {len=t.len/2;tree=r} (i-t.len/2)
      end else begin 
        Printf.printf "Right\n";
        aux (Right((_root r))::path) {len=t.len - t.len/2;tree=l} i
      end
    | _ -> failwith "Should not happen";
  in aux [] tree i

let verify root (path:path list) value = 
  let rec aux computed_root = function
    | [] -> computed_root = root
    | h::t -> (
      let k = Sha256.to_hex (Sha256.string (
        match h with
        | Left node -> String.concat "" [node; computed_root]
        | Right node -> String.concat "" [computed_root; node]))
      in
      Printf.printf "%s\n" k;
      aux (k) t)
  in aux "" (Right(value)::path)