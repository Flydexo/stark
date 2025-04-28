type poly = Field.t list;;

let valeur p x = fst(List.fold_left (fun (acc, x_i) coeff -> (Field.(+) acc (Field.( * ) coeff x_i), Field.( * ) x_i x)) (Field.zero, Field.one) p)

let rec addition a b = match (a,b) with
  | [], [] -> []
  | [], b::bt -> b::(addition [] bt)
  | a::at, [] -> a::(addition [] at)
  | a::at, b::bt -> (Field.(+) a b)::(addition at bt)

let rec soustraction u v = match (u,v) with
  | _, [] -> u
  | [], b::bt -> (Field.neg b)::(soustraction [] bt)
  | a::at, b::bt -> (Field.(-) a b)::(soustraction at bt)

let rec produit_scalaire u lambda = match u with
  | []  -> []
  | a::at -> (Field.( * ) lambda a)::(produit_scalaire at lambda)

let produit u v = 
  let rec aux a b = match a with 
  | [] -> []
  | a::at -> (produit_scalaire b a)::(aux at (Field.zero::b))
in List.fold_left (fun a u -> addition u a) [] (aux u v)

let print_poly p = 
  let rec aux p i = match p with
  | [] -> ();
  | x::t -> Printf.printf "%ax^%d + " Z.output x i; aux t (i+1)
in aux p 0; Printf.printf "\n"

let deg p =
  let rec aux p i = match p with
  | [] -> -1
  | x::p when x = Field.zero -> aux p (i+1)
  | _::p -> i+1+(aux p 0)
in aux p 0

let rec monomial coeff = function
 | 0 -> [coeff]
 | k -> Field.zero::(monomial coeff (k-1))

let division u v = 
  let rv = List.rev v in
  let dv = deg v  in
  let rec div ru du acc =
    if du < dv then acc
    else 
      let c = (Field.(/) (List.hd ru) (List.hd rv)) in
      let d = produit_scalaire rv c in
      div (List.tl (soustraction ru d)) (du-1) (c::acc)
  in div (List.rev u) (deg u) []

let modulo u v = soustraction u (produit (division u v) v)

let rec decoupe u n =
  if n=0 then ([],u,List.hd u)
  else if n = 1 then ([List.hd u], List.tl u, List.hd u)
  else 
    let (ub,uh,lu)=decoupe (List.tl u) (n-1) in
    (((List.hd u)::ub),uh,lu) ;;

let rec decale p e =
  if e=0 then p
  else Field.zero::(decale p (e-1)) ;;

let normalize u v =
 let lu = List.length u in
 let lv = List.length v in
 if lu-lv>0 then
  (u,v@(List.init (lu-lv) (fun _ -> Field.zero))) 
 else 
  (u@(List.init (lv-lu) (fun _ -> Field.zero)),v)

let produit_rapide uu vv = 
 let (u',v') = normalize uu vv in
 print_poly u';
 print_poly v';
 let rec aux u v = function
  | 0 -> []
  | 1 -> [Field.( * ) (List.hd u) (List.hd v)]
  | l ->
      let e = l / 2 in 
      let ub, uh,_ = decoupe u e in
      let vb, vh,_ = decoupe v e in
      let wh = aux uh vh (l-e) in
      let wb = aux ub vb (e) in
      let prod = aux (addition uh ub) (addition vh vb) (l-e) in
      let wm =
        soustraction prod (addition wh wb)
      in addition (addition wb (decale wm (l/2))) (decale wh (2*(l/2))) 
  in aux u' v' (List.length u')

let rec ecrete p n =
    if n=0 then []
    else (List.hd p)::(ecrete (List.tl p) (n-1)) ;;

let ajoute vb n =
  if n<>0 then List.rev (decale (List.rev vb) n) else vb;;

let division_rapide u v = 
 let l = List.length v in
 assert ((List.length u) = 2*l-1);
 let rec div u v l = 
  if l = 1 then
    [Field.( / ) (List.hd u) (List.hd v)] 
  else
    let e = l/2 in
    let _,uh,lu = decoupe u (2*e) in
    let vb,vh,_ = decoupe v e in
    let qh = div uh vh (l-e) in
    let rh = ecrete (soustraction uh (produit_rapide qh vh)) (l-e) in
    let s = soustraction (addition (decale rh e) (monomial lu (e-1))) (produit_rapide qh (ajoute vb (l-2*e))) in
    let qb = div s vh (l-e) in
    let q = addition (decale qh e) qb in
    q
 in div u v l

let modulo_rapide u v = soustraction u (produit_rapide v (division_rapide u v))

type arbre = Vide
| Noeud of poly * arbre * arbre

let polynom_from_root r = [Field.neg r;Field.one]

let arbreSousProduits roots = 
  let rec aux roots l =
    if l = 1 then
      Noeud(polynom_from_root (List.hd roots),Vide,Vide)
    else 
      let ub,uh,_ = decoupe roots (l/2) in
      let g = aux ub (l/2) in
      let d = aux uh (l - l/2) in
      match (g,d) with
      | Noeud(gp,_,_), Noeud(dp,_,_) -> Noeud((produit_rapide gp dp),g,d);
      | _ -> failwith "Should not happend"
  in aux roots (List.length roots)

let rec arbreRestes a = function
| Vide -> Vide
| Noeud(m,g,d) -> Noeud(modulo_rapide a m, arbreRestes a g, arbreRestes a d)

let rec feuilles t acc = match t with
| Vide -> []
| Noeud(p, Vide, Vide) -> (Field.neg (List.hd p))::acc
| Noeud(_, t1, t2) -> feuilles t1 (feuilles t2 acc) 

(* Hassoul ça marche *)

let rec codageArbre alpha a = feuilles (arbreRestes a (arbreSousProduits alpha)) []