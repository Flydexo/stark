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

let modulo u v = soustraction u (division u v)

let rec decoupe u n=
  if n=0 then ([],u)
  else let (ub,uh)=decoupe (List.tl u) (n-1) in (((List.hd u)::ub),uh) ;;
let rec decale p e =
  if e=0 then p
  else Field.zero::(decale p (e-1)) ;;

let produit_rapide u v = 
 let rec aux u v = function
  | 0 -> []
  | 1 -> [Field.( * ) (List.hd u) (List.hd v)]
  | l ->
      let e = l / 2 in 
      let ub, uh = decoupe u e in
      let vb, vh = decoupe v e in
      let wh = aux uh vh (l-e) in
      let wb = aux ub vb (e) in
      let wm = soustraction ( soustraction (aux (addition uh ub) (addition vh vb) (l-e)) wb) wh in
      addition
        (
          addition 
            ( decale wh (2*e))
            (decale wm e)
        )
        wb
  in aux u v (List.length u)

(* TODO: Division et modulo rapide *)

let rec last = function
| [] -> failwith "last"
| [x] -> [x]
| _::tl -> last tl

let quotient_rapide u v = 
  (* u is of length 2l-1 and v of length l *)
  (* deg(v) = l-1, deg(u) <= 2l-1 *)
  (* e = l/2 u = ub@uh split in 2e *)
  (* v split into vb and vh with 2e *)
  (*  Attention, selon la parité de d, on a 2e = d ou 2e = d + 1. ????? *)
  let rec aux u v l =
    let e = l / 2 in
    let ub, uh = decoupe u (2*e) in
    let vb, vh = decoupe v (2*e) in
    let qh = aux uh vh l in
    let rh = soustraction uh (produit_rapide qh vh) in
    let s = soustraction (addition (decale rh e) (decale (last ub) (e-1))) (produit_rapide qh vb) in
    let qb = aux s vh l in
    addition (decale qh e) qb
  in aux u v (List.length u)

type arbre = Vide
| Noeud of poly * arbre * arbre

let polynom_from_root r = [Field.neg r;Field.one]