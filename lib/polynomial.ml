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
  | x::t -> 
    if not (x = Z.zero) then
      Printf.printf "%ax^%d + " Z.output x i;
    aux t (i+1)
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

let codageArbre alpha a = feuilles (arbreRestes a (arbreSousProduits alpha)) [] 

let lagrange alphas alpha_i = 
  Printf.printf "lagrange\n";
  List.fold_left (fun prod alpha -> 
  if alpha <> alpha_i then 
    produit_rapide prod (produit_scalaire [Field.neg alpha;Field.one] (Field.inv (Field.(-) alpha_i alpha)))
  else prod) [Field.one] alphas

let lagrange_interpolation p alphas = List.fold_left (fun sum alpha -> addition sum (produit_scalaire (lagrange alphas alpha) (valeur p alpha))) [] alphas

let lagrange_interpolation_eval alphas evals = List.fold_left2 (fun sum alpha eval -> addition sum (produit_scalaire (lagrange alphas alpha) eval)) [] alphas evals

let horner_eval poly x0 = 
  let r_poly = List.rev poly in
  let rec aux a_n = function
    | h::t -> aux (Field.(+) h (Field.( * ) a_n x0)) t
    | [] -> a_n
  in aux (List.hd r_poly) (List.tl r_poly)

let rec split = function
  | [] -> [],[]
  | e::[] -> [e],[]
  | e::o::t -> 
    let even, odd = split t in
    e::even, o::odd

let print_arr a =
  for i = 0 to (Array.length a  - 1) do
    Printf.printf "%d: " i;
    Z.print a.(i);
    Printf.printf "\n";
  done;
  Printf.printf "\n\n"

let rec fft poly = 
  let d = deg poly +1 in
  if d = 0 then begin
    [|Field.zero|]
  end else if d = 1 then begin
    [|List.hd poly|]
  end else begin
    Printf.printf "%f\n" (log(float_of_int (d))/.log(2.)); 
    assert (Float.is_integer (log(float_of_int (d))/.log(2.)));
    let order = Z.of_int (d) in
    let w = Field.( ** ) Field.generator (Field.(/) Field.order order) in
    Printf.printf "W = ";
    Z.print w;
    Printf.printf "\n";
    assert (Z.equal (Field.( ** ) w order) Z.one);
    let x = Array.make ((d)/2) Field.zero in
    x.(0) <- w;
    for i = 1 to (d/2-1) do
      x.(i) <- (Field.( * ) x.(i-1) w);
    done;
    let y = Array.make d Z.zero in
    let even, odd = split poly in
    Printf.printf "e len: %d\n" (List.length even);
    Printf.printf "o len: %d\n" (List.length odd);
    let e_y = fft even in
    let o_y = fft odd in
    for i = 0 to d/2-1 do
      y.(i) <- Field.(+) e_y.(i) (Field.( * ) x.(i) o_y.(i));
      y.(i + d/2) <- Field.(-) e_y.(i) (Field.( * ) x.(i) o_y.(i)); 
    done;
    print_arr x;
    y
  end

let rec ifft y =
  let l = Array.length y in
  if l = 1 then
    y
  else 
    let o_y = Array.make (l/2) Z.zero in
    let e_y = Array.make (l/2) Z.zero in
    let w = Field.( ** ) Field.generator (Field.(/) Field.order (Z.of_int l)) in 
    Printf.printf "W = ";
    Z.print w;
    Printf.printf "\n";
    let x = Array.make (l/2) Z.zero in
    for i = 0 to (l/2-1) do
      e_y.(i) <- Field.(/) (Field.(+) y.(i) y.(i+l/2)) (Z.of_int 2);
      o_y.(i) <- Field.(/) (Field.(-) y.(i) y.(i+l/2)) (Field.( * ) (Field.( ** ) w (Z.of_int (i+1))) (Z.of_int 2));
      x.(i) <- (Field.( ** ) w (Z.of_int (i+1))); 
    done;
    Printf.printf "x\n";
    print_arr x;
    Printf.printf "e\n";
    print_arr e_y;
    Printf.printf "o\n";
    print_arr o_y;
    let o = ifft o_y in
    let e = ifft e_y in
    Printf.printf "Odd: \n";
    print_arr o;
    Printf.printf "Even: \n";
    print_arr e;
    let a = Array.make l Z.zero in
    for i = 0 to (l/2-1) do
      a.(2*i) <- e.(i);
      a.(2*i+1) <- o.(i);
    done;
    a

    