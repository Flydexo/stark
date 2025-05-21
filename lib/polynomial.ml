type poly = Field.t list;;

let rec add a b = match (a,b) with
  | [], [] -> []
  | [], b::bt -> b::(add [] bt)
  | a::at, [] -> a::(add [] at)
  | a::at, b::bt -> (Field.(+) a b)::(add at bt)

let rec sub u v = match (u,v) with
  | _, [] -> u
  | [], b::bt -> (Field.neg b)::(sub [] bt)
  | a::at, b::bt -> (Field.(-) a b)::(sub at bt)

let rec dot_prod u lambda = match u with
  | []  -> []
  | a::at -> (Field.( * ) lambda a)::(dot_prod at lambda)

let eval poly x0 = 
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

let deg p = List.length p;;

let next_pow2 d = Float.to_int (2. ** Float.ceil (log(float_of_int(d))/.log(2.)))

let fft poly n = 
  let rec _fft poly d = 
    Printf.printf "Poly length: %d\n" (List.length poly);
    if d = 0 then begin
      [|Field.zero|]
    end else if d = 1 then begin
      try 
        [|List.hd poly|]
      with
      | _ -> [|Field.zero|]
    end else begin
      let d = next_pow2 d in
      let order = Z.of_int d in
      let w = Field.( ** ) Field.generator (Field.(/) Field.order order) in
      assert (Z.equal (Field.( ** ) w order) Z.one);
      let x = Array.make ((d)/2) Field.zero in
      x.(0) <- w;
      for i = 1 to (d/2-1) do
        x.(i) <- (Field.( * ) x.(i-1) w);
      done;
      let y = Array.make d Z.zero in
      let even, odd = split poly in
      let e_y = _fft even (d/2) in
      let o_y = _fft odd (d/2) in
      for i = 0 to d/2-1 do
        y.(i) <- Field.(+) e_y.(i) (Field.( * ) x.(i) o_y.(i));
        y.(i + d/2) <- Field.(-) e_y.(i) (Field.( * ) x.(i) o_y.(i)); 
      done;
      y
    end
  in _fft poly n

let rec ifft y =
  let l = Array.length y in
  if l = 1 then
    y
  else 
    let o_y = Array.make (l/2) Z.zero in
    let e_y = Array.make (l/2) Z.zero in
    let w = Field.( ** ) Field.generator (Field.(/) Field.order (Z.of_int l)) in 
    let x = Array.make (l/2) Z.zero in
    for i = 0 to (l/2-1) do
      e_y.(i) <- Field.(/) (Field.(+) y.(i) y.(i+l/2)) (Z.of_int 2);
      o_y.(i) <- Field.(/) (Field.(-) y.(i) y.(i+l/2)) (Field.( * ) (Field.( ** ) w (Z.of_int (i+1))) (Z.of_int 2));
      x.(i) <- (Field.( ** ) w (Z.of_int (i+1))); 
    done;
    let o = ifft o_y in
    let e = ifft e_y in
    let a = Array.make l Z.zero in
    for i = 0 to (l/2-1) do
      a.(2*i) <- e.(i);
      a.(2*i+1) <- o.(i);
    done;
    a

let real_deg p =
  let rec aux p nz z = match p with
  | [] -> nz
  | x::p when x = Field.zero -> aux p nz (z+1)
  | _::p -> (aux p (nz+z+1) 0 )
  in aux p 0 0

let zeropad a b =
  let da, db = real_deg a, real_deg b in
  let m = da + db in
  let l = Float.to_int (2. ** Float.ceil (log(float_of_int(m))/.log(2.))) in
  let ap = List.init (l -  da) (fun _ -> Field.zero) in
  let bp = List.init (l - db) (fun _ -> Field.zero) in
  a@ap, b@bp

let format_fft a b = 
  let da, db = real_deg a, real_deg b in
  let m = da + db in
  let l = Float.to_int (2. ** Float.ceil (log(float_of_int(m))/.log(2.))) in
  l 

let prod a b = 
  let d = format_fft a b in
  let e_a = fft a d in
  let e_b = fft b d in
  let e_y = Array.map2 (fun a b -> Field.( * ) a b) e_a e_b in
  Printf.printf "\n\nProd!!\n\n";
  Array.to_list (ifft e_y)

let random_poly (n : int) (max_coeff : Z.t) : poly =
  let rec aux acc i =
    if i = 0 then acc
    else aux (Z.random_int max_coeff :: acc) (i - 1)
  in
  aux [] n

(* let produit u v = 
  let rec aux a b = match a with 
  | [] -> []
  | a::at -> (produit_scalaire b a)::(aux at (Field.zero::b))
in List.fold_left (fun a u -> addition u a) [] (aux u v)
 *)
let print_poly p = 
  let rec aux p i = match p with
  | [] -> ();
  | x::t -> 
    if not (x = Z.zero) then
      Printf.printf "%ax^%d + " Z.output x i;
    aux t (i+1)
in aux p 0; Printf.printf "\n"

let rec monomial coeff = function
 | 0 -> [coeff]
 | k -> Field.zero::(monomial coeff (k-1))

let division a b = 
  let d = format_fft a b in
  let e_a = fft a d in
  let e_b = fft b d in
  let e_y = Array.map2 (fun a b -> Field.( / ) a b) e_a e_b in
  Array.to_list (ifft e_y)

let modulo u v = sub u (prod (division u v) v)

let rec decoupe u n =
  if n=0 then ([],u,List.hd u)
  else if n = 1 then ([List.hd u], List.tl u, List.hd u)
  else 
    let (ub,uh,lu)=decoupe (List.tl u) (n-1) in
    (((List.hd u)::ub),uh,lu) ;;

let rec decale p e =
  if e=0 then p
  else Field.zero::(decale p (e-1)) ;;

let rec ecrete p n =
    if n=0 then []
    else (List.hd p)::(ecrete (List.tl p) (n-1)) ;;

let ajoute vb n =
  if n<>0 then List.rev (decale (List.rev vb) n) else vb;;

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
      | Noeud(gp,_,_), Noeud(dp,_,_) -> Noeud((prod gp dp),g,d);
      | _ -> failwith "Should not happend"
  in aux roots (List.length roots)

let rec arbreRestes a = function
| Vide -> Vide
| Noeud(m,g,d) -> Noeud(modulo a m, arbreRestes a g, arbreRestes a d)

let rec feuilles t acc = match t with
| Vide -> []
| Noeud(p, Vide, Vide) -> (Field.neg (List.hd p))::acc
| Noeud(_, t1, t2) -> feuilles t1 (feuilles t2 acc) 

let codageArbre alpha a = feuilles (arbreRestes a (arbreSousProduits alpha)) [] 

let lagrange alphas alpha_i = 
  List.fold_left (fun p alpha -> 
  if alpha <> alpha_i then 
    prod p (dot_prod [Field.neg alpha;Field.one] (Field.inv (Field.(-) alpha_i alpha)))
  else p) [Field.one] alphas

let lagrange_interpolation p alphas = List.fold_left (fun sum alpha -> add sum (dot_prod (lagrange alphas alpha) (eval p alpha))) [Field.zero] alphas

let lagrange_interpolation_eval alphas evals = List.fold_left2 (fun sum alpha eval -> add sum (dot_prod (lagrange alphas alpha) eval)) [] alphas evals

let produit u v = 
  let rec aux a b = match a with 
  | [] -> []
  | a::at -> (dot_prod b a)::(aux at (Field.zero::b))
in List.fold_left (fun a u -> add u a) [] (aux u v)


let l_i alphas i =
  let p = ref [Field.one] in
  for j = 0 to (Array.length alphas -1) do
    Printf.printf "l_i %d\n" j;
    if j <> i then
      p := prod (!p) (dot_prod ([Field.neg (alphas.(j));Field.one]) (Field.inv (Field.(-) alphas.(i) alphas.(j))));
    print_poly !p;
  done;
  !p

let lg alphas evals = 
  let s = ref [Field.zero] in
  for i = 0 to (Array.length alphas - 1) do
    Printf.printf "%d\n" i;
    s := add (!s) (dot_prod (l_i alphas i) evals.(i));
  done;
  !s