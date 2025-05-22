type poly = Field.t list;;

let ln_bar ~total =
  let open Progress.Line in
  list [ spinner (); bar total; count_to total ]

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
  in match r_poly with
  | [] -> Field.zero
  | h::t -> aux h t

let split poly = 
  let rec aux poly even odd x = match poly with
    | [] -> List.rev even, List.rev odd
    | h::t when x mod 2 = 0 -> aux t (h::even) odd (x+1)
    | h::t -> aux t (even) (h::odd) (x+1)
  in aux poly [] [] 0

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
  Array.to_list (ifft e_y)

let random_poly (n : int) (max_coeff : Z.t) : poly =
  let rec aux acc i =
    if i = 0 then acc
    else aux (Z.random_int max_coeff :: acc) (i - 1)
  in
  aux [] n

let naive_prod u v = 
  let rec aux a b = match a with 
  | [] -> []
  | a::at -> (dot_prod b a)::(aux at (Field.zero::b))
in List.fold_left (fun a u -> add u a) [] (aux u v)

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

let multiple_prod polynomials = 
  let rec aux b len f = 
    if len = 0 then f []
    else if len= 1 then f polynomials.(b)
    else 
      let mid = len/2 in
      aux b mid (fun left ->
        aux (b+mid) (len-mid) (fun right ->
          f (prod left right)
        )  
      )
  in aux 0 (Array.length polynomials) (fun x -> x)

let produit u v = 
  let rec aux a b = match a with 
  | [] -> []
  | a::at -> (dot_prod b a)::(aux at (Field.zero::b))
in List.fold_left (fun a u -> add u a) [] (aux u v)

let multiple_add polynomials = 
  let rec aux b len f = 
    if len = 0 then f []
    else if len= 1 then f polynomials.(b)
    else 
      let mid = len/2 in
      aux b mid (fun left ->
        aux (b+mid) (len-mid) (fun right ->
          f (add left right)
        )  
      )
  in aux 0 (Array.length polynomials) (fun x -> x)

let divide_by_linear poly alpha =
  let reversed_poly = List.rev poly in
  let rec horner acc = function
    | [] -> ( 
        let quotient_with_remainder = List.rev acc in
        match quotient_with_remainder with
        | [] -> ([], Field.zero)  
        | [remainder] -> ([], remainder)  
        | _ -> 
            let quotient = List.tl quotient_with_remainder in
            (List.rev quotient, List.hd quotient_with_remainder)
      )
    | h::t -> 
        let new_head = Field.(+) h (Field.( * ) alpha (List.hd acc)) in
        horner (new_head :: acc) t 
  in
  match reversed_poly with
  | [] -> []  
  | h::t -> 
      let (quotient, _) = horner [h] t in
      List.tl quotient

let lagrange_numerator alphas = multiple_prod (Array.map (fun alpha -> [Field.neg (alpha);Field.one]) alphas)

let lagrange_polynomial alphas i n =
  let d = (Array.fold_left (fun p x -> if x = alphas.(i) then p else (Field.( * ) p (Field.(-) alphas.(i) x))) Field.one alphas) in
  let l = dot_prod (divide_by_linear n alphas.(i)) (Field.inv d) in
  l

let lagrange_interpolation x y = 
  let numerator = lagrange_numerator x in
  let len = Array.length x in
  let lagrange_polynomials = Array.make len [] in 
  Progress.with_reporter (ln_bar ~total:len) (fun f ->
    for i = 0 to (len-1) do
      lagrange_polynomials.(i) <- (lagrange_polynomial x i numerator);
      f 1;
    done;
  );
  let s = multiple_add (Array.map2 (fun lagrange e -> dot_prod lagrange e) lagrange_polynomials y) in
  s