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