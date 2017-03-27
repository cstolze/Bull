open Utils

(* conversion functions bruijn <-> normal *)
(* TO FIX *)

(* TODO:
cf matita source code:
substitution DONE
lift DONE
fix_index => if the index are wrong and the ids are correct (for the *)
(* lexer) DONE
fix_id => if the ids are wrong and the index are correct (after beta-conversion)
also function for fixing Gamma

NOTE : WE DO NOT DEAL WITH META VARIABLES FOR NOW
 *)

(*
       match t with
  | Sort s ->
  | Prod (id1, t1, t2) ->
  | Abs (id1, t1, t2) ->
  | App (t1, t2) ->
  | Inter (t1, t2) ->
  | Union (t1, t2) ->
  | SPair (t1, t2) ->
  | SPrLeft t1 ->
  | SPrRight t1 ->
  | SMatch (t1, t2) ->
  | SInLeft (t1, t2) ->
  | SInRight (t1, t2) ->
  | Var b1 ->
  | Omega ->
  | Star ->
  | Meta b1 ->
     *)

(* Catamorphism iterator *)
(* goes recursively into most of the terms constructors *)
let cata_term f t =
  match t with
  | App (t1, t2) -> App (f t1, f t2)
  | Inter (t1, t2) -> Inter (f t1, f t2)
  | Union (t1, t2) -> Union (f t1, f t2)
  | SPair (t1, t2) -> SPair (f t1, f t2)
  | SPrLeft t1 -> SPrLeft (f t1)
  | SPrRight t1 -> SPrRight (f t1)
  | SMatch (t1, t2) -> SMatch (f t1, f t2)
  | SInLeft (t1, t2) -> SInLeft (f t1, f t2)
  | SInRight (t1, t2) -> SInRight (f t1, f t2)
  | _ -> t

(* Map iterator *)
(* inc modifies the counter h each time we add a level of abstraction *)
(* f is a function that maps De Bruijn indexes to terms *)

let map_term inc k f t =
  let rec aux k t =
    match t with
    | Prod (id1, t1, t2) -> Prod (id1, aux k t1, aux (inc k) t2)
    | Abs (id1, t1, t2) -> Abs (id1, aux k t1, aux (inc k) t2)
    | Var b1 -> f k b1
    | _ -> cata_term (aux k) t
  in aux k t

(* k is the index from which the context is changed *)
(* n is the shift *)
let lift k n =
  map_term (fun k -> k+1) k
	   (fun _ b -> match b with
		       | Bruijn (id, m)
			 -> if m < k then Var b
			    else Var(Bruijn (id, m+n)))

(* Transform (lambda x. t1) t2 into t1[t2/x] *)
let beta_redex t1 t2 =
  let aux k b =
    match b with
    | Bruijn (id, m)
      -> if m < k then Var b (* bound variable *)
	 else if m = k then (* x *)
	   lift 0 k t2
	 else (* the enclosing lambda goes away *)
	   Var (Bruijn (id, m-1))
  in map_term (fun k -> k+1) 0 aux t1

(* The indexes are broken during the parsing *)
(* Broken indexes have a negative value *)
let rec fix_index t =
  let aux id1 =
        map_term (fun k -> k+1) 0
	       (fun k b -> match b with
			   | Bruijn (id, m)
			     -> if id = id1 && m < 0 then
				  Var(Bruijn (id, k))
				else Var b) in
  match t with
  | Prod (id1, t1, t2) -> let t2' = fix_index t2 in
			  Prod (id1, fix_index t1, aux id1 t2')
  | Abs (id1, t1, t2) -> let t2' = fix_index t2 in
			  Abs (id1, fix_index t1, aux id1 t2')
  | _ -> cata_term fix_index t


(* !!!!!!!!!!!!!!!!!!!!!!!!! *)

let is_free id t =
  let rec aux k t =
    match t with
  | Prod (id1, t1, t2) -> aux k t1 && aux (k+1) t2
  | Abs (id1, t1, t2) -> aux k t1 && aux (k+1) t2
  | Var (Bruijn (id1, m)) -> if m >= k && id = id1 then true else false

let fix_id t =
  
     (* !!!!!!!!!!!!!!!!!!!!!!!!! *)

let rec f_replace f id n =
  match f with
  | BSFc (f1, f2) -> BSFc (f_replace f1 id n, f_replace f2 id (n+1))
  | BSProd (id', f1, f2) -> BSProd (id', f_replace f1 id n, f_replace f2 id (n+1))
  | BSLambda (id', f1, f2) -> BSLambda (id', f_replace f1 id n, f_replace f2 id (n+1))
  | BSApp (f1, d2) -> BSApp (f_replace f1 id n, d_replace d2 id n)
  | BSAnd (f1, f2) -> BSAnd (f_replace f1 id n, f_replace f2 id n)
  | BSOr (f1, f2) -> BSOr (f_replace f1 id n, f_replace f2 id n)
  | BSAtom id' -> f
  | BSOmega -> f
  | BSAnything -> f
  and
    d_replace d id n =
    match d with
    | BDVar (id', false, n') -> d
    | BDVar (id', true, n') -> if (n = n') then BDVar (id, true, n') else d
    | BDStar -> d
    | BDLambda (id', f1, d') -> BDLambda (id', f_replace f1 id n, d_replace d' id (n+1))
    | BDApp (d1, d2) -> BDApp (d_replace d1 id n, d_replace d2 id n)
    | BDAnd (d1, d2) -> BDAnd (d_replace d1 id n, d_replace d2 id n)
    | BDProjL d' -> BDProjL (d_replace d' id n)
    | BDProjR d' -> BDProjR (d_replace d' id n)
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       BDOr (id',
	     f_replace f' id n,
	     d_replace d' id (n+1),
	     id'',
	     f_replace f'' id n,
	     d_replace d'' id (n+1),
	     d_replace d''' id n)
    | BDInjL d' -> BDInjL (d_replace d' id n)
    | BDInjR d' -> BDInjR (d_replace d' id n)

let rec bruijn_to_family f =
  match f with
  | BSFc (f1, f2) -> SFc (bruijn_to_family f1, bruijn_to_family f2)
  | BSProd (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SProd (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSLambda (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SLambda (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSApp (f1, d2) -> SApp (bruijn_to_family f1, bruijn_to_delta d2)
  | BSAnd (f1, f2) -> SAnd (bruijn_to_family f1, bruijn_to_family f2)
  | BSOr (f1, f2) -> SOr (bruijn_to_family f1, bruijn_to_family f2)
  | BSAtom id -> SAtom id
  | BSOmega -> SOmega
  | BSAnything -> SAnything
  and
    bruijn_to_delta d =
    match d with
    | BDVar (id, b, n) -> DVar id
    | BDStar -> DStar
    | BDLambda (id, f1, d') -> let (id', d'') = alpha_conv id d' None d_check d_replace in DLambda (id', bruijn_to_family f1, bruijn_to_delta d'')
    | BDApp (d1, d2) -> DApp (bruijn_to_delta d1, bruijn_to_delta d2)
    | BDAnd (d1, d2) -> DAnd (bruijn_to_delta d1, bruijn_to_delta d2)
    | BDProjL d' -> DProjL (bruijn_to_delta d')
    | BDProjR d' -> DProjR (bruijn_to_delta d')
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       let (id'1, d'1) = alpha_conv id' d' None d_check d_replace in
       let (id''1, d''1) = alpha_conv id'' d'' None d_check d_replace in
       DOr (id'1, bruijn_to_family f', bruijn_to_delta d'1, id''1, bruijn_to_family f'', bruijn_to_delta d''1, bruijn_to_delta d''')
    | BDInjL d' -> DInjL (bruijn_to_delta d')
    | BDInjR d' -> DInjR (bruijn_to_delta d')

let rec bruijn_to_kind k =
  let rec k_check id k n =
    match k with
    | BType -> true
    | BKProd (id', f, k') -> (f_check id f n) && (k_check id k' (n+1))
  in
  let rec k_replace k id n =
    match k with
    | BType -> k
    | BKProd (id', f, k') -> BKProd (id', f_replace f id n, k_replace k' id (n+1))
  in
  match k with
  | BType -> Type
  | BKProd (id, f, k') -> let (id', k'') = alpha_conv id k' None k_check k_replace in KProd (id', bruijn_to_family f, bruijn_to_kind k'')
