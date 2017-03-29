open Utils

(* conversion functions bruijn <-> normal *)
(* TO FIX *)

(* TODO:
cf matita source code:
substitution DONE
lift DONE
fix_index => if the index are wrong and the ids are correct (for the *)
(* lexer) DONE
fix_id => if the ids are wrong and the index are correct (after beta-conversion) DONE
also function for fixing Gamma DONE

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

(* Visitor iterator *)
(* goes recursively into most of the terms constructors *)
let visit_term f g t =
  match t with
  | Prod (id1, t1, t2) -> Prod (id1, f t1, g id1 t2)
  | Abs (id1, t1, t2) -> Abs (id1, f t1, g id1 t2)
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
    | Var (Bruijn (id, n)) -> f k id n
    | _ -> visit_term (aux k) (fun id -> aux (inc id k)) t
  in aux k t

let map_term' = map_term (fun _ k -> k+1)

(* k is the index from which the context is changed *)
(* n is the shift *)
let lift k n =
  map_term' k
	   (fun _ id m -> if m < k then Var (Bruijn (id, m))
			  else Var(Bruijn (id, m+n)))

(* Transform (lambda x. t1) t2 into t1[t2/x] *)
let beta_redex t1 t2 =
  let aux k id m =
    if m < k then Var (Bruijn (id, m)) (* bound variable *)
    else if m = k then (* x *)
      lift 0 k t2
    else (* the enclosing lambda goes away *)
      Var (Bruijn (id, m-1))
  in map_term' 0 aux t1

(* The indexes are broken during the parsing *)
(* Broken indexes have a negative value *)

let rec fix_index sigma =
  map_term (fun id l ->
	    (* DefConst Omega is a hack *)
	    (id, DefConst Omega) :: l)
	   sigma
	   (fun l id m
	    ->
	    match (get_index id l) with
	    | None -> Var(Bruijn(id, -1)) (* ERROR *)
	    | Some n ->
	       Var(Bruijn (id, n)))



(* is_free id t = true iff id appears as a free variable in t *)
let is_free id t =
  let rec aux k t =
    match t with
    | Var (Bruijn (id1, m)) -> if m >= k && id = id1 then true
			       else false
    | SPrLeft t1 -> aux k t1
    | SPrRight t1 -> aux k t1
    | Prod (id1, t1, t2) -> aux k t1 || aux (k+1) t2
    | Abs (id1, t1, t2) -> aux k t1 || aux (k+1) t2
    | App (t1, t2) -> aux k t1 || aux (k+1) t2
    | Inter (t1, t2) -> aux k t1 || aux (k+1) t2
    | Union (t1, t2) -> aux k t1 || aux (k+1) t2
    | SPair (t1, t2) -> aux k t1 || aux (k+1) t2
    | SMatch (t1, t2) -> aux k t1 || aux (k+1) t2
    | SInLeft (t1, t2) -> aux k t1 || aux (k+1) t2
    | SInRight (t1, t2) -> aux k t1 || aux (k+1) t2
    | _ -> false
  in aux 0 t

(* find a fresh name for base_id (for alpha-conversion) *)
(* we suppose is_free base_id t = true *)
let new_ident base_id t =
  let rec aux k =
    let id = base_id ^ (string_of_int k) in
    if is_free id t then aux (k+1) else id
  in aux 0

(* The ids are broken during beta-reduction *)
let rec fix_id t =
  let aux id t =
    if is_free id t then
      let new_id = new_ident id t in
      fix_id @@ map_term' 0
		(fun k id n
		 -> Var (Bruijn (new_id, n))) t
    else fix_id t
  in visit_term fix_id aux t

(* gives the essence and type of the term of index n *)

let get sigma gamma n =
  let rec get f err n l =
    match l with
    | [] -> err n (* we suppose the index is correct *)
    | x :: l' -> if n = 0 then f x else get f err (n-1) l'
  in
  get
    (fun t -> (Var (Bruijn ("_",n)), lift 0 n t))
    (fun n -> get
		(fun (_,x) ->
		 match x with
		 | DefConst t -> (Var (Bruijn ("_",n)), lift 0 n t)
		 | DefLet (t1, t2, t3) -> (lift 0 n t2, lift 0 n t3)
		)
		(fun _ -> assert false)
		n
		sigma)
    n
    gamma
