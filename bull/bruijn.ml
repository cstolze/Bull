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

(* Visitor iterator *)
(* goes recursively into most of the terms constructors *)
let visit_term f g h t =
  match t with
  | Let (id1, t1, t2) -> Let (h id1 t2, f t1, g (h id1 t2) t2)
  | Prod (id1, t1, t2) -> Prod (h id1 t2, f t1, g (h id1 t2) t2)
  | Abs (id1, t1, t2) -> Abs (h id1 t2, f t1, g (h id1 t2) t2)
  | Subset (id1, t1, t2) -> Subset (h id1 t2, f t1, g (h id1 t2) t2)
  | Subabs (id1, t1, t2) -> Subabs (h id1 t2, f t1, g (h id1 t2) t2)
  | App (t1, t2) -> App (f t1, f t2)
  | Inter (t1, t2) -> Inter (f t1, f t2)
  | Union (t1, t2) -> Union (f t1, f t2)
  | SPair (t1, t2) -> SPair (f t1, f t2)
  | SPrLeft t1 -> SPrLeft (f t1)
  | SPrRight t1 -> SPrRight (f t1)
  | SMatch (t1, t2) -> SMatch (f t1, f t2)
  | SInLeft (t1, t2) -> SInLeft (f t1, f t2)
  | SInRight (t1, t2) -> SInRight (f t1, f t2)
  | Coercion (t1, t2) -> Coercion (f t1, f t2)
  | _ -> t

(* Map iterator *)
(* f is a function that maps De Bruijn indexes to terms *)

let map_term k f t =
  let rec aux k t =
    match t with
    | Var n -> f k n
    | _ -> visit_term (aux k) (fun _ -> aux (k + 1)) (fun id _ -> id) t
  in aux k t

(* k is the index from which the context is changed *)
(* n is the shift *)
let lift k n =
  map_term k
	   (fun k m -> if m < k then Var m
		       else Var (m+n))

(* The indexes are broken during the parsing *)
(* Broken indexes have a negative value *)

let rec fix_index id_list t =
  let get_index id l =
  let rec aux k l =
    match l with
    | [] -> None
    | x :: l' -> if x = id then Some k else aux (k+1) l'
  in aux 0 l
  in
  match t with
  | Const id -> (match get_index id id_list with
		 | None -> t
		 | Some k -> Var k)
  | _ -> visit_term
	   (fix_index id_list)
	   (fun id -> fix_index (id :: id_list))
	   (fun id _ -> id)
	   t


(* is_const id t = true iff Const id appears in t *)
let is_const id t =
  let rec aux t =
    match t with
    | Const id1 -> id = id1
    | SPrLeft t1 | SPrRight t1 -> aux t1
    | Prod (id1, t1, t2) | Abs (id1, t1, t2) | Subset (id1, t1, t2)
    | Let (id1, t1, t2) |
    Subabs (id1, t1, t2) -> aux t1 || (if id1 = id then false
					    else aux t2)
    | App (t1, t2) | Inter (t1, t2) | Union (t1, t2) | SPair (t1, t2)
    | Coercion (t1, t2) | SInLeft (t1, t2) | SMatch (t1, t2)
    | SInRight (t1, t2) -> aux t1 || aux t2
    | _ -> false
  in aux t

(* find a fresh name for base_id (for alpha-conversion) *)
(* we suppose is_const base_id t = true *)
let new_ident base_id t =
  let rec aux k =
    let id = base_id ^ (string_of_int k) in
    if is_const id t then aux (k+1) else id
  in aux 0

(* replace Var by Const for pretty-printing *)
let fix_id id_list t =
  let rec get_id index id_list =
    match id_list with
    | [] -> assert false
    | x :: l' -> if index = 0 then x else get_id (index-1) l'
  in
  (* replace Var k by id *)
  let map_id id = map_term 0 (fun k n -> if k = n then Const id
					 else Var n)
  in
  (* replace the global variables *)
  let t = map_term 0 (fun k n -> if n < k then Var n
				 else Const (get_id (n-k) id_list)) t
  in
  (* replace the local variables *)
  let rec foo t =
    let new_id id t = if is_const id t then
			new_ident id t else id
    in
    let aux id t = foo (map_id id t)
    in visit_term foo aux new_id t
  in foo t

(* gives the term, term essence and type of the term of index n *)

let get_from_context gamma n =
    match List.nth gamma n with
    | DefAxiom (t1, t2) ->
       (Var n, lift 0 (n+1) t1
	, (match t1 (* or t2 *) with
	     Subset(_,_,_) -> Abs("x",Nothing,Var 0) (* essence of
    subset is Id *)
	   | _ -> Var n)
	, lift 0 (n+1) t2)
    | DefLet (d, t, e, et)
      -> (lift 0 (n+1) d, lift 0 (n+1) t, lift 0 (n+1) e
	  , lift 0 (n+1) et)
