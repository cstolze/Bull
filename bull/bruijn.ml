open Utils

(* TODO:
 WE DO NOT DEAL WITH META VARIABLES FOR NOW
 *)

(* Visitor iterator *)
(* goes recursively into most of the terms constructors *)
(* f : recursor
   g : incremented recursor
   h : id modifier (take the subterm where id is free as argument)
*)
let visit_term f g h = function
  | Let (l, id1, t1, t2, t3) -> Let (l, h id1 t3, f t1, f t2, g (h id1 t3) t3)
  | Prod (l, id1, t1, t2) -> Prod (l, h id1 t2, f t1, g (h id1 t2) t2)
  | Abs (l, id1, t1, t2) -> Abs (l, h id1 t2, f t1, g (h id1 t2) t2)
  | App (l, t1, l2) -> App (l, f t1, List.map f l2)
  | Inter (l, t1, t2) -> Inter (l, f t1, f t2)
  | Union (l, t1, t2) -> Union (l, f t1, f t2)
  | SPair (l, t1, t2) -> SPair (l, f t1, f t2)
  | SPrLeft (l, t1) -> SPrLeft (l, f t1)
  | SPrRight (l, t1) -> SPrRight (l, f t1)
  | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6) ->
     SMatch (l, f t1, f t2,
             h id1 t4, f t3, g (h id1 t4) t4,
             h id2 t6, f t5, g (h id1 t6) t6)
  | SInLeft (l, t1, t2) -> SInLeft (l, f t1, f t2)
  | SInRight (l, t1, t2) -> SInRight (l, f t1, f t2)
  | Coercion (l, t1, t2) -> Coercion (l, f t1, f t2)
  | Meta (l, n, subst) -> Meta (l, n, List.map f subst)
  | t -> t (* non-recursive cases *)

(* Map iterator *)
(* f is a function that maps De Bruijn indexes to terms *)
(* k states how deep we are in the term *)

let map_term k f t =
  let rec aux k t =
    match t with
    | Var (l, n) -> f k l n
    | _ -> visit_term (aux k) (fun _ -> aux (k + 1)) (fun id _ -> id) t
  in aux k t

let rec map_context k f env =
  match env with
  | [] -> []
  | DefAxiom (id,t) :: env ->
     DefAxiom(id, map_term (k-1) f t) :: map_context (k-1) f env
  | DefLet (id,t1,t2) :: env ->
     DefLet(id, map_term (k-1) f t1, map_term (k-1) f t2)
     :: map_context (k-1) f env

(* k is the index from which the context is changed *)
(* n is the shift *)
let lift k n =
  map_term k
	   (fun k l m -> if m < k then Var (l, m)
		       else Var (l, m+n))

(* Change string constants to de bruijn indexes *)

let rec fix_index id_list t =
  let get_index id l =
    let rec aux k l =
      match l with
      | [] -> None
      | x :: l' -> if x = id then Some k else aux (k+1) l'
    in aux 0 l
  in
  match t with
  | Const (l,id) -> (match get_index id id_list with
		     | None -> t
		     | Some k -> Var (l,k))
  | _ -> visit_term
	   (fix_index id_list)
	   (fun id -> fix_index (id :: id_list))
	   (fun id _ -> id)
	   t

(* is_const id t = true iff Const id appears in t *)
let is_const id t =
  let rec aux t =
    match t with
    | Const (l, id1) -> id = id1
    | SPrLeft (l, t1) | SPrRight (l, t1) -> aux t1
    | Let (l, id1, t1, t2, t3) -> aux t1 || aux t2 ||
                                    (if id1 = id then false
                                     else aux t3)
    | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6) ->
       aux t1 || aux t2 || aux t3 || aux t5 ||
         (if id1 = id then false else aux t4) ||
           (if id2 = id then false else aux t6)
    | Prod (l, id1, t1, t2) | Abs (l, id1, t1, t2)
      -> aux t1 || (if id1 = id then false
		    else aux t2)
    | App (l, t1, l2) -> aux t1 || List.exists aux l2
    | Inter (l, t1, t2) | Union (l, t1, t2) | SPair (l, t1, t2)
    | Coercion (l, t1, t2) | SInLeft (l, t1, t2)
    | SInRight (l, t1, t2) -> aux t1 || aux t2
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
  let map_id id = map_term 0 (fun k l n -> if k = n then Const (l,id)
					 else Var (l,n))
  in
  (* replace the global variables *)
  let t = map_term 0 (fun k l n -> if n < k then Var (l, n)
				 else Const (l, get_id (n-k) id_list)) t
  in
  (* replace the local variables *)
  let rec foo t =
    let new_id id t = if is_const id t then
			new_ident id t else id
    in
    let aux id t = foo (map_id id t)
    in visit_term foo aux new_id t
  in foo t

