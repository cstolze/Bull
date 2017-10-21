open Utils
open Bruijn

(* Transform (lambda x. t1) t2 into t1[t2/x] *)
let beta_redex t1 t2 =
  let aux k m =
    if m < k then Var m (* bound variable *)
    else if m = k then (* x *)
      lift 0 k t2
    else (* the enclosing lambda goes away *)
      Var (m-1)
  in map_term 0 aux t1

let is_eta t =
  let rec aux k t =
    match t with
    | Var n -> n != k
    | SPrLeft t1 | SPrRight t1 -> aux k t1
    | Prod (id1, t1, t2) | Abs (id1, t1, t2) | Subset (id1, t1, t2)
    | Let (id1, t1, t2) |
    Subabs (id1, t1, t2) -> aux k t1 && aux (k+1) t2
    | App (t1, t2) | Inter (t1, t2) | Union (t1, t2) | SPair (t1, t2)
    | Coercion (t1, t2) | SInLeft (t1, t2) | SMatch (t1, t2)
    | SInRight (t1, t2) -> aux k t1 && aux k t2
    | _ -> true
  in aux 0 t

(* Strong normalization *)
let rec strongly_normalize gamma t =
  let sn_children = visit_term (strongly_normalize gamma)
			       (fun _
				->
				strongly_normalize ((DefAxiom (Nothing, Nothing))
						       :: gamma))
			       (fun id _ -> id)
  in
  (* Normalize the children *)
  let t = sn_children t in
  match t with
  (* Beta-redex *)
  | App (Abs (_,_, t1), t2)
    -> strongly_normalize gamma (beta_redex t1 t2)
  | App (Subabs (_,_, t1), t2) -> strongly_normalize gamma (beta_redex t1 t2)
  | Let (_, t1, t2) -> strongly_normalize gamma (beta_redex t1 t2)
  (* Delta-redex *)
  | Var n -> let (t1, _, _, _) = get_from_context gamma n in
	     (match t1 with
	      | Var _ -> t1
	      | _ -> strongly_normalize gamma t1)
  (* Eta-redex *)
  | Abs (_,_, App (t1, Var 0)) -> if is_eta t1 then
			 strongly_normalize gamma (lift 0 (-1) t1)
		       else
			 t
  (* Pair-redex *)
  | SPrLeft (SPair (x,_)) -> x
  | SPrRight (SPair (_, x)) -> x
  (* inj-reduction *)
  | App (SMatch (_, x), SInLeft (_,y))
    -> strongly_normalize gamma (App (SPrLeft x, y))
  | App (SMatch (_, x), SInRight (_,y))
    -> strongly_normalize gamma (App (SPrRight x, y))
  | _ -> t


(* t =_\beta t' *)
let is_equal gamma t t' =
  let rec remove_id t = (* erase the identifiers *)
    visit_term remove_id (fun _ -> remove_id) (fun _ _ -> "") t
  in
  let t = remove_id t in
  let t' = remove_id t' in
  strongly_normalize gamma t = strongly_normalize gamma  t'
