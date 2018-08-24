open Utils
open Bruijn

(* Transform (lambda x. t1) t2 into t1[t2/x] *)
let beta_redex t1 t2 =
  let aux k l m =
    if m < k then Var (l, m) (* bound variable *)
    else if m = k then (* x *)
      lift 0 k t2
    else (* the enclosing lambda goes away *)
      Var (l, m-1)
  in map_term 0 aux t1

let is_eta t =
  let rec aux k t =
    match t with
    | Var (l, n) -> n != k
    | SPrLeft (l, t1) | SPrRight (l, t1) -> aux k t1
    | Let (l, id1, t1, t2, t3) ->
       aux k t1 && aux k t2 && aux (k+1) t3
    | Prod (l, id1, t1, t2) | Abs (l, id1, t1, t2)
     -> aux k t1 && aux (k+1) t2
    | App (l, t1, t2) | Inter (l, t1, t2) | Union (l, t1, t2) | SPair (l, t1, t2)
    | Coercion (l, t1, t2) | SInLeft (l, t1, t2)
    | SInRight (l, t1, t2) -> aux k t1 && aux k t2
    | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6) ->
       aux k t1 && aux k t2 && aux k t3 && aux (k+1) t4 && aux k t5 && aux (k+1) t6
    | _ -> true
  in aux 0 t

(* Strong normalization *)
let rec strongly_normalize gamma t =
  let sn_children = visit_term (strongly_normalize gamma)
			       (fun _
				->
				 strongly_normalize ((DefAxiom ("",dummy_term))
						     :: gamma))
			       (fun id _ -> id)
  in
  (* Normalize the children *)
  let t = sn_children t in
  match t with
  (* Beta-redex *)
  | App (l, Abs (l',_,_, t1), t2)
    -> strongly_normalize gamma (beta_redex t1 t2)
  | Let (l, _, t1, t2, t3) -> strongly_normalize gamma (beta_redex t2 t1)
  (* Delta-redex *)
  | Var (l, n) -> let (t1, _) = get_from_context gamma n in
	     (match t1.delta with
	      | Var _ -> t1.delta
	      | _ -> strongly_normalize gamma t1.delta)
  (* Eta-redex *)
  | Abs (l,_, _, App (l',t1, Var (_,0))) -> if is_eta t1 then
			               strongly_normalize gamma (lift 0 (-1) t1)
		                     else
			               t
  (* Pair-redex *)
  | SPrLeft (l, SPair (l', x,_)) -> x
  | SPrRight (l, SPair (l', _, x)) -> x
  (* inj-reduction *)
  | SMatch (l, SInLeft(l',_,t1), _, id1, _, t2, id2, _, _) ->
     strongly_normalize gamma (beta_redex t2 t1)
  | SMatch (l, SInRight(l',_,t1), _, id1, _, _, id2, _, t2) ->
     strongly_normalize gamma (beta_redex t2 t1)
  | _ -> t
