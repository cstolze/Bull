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
  (* | Abs (t1, Var 0) -> eta_redex t1 NOT IMPLEMENTED *)
  (* Pair-redex *)
  | SPrLeft (SPair (x,_)) -> x
  | SPrRight (SPair (_, x)) -> x
  (* inj-reduction *)
  | SMatch (x, SInLeft (_,y))
    -> strongly_normalize gamma (App (SPrLeft x, y))
  | SMatch (x, SInRight (_,y))
    -> strongly_normalize gamma (App (SPrRight x, y))
  | _ -> t
