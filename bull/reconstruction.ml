open Utils
open Bruijn
open Reduction
open Subtyping
open Printer

(* returns the essence and the type of a term *)

let type_of_sort s =
  match s with
  | Type -> Result.Ok (Sort Kind, Sort Type, Sort Kind)
  | Kind -> Result.Error (error_kind)

(* returns the sort of Pi x : A. B, where A:s1 and b:s2 *)
let principal_type_system s1 s2 =
  match (s1, s2) with
  | (Type, Type) -> Some Type (* terms depending on terms *)
  | (Type, Kind) -> Some Kind (* types depending on terms *)
  | _ -> None (* we are doing lambdaP (aka LF) for now *)

(* tells if x of type (Sort s) is a set, ie if "x inter x" is legal *)
let is_set s =
  true

exception Error of string

let rec reconstruct str id_list sigma gamma l t =
  match t with
  | Sort s -> 
  | Let (s,t1,t2) -> 
  | Prod (s,t1,t2) -> 
  | Abs (s,t1,t2) -> 
  | App (t1,t2) -> 
  | Inter (t1,t2) -> 
  | Union (t1,t2) -> 
  | SPair (t1,t2) -> 
  | SPrLeft of term
  | SPrRight of term
  | SMatch (t1,t2) -> 
  | SInLeft (t1,t2) -> 
  | SInRight (t1,t2) -> 
  | Coercion (t1,t2) -> 
  | Var n -> 
  | Const s -> Result.Error(error_const getloc str id)
  | Nothing -> assert false
  | Meta n -> 
  | _ -> Error "illegal term"

and rec check str id_list sigma gamma l t1 t2 =
(*  match t1 with
  | Sort s -> 
  | Let (s,t1,t2) -> 
  | Prod (s,t1,t2) -> 
  | Abs (s,t1,t2) -> 
  | App (t1,t2) -> 
  | Inter (t1,t2) -> 
  | Union (t1,t2) -> 
  | SPair (t1,t2) -> 
  | SPrLeft of term
  | SPrRight of term
  | SMatch (t1,t2) -> 
  | SInLeft (t1,t2) -> 
  | SInRight (t1,t2) -> 
  | Coercion (t1,t2) -> 
  | Var n -> 
  | Const s -> Result.Error(error_const getloc str id)
  | Nothing -> assert false
  | Meta n -> 
  | _ -> Error "illegal term" *)


(* **************************************************************************************************** *)
(* ******************************************** TO REMOVE ********************************************* *)
(* **************************************************************************************************** *)

let rec reconstruction str id_list gamma l t =
  let r0 = reconstruction str in
  let getloc = (* get location *)
    let Locnode (a,b,_) = l in (a,b)
  in
  let get n = (* get loc for the nth child *)
    let Locnode (_,_,l') = l in
    try List.nth l' n
    with _ -> l (* in case we're dealing with a let-variable (it is a hack, we should be able to recurse while staying on the same locnode level)*)
  in
  let r nl1 t1 = (* recursive call *)
    Result.bind (r0 id_list gamma (get nl1) t1)
  in
  let r2 t1 t2 f = (* recursively type the two children *)
    r 0 t1 (fun x -> r 1 t2 (f x))
  in
  let check_abs x nl1 t1 nl2 t2 f = (* check that x:t1 can be put in gamma, then type gamma,x:t1 |- t2 *)
    r nl1 t1 (fun (s1,e1,_) ->
	      match s1 with
	      | Sort s -> Result.bind (r0 (x::id_list) (DefAxiom(t1,e1)::gamma) (get nl2) t2) (f s e1) (* note the signature of f *)
	      | _ -> Result.Error (error_abs id_list (get 0) str s1) )
  in
  let type_prod x s1 t2 = (* s1 is the sort of A in 'forall x:A, t2' *)
    match t2 with
    | Sort s2 ->
       (match principal_type_system s1 s2 with
	| Some s -> Result.Ok s
	| None -> Result.Error (error_pts getloc str))
    | _ -> Result.Error (error_type_prod (x::id_list) getloc str t2)
  in
  let type_app t (t1,e1,et1) (t2,e2,et2) =
    match (t1,et1) with
    | (Prod(_,_,t3), Prod (_,et2',et3)) -> if is_equal gamma et2 et2' then Result.Ok (beta_redex t3 t, App(e1,e2), beta_redex et3 e2)
					      else
					     Result.Error (error_match id_list getloc str et2' et2)
    | (Subset(_,_,t3), Subset(_,et2',et3)) -> if is_equal gamma et2 et2' then Result.Ok (beta_redex t3 t, e2, beta_redex et3 e2) else Result.Error (error_match id_list getloc str et2' et2)
    | _ -> Result.Error (error_no_prod id_list (get 0) str t1)
  in
  let type_sproj b t1 = (* b = true -> proj_left *)
     r 0 t1
       (fun (t1,e1,et1) ->
	match (t1,et1) with
	| (Inter(l,r),Inter(el,er)) -> Result.Ok((if b then l else r),e1,if b then el else er)
	| _ -> Result.Error (error_sproj id_list (get 0) str t1))
  in
  let type_set s1 s2 e = (* look if s1 = s2 and if we are dealing with sets *)
    if s1 = s2 then
      match s1 with
      | Sort s -> if is_set s then Result.Ok (Sort s,e,Sort s) else Result.Error (error_set getloc str)
      | _ -> Result.Error (error_set getloc str)
    else Result.Error (error_set getloc str)
  in
  let type_union_inter b t1 t2 = (* b = true -> inter *)
    r2 t1 t2 (fun (s1,e1,_) (s2,e2,_) ->
	      type_set s1 s2 (if b then Inter(e1,e2) else Union(e1,e2)))
  in
  let type_inj b t1 t2 = (* b = true -> inj_left *)
    let l' = let l = get 0 in let Locnode (a,b,_) = l in Locnode(a,b,[l;l]) (* fix the location for the recursive call *)
    in
    r 1 t2 (fun (t,e,_) ->
	    let res = if b then Union (t,t1) else Union (t1,t)
	    in
	    Result.bind (r0 id_list gamma l' res) (fun (_,et,_) -> Result.Ok (res,e,et)))
  in
  match t with
  | Sort s -> type_of_sort s
  | Let (id,t1,t2) ->
     r 0 t1
       (fun (t1',e1',et1')
	-> r0 (id::id_list) (DefLet(t1,t1',e1',et1') :: gamma) (get 1) t2)
  | Prod (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,_)
					       ->
					       Result.bind (type_prod id s1 t2) (fun s -> Result.Ok (Sort s,Prod(id,e1,e2),Sort s)))
  | Abs (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,et2) ->
 					      (* hack to see if Prod(id,t1,t2) is well-defined *)
						 Result.bind (r0 id_list gamma l (Prod(id,t1,t2)))
							     (fun (_,et,_) -> Result.Ok (Prod(id,t1,t2), Abs(id,Nothing,e2),Prod(id,e1,et2))))
  | Subset (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,_) -> type_set (Sort s1) t2 (Subset(id,e1,e2)))
  | Subabs (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,et2) ->
						 if is_equal (DefAxiom(Nothing,Nothing)::gamma) e2 (Var 0) then
						   (* hack to see if Subset(id,t1,t2) is well-defined *)
						   Result.bind (r0 id_list gamma l (Subset(id,t1,t2)))
							       (fun (_,et,_) -> Result.Ok (Subset(id,t1,t2), Abs(id,Nothing,(*e2*)Var 0),Subset(id,e1,et2)))
						 else Result.Error (error_essence getloc str))
  | App (t1, t2) -> r2 t1 t2 (type_app t2)
  | Inter (t1, t2) -> type_union_inter true t1 t2
  | Union (t1, t2) -> type_union_inter false t1 t2
  | SPair (t1, t2) -> r2 t1 t2
			 (fun (t1,e1,et1) (t2,e2,et2) ->
			  if is_equal gamma e1 e2 then
			    r2 t1 t2 (fun (s1,_,_) (s2,_,_) ->
				      match (s1,s2) with
				      | (Sort s1, Sort s2) -> if (s1 == s2) then if is_set s1 then Result.Ok (Inter (t1, t2), e1, Inter(et1,et2)) else Result.Error (error_set getloc str) else Result.Error (error_set getloc str)
				      | _ -> assert false)
			  else Result.Error (error_essence getloc str))
  | SPrLeft t1 -> type_sproj true t1
  | SPrRight t1 -> type_sproj false t1
  | SMatch (t1, t2) -> r2 t1 t2 (fun (t1',e1',et1') (t2',e2',et2') ->
				 match (e1',et2') with
				 | (Prod(_,Union(a,b),f),
				    Inter(Prod(_,a',fa),Prod(_,b',fb)))->
				    if is_equal (DefAxiom(Nothing,Nothing)::gamma) fa fb then
				      if is_equal (DefAxiom(Nothing,Nothing)::gamma) f fa && is_equal gamma a a' && is_equal gamma b b' then
					Result.Ok (t1, e2', e1')
				      else Result.Error (error_return (get 0) str)
				    else Result.Error (error_with (get 1) str)
				 | _ -> Result.Error (error_smatch getloc str))
  | SInLeft (t1, t2) -> type_inj true t1 t2
  | SInRight (t1, t2) -> type_inj false t1 t2
  | Coercion (t1, t2) -> r2 t1 t2 (fun (t1',e1',_) (t2',e2',et2') ->
    match t1' with
    | Sort s1 ->
       Result.bind (r0 id_list gamma l t2')
         (fun (t,_,_) -> match t with
                         | Sort s2 -> if s1 == s2 then
                                        if is_subtype gamma et2' e1' then Result.Ok(t1,e2',e1')
                                        else
                                          Result.Error(error_subtype
                                                         l str id_list
                                                         t1 t2')
                                      else
                                        Result.Error (error_set getloc str)
                         | _ -> Result.Error(error_coe2 (get 1) str))
    | _ -> Result.Error(error_coe1 (get 0) str id_list t1'))
  | Var n -> let (_,t,e,et) = get_from_context gamma n in Result.Ok(t,e,et)
  | Const id -> Result.Error(error_const getloc str id)
  | Omega -> Result.Ok(Sort Type, Omega, Sort Type)
  | Nothing -> assert false
  | Meta n -> Result.Error("No meta variables for now.\n")

let check_axiom str id_list gamma l t =
  Result.bind (reconstruction str id_list gamma l t)
	      (fun (s,et,_) -> match s with
			       | Sort s -> Result.Ok (et)
			       | _ -> Result.Error error_axiom)
