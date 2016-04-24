open Utils
open Reduction

(* wellformed__ x returns true iff x's essence exists *)
let rec wellformed_family f ctx =
  match f with
  | BSFc (f1, f2) -> (wellformed_family f1 ctx) && (wellformed_family f2 ctx)
  | BSProd (id, f1, f2) -> (wellformed_family f1 ctx) && (wellformed_family f2 ctx)
  | BSLambda (id, f1, f2) -> (wellformed_family f1 ctx) && (wellformed_family f2 ctx)
  | BSApp (f1, d2) -> (wellformed_family f1 ctx) && (wellformed_delta d2 ctx)
  | BSAnd (f1, f2) -> (wellformed_family f1 ctx) && (wellformed_family f2 ctx)
  | BSOr (f1, f2) -> (wellformed_family f1 ctx) && (wellformed_family f2 ctx)
  | BSAtom id -> true
  | BSOmega -> true
  | BSAnything -> true
and wellformed_delta d ctx =
  let rec essence_eq d1 d2 = (* d1 and d2 are supposed to be well-formed *)
    match (d1, d2) with
    | (BDVar (id, false,_), BDVar (id', false, _)) -> if find_def id ctx then
							let (d, _) = get_def id ctx in essence_eq d d2
						      else if find_def id' ctx then
							let (d', _) = get_def id' ctx in essence_eq d1 d'
						      else id = id'
    | (BDVar (id, false,_), _) -> if find_def id ctx then
				    let (d, _) = get_def id ctx in essence_eq d d2
				  else false
    | (_, BDVar (id', false,_)) -> if find_def id' ctx then
				     let (d', _) = get_def id' ctx in essence_eq d1 d'
				   else false
    | (BDVar (_, true, n), BDVar (_, true, n')) -> n = n'
    | (BDStar, _) -> true
    | (_, BDStar) -> true
    | (BDLambda (id', f1', d2'), BDLambda (id'', f1'', d2'')) -> essence_eq d2' d2''
    | (BDApp (d1', d2'), BDApp (d1'', d2'')) -> (essence_eq d1' d1'') && (essence_eq d2' d2'')
    | (BDAnd (d1', d2'), _) -> essence_eq d1' d2
    | (_, BDAnd (d1', d2')) -> essence_eq d1 d1'
    | (BDProjL d', _) -> essence_eq d' d2
    | (_, BDProjL d') -> essence_eq d1 d'
    | (BDProjR d', _) -> essence_eq d' d2
    | (_, BDProjR d') -> essence_eq d1 d'
    | (BDOr (id1, f1, d1', id2, f2, d2', d3), _) -> essence_eq (delta_apply 0 d1' d3) d2
    | (_, BDOr (id1, f1, d1', id2, f2, d2', d3)) -> essence_eq d1 (delta_apply 0 d1' d3)
    | (BDInjL d', _) -> essence_eq d' d2
    | (_, BDInjL d') -> essence_eq d1 d'
    | (BDInjR d', _) -> essence_eq d' d2
    | (_, BDInjR d') -> essence_eq d1 d'
    | (_, _) -> false
  in
  match d with
  | BDVar (id, b, n) -> true
  | BDStar -> true
  | BDLambda (id, f1, d2) -> (wellformed_family f1 ctx) && (wellformed_delta d2 ctx)
  | BDApp (d1, d2) -> (wellformed_delta d1 ctx) && (wellformed_delta d2 ctx)
  | BDAnd (d1, d2) -> (wellformed_delta d1 ctx) && (wellformed_delta d2 ctx) && (essence_eq d1 d2)
  | BDProjL d' -> wellformed_delta d' ctx
  | BDProjR d' -> wellformed_delta d' ctx
  | BDOr (id1, f1, d1, id2, f2, d2, d3) ->
     (wellformed_delta d1 ctx) &&
       (wellformed_delta d2 ctx) &&
	 (wellformed_family f1 ctx) &&
	   (wellformed_family f2 ctx) &&
	     (wellformed_delta d3 ctx) &&
	       (essence_eq d1 d2)
  | BDInjL d' -> wellformed_delta d' ctx
  | BDInjR d' -> wellformed_delta d' ctx

let rec wellformed_kind k ctx =
  match k with
  | BType -> true
  | BKProd (id, f, k') -> (wellformed_family f ctx) && (wellformed_kind k' ctx)

let rec deltaequal d1 d2 ctx =
  match (d1, d2) with
  | (BDVar (id, false,n), BDVar (id', false, n')) -> id = id'
  | (BDVar (id, true,n), BDVar (id', true, n')) -> n = n'
  | (BDStar, BDStar) -> true
  | (BDLambda (id, f, d1'), BDLambda (id', f', d2')) -> unifiable f f' ctx && deltaequal d1' d2' ctx
  | (BDApp (d1', d1''), BDApp (d2', d2'')) -> deltaequal d1' d2' ctx && deltaequal d1'' d2'' ctx
  | (BDAnd (d1', d1''), BDAnd (d2', d2'')) -> deltaequal d1' d2' ctx && deltaequal d1'' d2'' ctx
  | (BDProjL d1', BDProjL d2') -> deltaequal d1' d2' ctx
  | (BDProjR d1', BDProjR d2') -> deltaequal d1' d2' ctx
  | (BDOr (id1', f1', d1', id1'', f1'', d1'', d1'''), BDOr (id2', f2', d2', id2'', f2'', d2'', d2''')) -> unifiable f1' f2' ctx && deltaequal d1' d2' ctx && unifiable f1'' f2'' ctx && deltaequal d1'' d2'' ctx && deltaequal d1''' d2''' ctx
  | (BDInjL d1', BDInjL d2') -> deltaequal d1' d2' ctx
  | (BDInjR d1', BDInjR d2') -> deltaequal d1' d2' ctx
  | (_,_) -> false
and unifiable f1 f2 ctx =
  match (f1, f2) with
  | (BSAnything, f) -> true
  | (f, BSAnything) -> true
  | (BSFc (a,b), BSFc(a',b')) -> unifiable a a' ctx && unifiable b b' ctx
  | (BSProd (id, a, b), BSFc(a',b')) -> unifiable a a' ctx && unifiable b b' ctx
  | (BSFc(a,b), BSProd (id, a', b')) -> unifiable a a' ctx && unifiable b b' ctx
  | (BSProd (id, a, b), BSProd (id', a', b')) -> unifiable a a' ctx && unifiable b b' ctx
  | (BSLambda (id, a, b), BSLambda (id', a', b')) -> unifiable a a' ctx && unifiable b b' ctx
  | (BSApp (a,b), BSApp (a',b')) -> unifiable a a' ctx && deltaequal (delta_compute b ctx) (delta_compute b' ctx) ctx
  | (BSAnd (a,b), BSAnd(a',b')) -> unifiable a a' ctx && unifiable b b' ctx
  | (BSOr (a,b), BSOr(a',b')) -> unifiable a a' ctx && unifiable b b' ctx
  | (BSAtom x, BSAtom y) -> if x = y then true else false
  | (_,_) -> false

(* we suppose unifiable f1 f2 ctx = true *)
let rec unify f1 f2 =
  match (f1, f2) with
  | (BSAnything, f) -> f
  | (f, BSAnything) -> f
  | (BSFc (a,b), BSFc(a',b')) -> BSFc (unify a a', unify b b')
  | (BSProd (id, a, b), BSFc(a',b')) -> BSFc (unify a a', unify b b')
  | (BSFc(a,b), BSProd (id, a', b')) -> BSFc (unify a a', unify b b')
  | (BSProd (id, a, b), BSProd (id', a', b')) -> BSProd (id, unify a a', unify b b')
  | (BSLambda (id, a, b), BSLambda (id', a', b')) -> BSLambda (id, unify a a', unify b b')
  | (BSApp (a,b), BSApp (a',b')) -> BSApp (unify a a', b)
  | (BSAnd (a,b), BSAnd(a',b')) -> BSAnd (unify a a', unify b b')
  | (BSOr (a,b), BSOr(a',b')) -> BSOr (unify a a', unify b b')
  | (BSAtom x, BSAtom y) -> if x = y then BSAtom x else failwith "the programmer should ensure this does not happen (use the unifiable function)"
  | (_,_) -> failwith "the programmer should ensure this does not happen (use the unifiable function)"

(* _check checks if _ is valid and returns an error message ("" if no error)
   _infer infers _'s family/kind
   __compute normalizes _ *)

(* we suppose f is typable (ie familycheck f gamma ctx = "") *)
let rec familyinfer f gamma ctx =
  match f with
  | BSFc (f1, f2) -> BType
  | BSProd (id, f1, f2) -> BType
  | BSLambda (id, f1, f2) -> BKProd(id, f1, familyinfer f2 ((id,f1) :: gamma) ctx)
  | BSApp (f1, d) ->
     (match (familyinfer f1 gamma ctx, deltainfer d gamma ctx) with
      | (BKProd (id, f1, k), f2) -> kind_apply 0 k d
      | (k,f2) -> failwith "error: use familycheck")
  | BSAnd (f1, f2) -> BType
  | BSOr (f1, f2) -> BType
  | BSAtom id -> get_type id ctx
  | BSOmega -> BType
  | BSAnything -> BType

(* we suppose d is typable (ie deltacheck d gamma ctx = "") *)
and deltainfer d gamma ctx =
  let rec isindependentfamily f n =
    match f with
    | BSFc (f1, f2) -> (isindependentfamily f1 n) && (isindependentfamily f2 n)
    | BSProd (id, f1, f2) -> (isindependentfamily f1 n) && (isindependentfamily f2 (n+1))
    | BSLambda (id, f1, f2) -> (isindependentfamily f1 n) && (isindependentfamily f2 (n+1))
    | BSApp (f1, d) -> (isindependentfamily f1 n) && (isindependentdelta d n)
    | BSAnd (f1, f2) -> (isindependentfamily f1 n) && (isindependentfamily f2 n)
    | BSOr (f1, f2) -> (isindependentfamily f1 n) && (isindependentfamily f2 n)
    | BSAtom id -> true
    | BSOmega -> true
    | BSAnything -> true
  and isindependentdelta d n =
    match d with
    | BDVar (x, b, n') -> if b then not (n = n') else true
    | BDStar -> true
    | BDLambda (x, f, d') -> isindependentfamily f n && isindependentdelta d' (n+1)
    | BDApp (d', d'') -> isindependentdelta d' n && isindependentdelta d'' n
    | BDAnd (d', d'') -> isindependentdelta d' n && isindependentdelta d'' n
    | BDProjL d' -> isindependentdelta d' n
    | BDProjR d' -> isindependentdelta d' n
    | BDOr (x', f', d', x'', f'', d'', d''') ->
       isindependentfamily f' n &&
	 isindependentdelta d' (n+1) &&
	   isindependentfamily f'' n &&
	     isindependentdelta d'' (n+1) &&
	       isindependentdelta d''' n
    | BDInjL d' -> isindependentdelta d' n
    | BDInjR d' -> isindependentdelta d' n
  in
  match d with
  | BDVar (x, b, n) -> if b then get x gamma else
			 if find_cst x ctx then get_cst x ctx else
			   if find_def x ctx then let (a, b) = get_def x ctx in b else
			     failwith "error: use deltacheck"
  | BDStar -> BSOmega
  | BDLambda (x, f, d') -> let f' = deltainfer d' ((x,f)::gamma) ctx in
			   if isindependentfamily f' 0 then
			     BSFc(f,f')
			   else BSProd(x, f, deltainfer d' ((x,f)::gamma) ctx)
  | BDApp (d', d'') ->
     (match deltainfer d' gamma ctx with
      | BSFc (f', f'') -> f''
      | BSProd (x, f', f'') -> family_apply 0 f'' d''
      | _ -> failwith "error: use deltacheck")
  | BDAnd (d', d'') -> BSAnd (deltainfer d' gamma ctx, deltainfer d'' gamma ctx)
  | BDProjL d' ->
     (match deltainfer d' gamma ctx with
      | BSAnd (f', _) -> f'
      | _ -> failwith "error: use deltacheck")
  | BDProjR d' ->
     (match deltainfer d' gamma ctx with
      | BSAnd (_, f') -> f'
      | _ -> failwith "error: use deltacheck")
  | BDOr (x', f', d', x'', f'', d'', d''') -> unify (deltainfer d' ((x',f') :: gamma) ctx) (deltainfer d'' ((x'',f'') :: gamma) ctx)
  | BDInjL d' -> BSOr(deltainfer d' gamma ctx, BSAnything)
  | BDInjR d' -> BSOr(BSAnything, deltainfer d' gamma ctx)

let rec gammacheck gamma ctx =
  match gamma with
  | [] -> ""
  | (x, f) :: gamma' -> let err = gammacheck gamma' ctx in
			if err = "" then
			  let err = familycheck f gamma' ctx in
			  if err = "" then
			    match familyinfer f gamma' ctx with
			    | BType -> ""
			    | k' -> "Error: " ^ (family_to_string (bruijn_to_family f)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k')) ^ " (should be Type).\n"
			  else
			    err
			else
			  err

and kindcheck k gamma ctx =
  match k with
  | BType -> gammacheck gamma ctx
  | BKProd (id, f, k') -> kindcheck k' ((id,f) :: gamma) ctx


and familycheck f gamma ctx =
  match f with
  | BSFc (f1, f2) -> let err = familycheck f2 (("",f1) :: gamma) ctx in (* independent product is a dependent product whose variable has an empty name *)
		     if err = "" then
		       match familyinfer f2 (("",f1) :: gamma) ctx with
		       | BType -> ""
		       | k -> "Error: " ^ (family_to_string (bruijn_to_family f2)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k)) ^ " (should be Type).\n"
		     else err
  | BSProd (id, f1, f2) -> let err = familycheck f2 ((id,f1) :: gamma) ctx in
			   if err = "" then
			     match familyinfer f2 ((id,f1) :: gamma) ctx with
			     | BType -> ""
			     | k -> "Error: " ^ (family_to_string (bruijn_to_family f2)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k)) ^ " (should be Type).\n"
			   else err
  | BSLambda (id, f1, f2) -> familycheck f2 ((id, f1) :: gamma) ctx
  | BSApp (f1, d) -> let err = familycheck f1 gamma ctx in
		     if err = "" then
		       let err = deltacheck d gamma ctx in
		       if err = "" then
			 let (k, f2) = (familyinfer f1 gamma ctx, deltainfer d gamma ctx) in
			 match k with
			 | BKProd (id, f1', k') -> if unifiable f1' f2 ctx then "" else "Error: type application " ^ (family_to_string (bruijn_to_family f1)) ^ " : " ^ (kind_to_string (bruijn_to_kind k)) ^ " cannot be applied to " ^ (delta_to_string (bruijn_to_delta d)) ^ " : " ^ (family_to_string (bruijn_to_family f2)) ^ ".\n"
			 | _ -> "Error: type application " ^ (family_to_string (bruijn_to_family f1)) ^ " : " ^ (kind_to_string (bruijn_to_kind k)) ^ " cannot be applied to " ^ (delta_to_string (bruijn_to_delta d)) ^ " : " ^ (family_to_string (bruijn_to_family f2)) ^ ".\n"
		       else err
		     else err
  | BSAnd (f1, f2) -> let err = familycheck f1 gamma ctx in
		      if err = "" then
			let err = familycheck f2 gamma ctx in
			if err = "" then
			  match familyinfer f1 gamma ctx with
			  | BType -> (match familyinfer f2 gamma ctx with
				      | BType -> ""
				      | k -> "Error: " ^ (family_to_string (bruijn_to_family f2)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k)) ^ " (should be Type).\n")
			  | k -> "Error: " ^ (family_to_string (bruijn_to_family f1)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k)) ^ " (should be Type).\n"
			else err
		      else err
  | BSOr (f1, f2) -> let err = familycheck f1 gamma ctx in
		     if err = "" then
		       let err = familycheck f2 gamma ctx in
		       if err = "" then
			 match familyinfer f1 gamma ctx with
			 | BType -> (match familyinfer f2 gamma ctx with
				     | BType -> ""
				     | k -> "Error: " ^ (family_to_string (bruijn_to_family f2)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k)) ^ " (should be Type).\n")
			 | k -> "Error: " ^ (family_to_string (bruijn_to_family f1)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k)) ^ " (should be Type).\n"
		       else err
		     else err
  | BSAtom id -> let err = gammacheck gamma ctx in
		 if err = "" then
		   if find_type id ctx then "" else "Error: the type " ^ id ^ " has not been declared yet.\n"
		 else err
  | BSOmega -> gammacheck gamma ctx
  | BSAnything -> gammacheck gamma ctx

and deltacheck d gamma ctx =
  match d with
  | BDVar (x,b,n) -> if b then gammacheck gamma ctx (* we are sure n is bound in gamma so we don't call find gamma x *)
		     else
		       if (find_cst x ctx) then "" else
			 if (find_def x ctx) then "" else
			   "Error: " ^ x ^ " has not been declared yet.\n"
  | BDStar -> gammacheck gamma ctx
  | BDLambda (x, f, d') -> deltacheck d' ((x,f)::gamma) ctx
  | BDApp (d', d'') ->
     let err = deltacheck d' gamma ctx in
     if err = "" then
       let err = deltacheck d'' gamma ctx in
       if err = "" then
	 let (f1, f2) = (deltainfer d'' gamma ctx, deltainfer d' gamma ctx) in
	 match f2 with
	 | BSFc (f', _) -> if unifiable f' f1 ctx then "" else "Error: cannot apply " ^ (delta_to_string (bruijn_to_delta d')) ^ " : " ^ (family_to_string (bruijn_to_family f2)) ^ " to " ^ (delta_to_string (bruijn_to_delta d'')) ^ " : " ^ (family_to_string (bruijn_to_family f1)) ^ ".\n"
	 | BSProd (_, f', _) -> if unifiable f' f1 ctx then "" else "Error: cannot apply " ^ (delta_to_string (bruijn_to_delta d')) ^ " : " ^ (family_to_string (bruijn_to_family f2)) ^ " to " ^ (delta_to_string (bruijn_to_delta d'')) ^ " : " ^ (family_to_string (bruijn_to_family f1)) ^ ".\n"
	 | _ -> "Error: cannot apply " ^ (delta_to_string (bruijn_to_delta d')) ^ " : " ^ (family_to_string (bruijn_to_family f2)) ^ " to " ^ (delta_to_string (bruijn_to_delta d'')) ^ " : " ^ (family_to_string (bruijn_to_family f1)) ^ ".\n"
       else err
     else err
  | BDAnd (d', d'') -> let err = deltacheck d' gamma ctx in
		       if err = "" then deltacheck d'' gamma ctx
		       else err
  | BDProjL d' -> let err = deltacheck d' gamma ctx in
		  if err = "" then
		    let f = deltainfer d' gamma ctx in
		    match f with
		    | BSAnd (_, _) -> ""
		    | _ -> "Error: " ^ (delta_to_string (bruijn_to_delta d')) ^ " has type " ^ (family_to_string (bruijn_to_family f)) ^ " (should be an intersection).\n"
		  else err
  | BDProjR d' -> let err = deltacheck d' gamma ctx in
		  if err = "" then
		    let f = deltainfer d' gamma ctx in
		    match f with
		    | BSAnd (_, _) -> ""
		    | _ -> "Error: " ^ (delta_to_string (bruijn_to_delta d')) ^ " has type " ^ (family_to_string (bruijn_to_family f)) ^ " (should be an intersection).\n"
		  else err
  | BDOr (x', f', d', x'', f'', d'', d''') ->
     let err = deltacheck d' ((x',f')::gamma) ctx in
     if err = "" then
       let err = deltacheck d'' ((x'',f'')::gamma) ctx in
       if err = "" then
	 let err = deltacheck d''' gamma ctx in
	 if err = "" then
	   let f1 = deltainfer d' ((x',f')::gamma) ctx in
	   let f2 = deltainfer d'' ((x'',f'')::gamma) ctx in
	   let f3 = deltainfer d''' gamma ctx in
	   if (unifiable f1 f2 ctx) && (unifiable (BSOr(f',f'')) f3 ctx) then "" else "Error: cannot type " ^ (delta_to_string (bruijn_to_delta d)) ^ ".\n"
	 else err
       else err
     else err
  | BDInjL d' -> deltacheck d' gamma ctx
  | BDInjR d' -> deltacheck d' gamma ctx

let typecstcheck id k ctx =
  if (find_all id ctx) then ("Error: " ^ id ^ " already exists.\n") else
    kindcheck k [] ctx

let cstcheck id f ctx =
  if (find_all id ctx) then ("Error: " ^ id ^ " already exists.\n") else
    let err =  familycheck f [] ctx in
    if err = "" then
      match familyinfer f [] ctx with
      | BType -> ""
      | k' -> "Error: " ^ (family_to_string (bruijn_to_family f)) ^ " has kind " ^ (kind_to_string (bruijn_to_kind k')) ^ " (should be Type).\n"
    else
      err
