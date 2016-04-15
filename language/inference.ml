open Utils

let rec wellformed_family f =
  match f with
  | BSFc (f1, f2) -> (wellformed_family f1) && (wellformed_family f2)
  | BSProd (id, f1, f2) -> (wellformed_family f1) && (wellformed_family f2)
  | BSLambda (id, f1, f2) -> (wellformed_family f1) && (wellformed_family f2)
  | BSApp (f1, d2) -> (wellformed_family f1) && (wellformed_delta d2)
  | BSAnd (f1, f2) -> (wellformed_family f1) && (wellformed_family f2)
  | BSOr (f1, f2) -> (wellformed_family f1) && (wellformed_family f2)
  | BSAtom id -> true
  | BSOmega -> true
  | BSAnything -> true
and wellformed_delta d =
  let rec essence_eq d1 d2 = (* d1 and d2 are supposed to be well-formed *)
    match (d1, d2) with
    | (BDVar (id, b, n), BDVar (id', b', n')) -> b = b' && (if b = true then n = n' else id = id')
    | (BDStar, _) -> true
    | (_, BDStar) -> true
    | (BDLambda (id', f1', d2'), BDLambda (id'', f1'', d2'')) -> essence_eq d2' d2''
    | (BDApp (d1', d2'), BDApp (d1'', d2'')) -> (essence_eq d1' d1'') && (essence_eq d2' d2'')
    | (BDAnd (d1', d2'), _) -> essence_eq d1' d2
    | (_, BDAnd (d1', d2') -> essence_eq d1 d1'
    | (BDProjL d', _) -> essence_eq d' d2
    | (_, BDProjL d') -> essence_eq d1 d'
    | (BDProjR d', _) -> essence_eq d' d2
    | (_, BDProjR d') -> essence_eq d1 d'
    | (BDOr (id1, f1, d1', id2, f2, d2', d3), _) ->
    | (_, BDOr (id1, f1, d1', id2, f2, d2', d3)) ->
    | (BDInjL d', _) -> essence_eq d' d2
    | (_, BDInjL d') -> essence_eq d1 d'
    | (BDInjR d', _) -> essence_eq d' d2
    | (_, BDInjR d') -> essence_eq d1 d'
    | (_, _) -> false
  in
  match d with
  | BDVar (id, b, n) -> true
  | BDStar -> true
  | BDLambda (id, f1, d2) -> (wellformed_family f1) && (wellformed_delta d2)
  | BDApp (d1, d2) -> (wellformed_delta d1) && (wellformed_delta d2)
  | BDAnd (d1, d2) -> (wellformed_delta d1) && (wellformed_delta d2) && (essence_eq d1 d2)
  | BDProjL d' -> wellformed_delta d'
  | BDProjR d' -> wellformed_delta d'
  | BDOr (id1, f1, d1, id2, f2, d2, d3) ->
     (wellformed_delta d1) &&
       (wellformed_delta d2) &&
	 (wellformed_family f1) &&
	   (wellformed_family f2) &&
	     (wellformed_delta d3) &&
	       (essence_eq d1 d2)
  | BDInjL d' -> wellformed_delta d'
  | BDInjR d' -> wellformed_delta d'

let rec wellformed_kind k =
  match k with
  | BType -> true
  | BKProd (id, f, k) ->

let rec is_wellformed d =
  let apply b b' =
    let rec replace b b' n =
      match b with
      | BVar (y, false, _) -> b
      | BVar (_, true, n') -> if n = n' then b' else b
      | BLambda b1 -> replace b b' (n+1)
      | BApp (b1, b2) -> BApp (replace b1 b' n, replace b2 b' n)
    in
    match b with
    | BLambda b1 -> replace b1 b' 0
    | _ -> b' (* SHOULD NOT HAPPEN *)
  in
  let rec to_bruijn d = (* convert d to a lambda-term with De Bruijn indexes, here d is supposed well-formed *)
    let rec update b x n = (* bind x in b *)
      match b with
      | BVar (y,false,_) -> if (y = x) then BVar(y, true, n) else b
      | BVar (_,true,_) -> b
      | BLambda b' -> BLambda (update b' x (n+1))
      | BApp (b', b'') -> BApp (update b' x n, update b'' x n)
    in
    match d with
    | DVar x -> BVar(x, false, 0)
    | DStar -> BVar("*", false, 0)
    | DLambda (x, _, d') -> BLambda (update (to_bruijn d') x 0)
    | DApp (d', d'') -> BApp (to_bruijn d', to_bruijn d'')
    | DAnd (d', _) -> to_bruijn d'
    | DProjL d' -> to_bruijn d'
    | DProjR d' -> to_bruijn d'
    | DOr (x, f, d', _, _, _, d'') -> apply (to_bruijn (DLambda (x, f, d'))) (to_bruijn d'')
    | DInjL d' -> to_bruijn d'
    | DInjR d' -> to_bruijn d'
  in
  let rec equal_bruijn b1 b2 =
    match (b1, b2) with
    | BVar (x, false,_), BVar(y, false, _) -> x = y (* free variables *)
    | BVar (_, true, n), BVar(_, true, n') -> n = n' (* bound variables *)
    | BLambda b1', BLambda b2' -> equal_bruijn b1' b2'
    | BApp (b1', b1''), BApp (b2', b2'') -> equal_bruijn b1' b2' && equal_bruijn b1'' b2''
    | BVar("*", false, 0), _ -> true (* star case *)
    | _, BVar("*", false, 0) -> true (* star case *)
    | _, _ -> false
  in
  match d with
  | DVar x -> true
  | DStar -> true
  | DLambda (x,f,d') -> is_wellformed d'
  | DApp (d', d'') -> (is_wellformed d') && (is_wellformed d'')
  | DAnd (d',d'') -> (is_wellformed d') && (is_wellformed d'') && (equal_bruijn (to_bruijn d') (to_bruijn d''))
  | DProjL d' -> is_wellformed d'
  | DProjR d' -> is_wellformed d'
  | DOr (x', f', d', x'', f'', d'', d''') -> (is_wellformed d') && (is_wellformed d'') && (is_wellformed d''') && (equal_bruijn (to_bruijn (DLambda (x',f',d'))) (to_bruijn (DLambda (x'',f'',d''))))
  | DInjL d' -> is_wellformed d'
  | DInjR d' -> is_wellformed d'

let rec unifiable f1 f2 =
  match (f1, f2) with
  | (SAnything, f) -> true
  | (f, SAnything) -> true
  | (SFc (a,b), SFc(a',b')) -> unifiable a a' && unifiable b b'
  | (SProd (id, a, b), SProd (id', a', b')) -> unifiable a a' && 
  | (SAnd (a,b), SAnd(a',b')) -> unifiable a a' && unifiable b b'
  | (SOr (a,b), SOr(a',b')) -> unifiable a a' && unifiable b b'
  | (SAtom x, SAtom y) -> if x = y then true else false
  | (_,_) -> false

let rec unify f1 f2 =
  match (f1, f2) with
  | (SAnything, f) -> f
  | (f, SAnything) -> f
  | (SFc (a,b), SFc(a',b')) -> SFc(unify a a', unify b b')
  | (SAnd (a,b), SAnd(a',b')) -> SAnd(unify a a', unify b b')
  | (SOr (a,b), SOr(a',b')) -> SOr(unify a a', unify b b')
  | (SAtom x, SAtom y) -> if x = y then SAtom x else failwith "the programmer should ensure this does not happen (use the unifiable function)"
  | (_,_) -> failwith "the programmer should ensure this does not happen (use the unifiable function)"

(* _check checks if _ is valid and returns an error message ("" if no error)
   _infer infers _'s family/kind
   _norm normalizes _ *)

let rec deltainfer d gamma ctx =
    match d with
    | DVar x -> if find x gamma then familysimpl (get x gamma) else (* local variables shadow global ones *)
		  (if find_cst x ctx then familysimpl (get_cst x ctx) else
		     (if find_def x ctx then let (_, f) = familysimpl (get_def x ctx) in f else
			failwith "should not happen (use deltacheck)"))
    | DStar -> SOmega
    | DLambda (x, f, d') -> SProd (x, familysimpl f, deltainfer d' ((x,f)::gamma) ctx)
    | DApp (d', d'') ->
       let f1 = deltainfer d'' gamma ctx in
       (match deltainfer d' gamma ctx with
	| SProd (x, f', f2) -> if unifiable f' f1 then familysimpl (familyreplace d'' x f2) else failwith "should not happen (use deltacheck)"
	| SFc (f', f2) if unifiable f' f1 then f2
	| _ -> failwith "should not happen (use deltacheck)")
    | DAnd (d', d'') -> SAnd (deltainfer d' gamma ctx, deltainfer d'' gamma ctx)
    | DProjL d' -> (match (deltainfer d' gamma ctx) with
		   | SAnd (f1, f2) -> f1
		   | _ -> failwith "should not happen (use deltacheck)")
    | DProjR d' -> (match (deltainfer d' gamma ctx) with
		   | SAnd (f1, f2) -> f2
		   | _ -> failwith "should not happen (use deltacheck)")
    | DOr (x', f', d', x'', f'', d'', d''') ->
       let f1 = deltainfer d' ((x',f')::gamma) ctx in
       let f2 = deltainfer d'' ((x'',f'')::gamma) ctx in
       let f3 = deltainfer d''' gamma ctx in
       if (unifiable_or f1 f2 x' x'') && (unifiable (SOr(f',f'')) f3) then
	 familysimpl (unify_or f1 f2 x' x'' d'')
       else
	 failwith "should not happen (use deltacheck)"
    | DInjL d' -> SOr(deltainfer d' gamma ctx, SAnything)
    | DInjR d' -> SOr(SAnything, deltainfer d' gamma ctx)

let rec familyinfer f gamma ctx =
  match f with
  | SFc (f1, f2) -> Type
  | SProd (id, f1, f2) -> Type
  | SLambda (id, f1, f2) -> KProd (id, familynorm f1, familyinfer f2 ((id, f1) :: gamma) ctx)
  | SApp (f1, d) -> (match (familyinfer f1 gamma ctx, deltainfer d gamma ctx) with
		    | (KProd (id, f1, k), f2) -> kindnorm (kindreplace f2 id k)
		    | _ -> failwith "should not happen (use familycheck)")
  | SAnd (f1, f2) -> Type
  | SOr (f1, f2) -> Type
  | SOmega -> Type
  | SAnything -> Type

let rec gammacheck gamma ctx =
  match gamma with
  | [] -> ""
  | (x, f) :: gamma' -> let err = gammacheck gamma' ctx in
			if err = "" then
			  let err = typecheck f gamma' ctx in
			  if err = "" then
			    match typeinfer f gamma' ctx with
			    | Type -> ""
			    | k' -> "Error: " ^ (family_to_string f) ^ " has kind " ^ (kind_to_string k') ^ " (should be Type).\n"
			  else
			    err
			else
			  err
  and

let rec kindcheck k gamma ctx =
  match k with
  | Type -> gammacheck gamma ctx
  | Prod (id, f, k') -> kindcheck ((id,f) :: gamma) k'
  and

let rec familycheck f gamma ctx =
  match f with
  | SFc (f1, f2) -> let err = familycheck f2 (("",f1) :: gamma) ctx in (* independent product is a dependent product whose variable has an empty name *)
		    if err = "" then
		      match familyinfer f2 (("",f1) :: gamma) ctx with
		      | Type -> ""
		      | k -> "Error: " ^ (family_to_string f2) ^ " has kind " ^ (kind_to_string k) ^ " (should be Type).\n"
		    else err
  | SProd (id, f1, f2) -> let err = familycheck f2 ((id,f1) :: gamma) ctx in
		    if err = "" then
		      match familyinfer f2 ((id,f1) :: gamma) ctx with
		      | Type -> ""
		      | k -> "Error: " ^ (family_to_string f2) ^ " has kind " ^ (kind_to_string k) ^ " (should be Type).\n"
		    else err
  | SLambda (id, f1, f2) -> familycheck f2 ((id, f1) :: gamma) ctx
  | SApp (f1, d) -> let err = familycheck f1 gamma ctx in
		    if err = "" then
		      let err = deltacheck d gamma ctx in
		      if err = "" then
			match (familyinfer f1 gamma ctx, deltainfer d gamma ctx) with
			| (KProd (id, f1, k), f2) -> if f1 = f2 then "" else "Error: type application " ^ (family_to_string f1) ^ " : " ^ (kind_to_string k) ^ " cannot be applied to " ^ (delta_to_string d) ^ " : " ^ (delta_to_string f2) ^ ".\n"
			| (k,f2) -> "Error: type application " ^ (family_to_string f1) ^ " : " ^ (kind_to_string k) ^ " cannot be applied to " ^ (delta_to_string d) ^ " : " ^ (delta_to_string f2) ^ ".\n"
		      else err
		    else err
  | SAnd (f1, f2) -> let err = familycheck f1 gamma id in
		     if err = "" then
		       let err = familycheck f2 gamma id in
		       if err = "" then
			 match familyinfer f1 gamma id with
			 | Type -> (match familyinfer f2 gamma id with
				    | Type -> ""
				    | k -> "Error: " ^ (family_to_string f2) ^ " has kind " ^ (kind_to_string k) ^ " (should be Type).\n")
			 | k -> "Error: " ^ (family_to_string f1) ^ " has kind " ^ (kind_to_string k) ^ " (should be Type).\n"
		       else err
		     else err
  | SOr (f1, f2) -> let err = familycheck f1 gamma id in
		     if err = "" then
		       let err = familycheck f2 gamma id in
		       if err = "" then
			 match familyinfer f1 gamma id with
			 | Type -> (match familyinfer f2 gamma id with
				    | Type -> ""
				    | k -> "Error: " ^ (family_to_string f2) ^ " has kind " ^ (kind_to_string k) ^ " (should be Type).\n")
			 | k -> "Error: " ^ (family_to_string f1) ^ " has kind " ^ (kind_to_string k) ^ " (should be Type).\n"
  | SAtom id -> let err = gammacheck gamma ctx in
		if err = "" then
		  if find_type id ctx then "" else "Error: the type " ^ id ^ " has not been declared yet.\n"
		else err
  | SOmega -> gammacheck gamma ctx
  | SAnything -> gammacheck gamma ctx
  and

let deltacheck d gamma ctx =
  | DVar x -> let err = gammacheck gamma ctx in
	      if err = "" then
		if find x gamma then "" else
		(if find_cst x ctx then "" else
		   if find_def x ctx then "" else
		     "Error: " ^ x ^ " has not been declared.\n")
	      else err
  | DStar -> gammacheck gamma ctx
  | DLambda (x, f, d') -> deltacheck d' ((x,f)::gamma) ctx
  | DApp (d', d'') ->
     let err = deltacheck d' gamma ctx in
     if err = "" then
       let err = deltacheck d'' gamma ctx in
       if err = "" then
	 let (f1, f2) = (deltainfer d'' gamma ctx, deltainfer d' gamma ctx) in
	 match f2 with
	 | SFc (f', _) -> if unifiable f' f1 then "" else "Error: cannot apply " (delta_to_string d') ^ " : " ^ (family_to_string f2) ^ " to " ^ (delta_to_string d'') " : " (family_to_string f1) ^ ".\n"
	 | _ -> "Error: cannot apply " (delta_to_string d') ^ " : " ^ (family_to_string f2) ^ " to " ^ (delta_to_string d'') " : " (family_to_string f1) ^ ".\n"
       else err
     else err
  | DAnd (d', d'') -> let err = deltacheck d' gamma ctx in
		      if err = "" then deltacheck d'' gamma ctx
		      else err
  | DProjL d' -> let err = deltacheck d' gamma ctx in
		 if err = "" then
		   let f = deltainfer d' gamma ctx in
		   match f with
		   | SAnd (_, _) -> ""
		   | _ -> "Error: " ^ (delta_to_string d') ^ " has type " ^ (family_to_string f) ^ " (should be an intersection).\n"
		 else err
  | DProjR d' -> let err = deltacheck d' gamma ctx in
		 if err = "" then
		   let f = deltainfer d' gamma ctx in
		   match f with
		   | SAnd (_, _) -> ""
		   | _ -> "Error: " ^ (delta_to_string d') ^ " has type " ^ (family_to_string f) ^ " (should be an intersection).\n"
		 else err
  | DOr (x', f', d', x'', f'', d'', d''') ->
     let err = deltacheck d' ((x',f')::gamma) ctx in
     if err = "" then
       let err = deltacheck d'' ((x'',f'')::gamma) ctx in
       if err = "" then
	 let f3' = deltacheck d''' gamma ctx in
	 if err = "" then
	   let f1 = deltainfer d' ((x',f')::gamma) ctx in
	   let f2 = deltainfer d'' ((x'',f'')::gamma) ctx in
	   let f3 = deltainfer d''' gamma ctx in
	   if (unifiable f1 f2) && (unifiable (SOr(f',f'')) f3) then "" else "Error: cannot type " ^ (delta_to_string d) ^ ".\n"
	 else err
       else err
     else err
  | DInjL d' -> deltacheck d' gamma ctx
  | DInjR d' -> deltacheck d' gamma ctx

     (* /\ TO FINISH /\ *)
     (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

let typecstcheck id k ctx =
  if (find_all id ctx) then ("Error: " ^ id ^ " already exists.\n") else
    kindcheck k [] ctx

let cstcheck id f ctx =
  if (find_all id ctx) then ("Error: " ^ id ^ " already exists.\n") else
    let err =  familycheck f [] ctx in
    if err = "" then
      match familyinfer f [] ctx with
      | Type -> ""
      | k' -> "Error: " ^ (family_to_string f) ^ " has kind " ^ (kind_to_string k') ^ " (should be Type).\n"
    else
      err
