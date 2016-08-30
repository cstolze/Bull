open Utils

(*
let rec to_string bd = (* for debugging purposes *)
  match bd with
  | BDVar (x,false,_) -> x
  | BDVar (x,true,n) -> "["^x^","^(string_of_int n)^"]"
  | BDLambda (x, f, bd') -> "(\\" ^ x ^ " " ^ (to_string bd') ^ ")"
  | BDApp (bd', bd'') -> "(" ^ (to_string bd') ^ " " ^ (to_string bd'') ^ ")"
  | BDAnd (bd', bd'') -> "< " ^ to_string bd' ^ " & " ^ (to_string bd'') ^ " >"
  | BDProjL bd' -> "(proj_l " ^ (to_string bd') ^ ")"
  | BDProjR bd' -> "(proj_r " ^  (to_string bd') ^ ")"
  | BDOr (x',f',bd',x'',f'',bd'',bd''') -> "< \\" ^ (to_string bd') ^ " | " ^ (to_string bd'') ^ " # " ^ (to_string bd''') ^ " >"
  | BDInjL bd' -> "(inj_l " ^ (to_string bd') ^ ")"
  | BDInjR bd' -> "(inj_r " ^ (to_string bd') ^ ")"
 *)

let rec family_apply n f1 d2 = (* replace the nth variable in f1 by d2 *)
  match f1 with
  | BSFc (f1', f2) -> BSFc (family_apply n f1' d2, family_apply (n+1) f2 d2)
  | BSProd (id, f1', f2) -> BSProd (id, family_apply n f1' d2, family_apply (n+1) f2 d2)
  | BSLambda (id, f1', f2) -> BSLambda (id, family_apply n f1' d2, family_apply (n+1) f2 d2)
  | BSApp (f1', d2') -> BSApp (family_apply n f1' d2, delta_apply n d2' d2)
  | BSAnd (f1', f2) -> BSAnd (family_apply n f1' d2, family_apply n f2 d2)
  | BSOr (f1', f2) -> BSOr (family_apply n f1' d2, family_apply n f2 d2)
  | BSAtom id -> f1
  | BSOmega -> f1
  | BSAnything -> f1
and delta_apply n d1 d2 = (* replace the nth variable in d1 by d2 *)
  let rec family_shift f n m =
    match f with
    | BSFc (f1', f2) -> BSFc (family_shift f1' n m, family_shift f2 n (m+1))
    | BSProd (id, f1', f2) -> BSProd (id, family_shift f1' n m, family_shift f2 n (m+1))
    | BSLambda (id, f1', f2) -> BSLambda (id, family_shift f1' n m, family_shift f2 n (m+1))
    | BSApp (f1', d2') -> BSApp (family_shift f1' n m, delta_shift d2 n m)
    | BSAnd (f1', f2) -> BSAnd (family_shift f1' n m, family_shift f2 n m)
    | BSOr (f1', f2) -> BSOr (family_shift f1' n m, family_shift f2 n m)
    | BSAtom id -> f
    | BSOmega -> f
    | BSAnything -> f
    and
      delta_shift d n m =
      match d with
      | BDVar (_,false,_) -> d
      | BDVar (x,true,n') -> BDVar(x,true,if n' < m then n' else n+n') (* we must verify whether the binding lies inside the current scope *)
      | BDStar -> d
      | BDLambda (x', f, d') -> BDLambda (x', family_shift f n m, delta_shift d' n (m+1))
      | BDApp (d', d'') -> BDApp (delta_shift d' n m, delta_shift d'' n m)
      | BDAnd (d', d'') -> BDAnd (delta_shift d' n m, delta_shift d'' n m)
      | BDProjL d' -> BDProjL (delta_shift d' n m)
      | BDProjR d' -> BDProjR (delta_shift d' n m)
      | BDOr (x',f',d',x'',f'',d'',d''') -> BDOr(x', family_shift f' n m, delta_shift d' n (m+1), x'', family_shift f'' n m, delta_shift d'' n (m+1), delta_shift d''' n m)
      | BDInjL d' -> BDInjL (delta_shift d' n m)
      | BDInjR d' -> BDInjR (delta_shift d' n m)
  in
  match d1 with
  | BDVar (id, b, n') -> if b then
			   if n = n' then delta_shift d2 n 0 else
			     if n < n' then BDVar (id, b, n'-1) else d1 (* we must verify whether the binding lies inside the current scope *)
			 else d1
  | BDStar -> d1
  | BDLambda (id, f1, d2') -> BDLambda (id, family_apply n f1 d2, delta_apply (n+1) d2' d2)
  | BDApp (d1', d2') -> BDApp (delta_apply n d1' d2, delta_apply n d2' d2)
  | BDAnd (d1', d2') -> BDAnd (delta_apply n d1' d2, delta_apply n d2' d2)
  | BDProjL d' -> BDProjL (delta_apply n d' d2)
  | BDProjR d' -> BDProjR (delta_apply n d' d2)
  | BDOr (id1, f1, d1', id2, f2, d2', d3) ->
     BDOr (id1,
	   family_apply n f1 d2,
	   delta_apply (n+1) d1' d2,
	   id2,
	   family_apply n f2 d2,
	   delta_apply (n+1) d2' d2,
	   delta_apply n d3 d2)
  | BDInjL d' -> BDInjL (delta_apply n d' d2)
  | BDInjR d' -> BDInjR (delta_apply n d' d2)

let rec kind_apply n k d =
  match k with
  | BType -> k
  | BKProd (id, f, k') -> BKProd (id, family_apply n f d, kind_apply (n+1) k' d)

(* in the _compute functions, the terms are supposed to be well-typed and therefore they strongly normalize *)
let rec family_compute f ctx =
  match f with
  | BSFc (f1, f2) -> BSFc (family_compute f1 ctx, family_compute f2 ctx)
  | BSProd (id, f1, f2) -> BSProd (id, family_compute f1 ctx, family_compute f2 ctx)
  | BSLambda (id, f1, f2) -> BSLambda (id, family_compute f1 ctx, family_compute f2 ctx)
  | BSApp (f1, d2) ->
     let f' = family_compute f1 ctx in
     let d'' = delta_compute d2 ctx in
     (match f1 with
      | BSLambda (_,_,f2) -> family_compute (family_apply 0 f2 d'') ctx
      | _ -> BSApp (f', d''))
  | BSAnd (f1, f2) -> BSAnd (family_compute f1 ctx, family_compute f2 ctx)
  | BSOr (f1, f2) -> BSOr (family_compute f1 ctx, family_compute f2 ctx)
  | BSAtom id -> f
  | BSOmega -> f
  | BSAnything -> f
  and
    delta_compute d ctx =
    match d with
    | BDVar (id, false,_) -> if find_def id ctx then let (a,_) = get_def id ctx in delta_compute a ctx else d
    | BDVar (_, true,_) -> d
    | BDStar -> d
    | BDLambda (x, f, d') -> let d'' = delta_compute d' ctx in
			     (match d'' with
			      | BDApp (d''', BDVar(x',true, 0)) -> (* eta-reduction *)
				 let rec familycheck f n =
				   match f with
				       | BSFc (f1, f2) -> familycheck f1 n && familycheck f2 (n+1)
				       | BSProd (id, f1, f2) -> familycheck f1 n && familycheck f2 (n+1)
				       | BSLambda (id, f1, f2) -> familycheck f1 n && familycheck f2 (n+1)
				       | BSApp (f1, d2) -> familycheck f1 n && deltacheck d2 n
				       | BSAnd (f1, f2) -> familycheck f1 n && familycheck f2 n
				       | BSOr (f1, f2) -> familycheck f1 n && familycheck f2 n
				       | BSAtom id -> true
				       | BSOmega -> true
				       | BSAnything -> true
				 and deltacheck d n =
				   match d with
				   | BDVar (_,b,n) -> if b then n <> 0 else true
				   | BDStar -> true
				   | BDLambda (x', f, d') -> familycheck f n && deltacheck d' (n+1)
				   | BDApp (d', d'') -> deltacheck d' n && deltacheck d'' n
				   | BDAnd (d', d'') -> deltacheck d' n && deltacheck d'' n
				   | BDProjL d' -> deltacheck d' n
				   | BDProjR d' -> deltacheck d' n
				   | BDOr (x',f',d',x'',f'',d'',d''') ->
				      familycheck f' n && deltacheck d' (n+1)
				      && familycheck f'' n && deltacheck d'' (n+1)
				      && deltacheck d''' n
				   | BDInjL d' -> deltacheck d' n
				   | BDInjR d' -> deltacheck d' n
				 in if deltacheck d''' 0 (* verify whether x is _not_ free in d''' *)
				    then delta_apply 0 d''' BDStar (* trick to decrement the variable indexes in d''' *)
				    else BDLambda (x, family_compute f ctx, d'')
			      | _ -> BDLambda (x, family_compute f ctx, d''))
    | BDApp (d', d'') ->
       let d1 = delta_compute d' ctx in
       let d2 = delta_compute d'' ctx in
       (match d1 with
	| BDLambda (_,_,d1') -> delta_compute (delta_apply 0 d1' d2) ctx
	| _ -> BDApp (d1, d2))
    | BDAnd (d', d'') ->
       let rec eq d1 d2 =
	 match (d1, d2) with
	 | (BDVar (id1,false,_), BDVar(id2,false,_)) -> id1 = id2
	 | (BDVar (_,true,n1), BDVar(_,true,n2)) -> n1 = n2
	 | (BDStar, BDStar) -> true
	 | (BDLambda (_, _, d'), BDLambda (_, _, d'')) -> eq d' d''
	 | (BDApp (d', d''), BDApp (d_', d_'')) -> (eq d' d_') && (eq d'' d_'')
	 | (BDAnd (d', d''), BDAnd (d_', d_'')) -> (eq d' d_') && (eq d'' d_'')
	 | (BDProjL d', BDProjL d'') -> eq d' d''
	 | (BDProjR d', BDProjR d'') -> eq d' d''
	 | (BDOr (_,_,d',_,_,d'',d'''), BDOr (_,_,d_',_,_,d_'',d_''')) -> (eq d' d_') && (eq d'' d_'') && (eq d''' d_''')
	 | (BDInjL d', BDInjL d'') -> eq d' d''
	 | (BDInjR d', BDInjR d'') -> eq d' d''
	 | (_,_) -> false
       in
       let d1 = delta_compute d' ctx in
       let d2 = delta_compute d'' ctx in
       (match (d1, d2) with
	| (BDProjL d1', BDProjR d2') -> if eq d1' d2' then d1' else BDAnd(d1,d2)
	| (_,_) -> BDAnd (d1, d2))
    | BDProjL d' ->
       let d1 = delta_compute d' ctx in
       (match d1 with
	| BDAnd (d1', _) -> d1'
	| _ -> BDProjL d1)
    | BDProjR d' ->
       let d1 = delta_compute d' ctx in
       (match d1 with
	| BDAnd (_, d1') -> d1'
	| _ -> BDProjR d1)
    | BDOr (x',f',d',x'',f'',d'',d''') ->
       let d1 = delta_compute d''' ctx in
       (match d1 with
	| BDInjL d1' -> delta_compute (delta_apply 0 d' d1') ctx
	| BDInjR d1' -> delta_compute (delta_apply 0 d'' d1') ctx
	| _ ->
	   let rec eq d1 d2 n =
	     match (d1, d2) with
	     | (BDVar (id1,false,_), BDVar(id2,false,_)) -> id1 = id2
	     | (BDVar (_,true,n1), BDVar(_,true,n2)) -> n1 = n2 && not (n1 = n)
	     | (BDStar, BDStar) -> true
	     | (BDLambda (_, _, d'), BDLambda (_, _, d'')) -> eq d' d'' (n+1)
	     | (BDApp (d', d''), BDApp (d_', d_'')) -> (eq d' d_' n) && (eq d'' d_'' n)
	     | (BDAnd (d', d''), BDAnd (d_', d_'')) -> (eq d' d_' n) && (eq d'' d_'' n)
	     | (BDProjL d', BDProjL d'') -> eq d' d'' n
	     | (BDProjR d', BDProjR d'') -> eq d' d'' n
	     | (BDOr (_,_,d',_,_,d'',d'''), BDOr (_,_,d_',_,_,d_'',d_''')) -> (eq d' d_' (n+1)) && (eq d'' d_'' (n+1)) && (eq d''' d_''' n)
	     | (BDInjL d', BDInjL d'') -> eq d' d'' n
	     | (BDInjR d', BDInjR d'') -> eq d' d'' n
	     | (BDInjL (BDVar(_,true,n1)), BDInjR (BDVar (_,true,n2))) -> n1 = n2 && n1 = n
	     | (_,_) -> false
	   in
	   let rec get_delta d n =
	     match d with
	     | BDVar (_,_,_) -> d
	     | BDStar -> d
	     | BDLambda (x', f, d') -> BDLambda (x', f, get_delta d' (n+1))
	     | BDApp (d', d'') -> BDApp (get_delta d' n, get_delta d'' n)
	     | BDAnd (d', d'') -> BDAnd (get_delta d' n, get_delta d'' n)
	     | BDProjL d' -> BDProjL (get_delta d' n)
	     | BDProjR d' -> BDProjR (get_delta d' n)
	     | BDOr (x',f',d',x'',f'',d'',d''') -> BDOr(x', f', get_delta d' (n+1), x'', f'', get_delta d'' (n+1), get_delta d''' n)
	     | BDInjL (BDVar (id,true, n)) -> BDVar (id, true, n)
	     | BDInjL d' -> BDInjL (get_delta d' n)
	     | BDInjR d' -> BDInjR (get_delta d' n)
	   in
	   let d2 = delta_compute d' ctx in
	   let d3 = delta_compute d'' ctx in
	   if eq d2 d3 0 then delta_compute (delta_apply 0 (get_delta d2 0) d1) ctx (* <\x. M[inj_l x/x] | \x. M[inj_r x/x] # N > --> M[N/x] *)
	   else BDOr(x', family_compute f' ctx, d2, x'', family_compute f'' ctx, d3, d1)
       )
    | BDInjL d' -> BDInjL (delta_compute d' ctx)
    | BDInjR d' -> BDInjR (delta_compute d' ctx)

let rec kind_compute k ctx =
  match k with
  | BType -> BType
  | BKProd (id, f, k') -> BKProd (id, family_compute f ctx, kind_compute k' ctx)
