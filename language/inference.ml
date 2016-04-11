open Utils

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

let (inference, inferable) =
  let rec inference' d gamma ctx =
    match d with
    | DVar x -> if find x gamma then get x gamma else (* local variables shadow global ones *)
		  (if find_cst x ctx then get_cst x ctx else
		     (if find_def x ctx then let (_, f) = get_def x ctx in f else
			failwith "the programmer should ensure this does not happen (use the inferable function)"))
    | DStar -> SOmega
    | DLambda (x, f, d') -> SFc (f, inference' d' ((x,f)::gamma) ctx)
    | DApp (d', d'') ->
       let f1 = inference' d'' gamma ctx in
       (match inference' d' gamma ctx with
	| SFc (f', f2) -> if unifiable f' f1 then f2 else failwith "the programmer should ensure this does not happen (use the inferable function)"
       | _ -> failwith "the programmer should ensure this does not happen (use the inferable function)")
    | DAnd (d', d'') -> SAnd (inference' d' gamma ctx, inference' d'' gamma ctx)
    | DProjL d' -> (match (inference' d' gamma ctx) with
		   | SAnd (f1, f2) -> f1
		   | _ -> failwith "the programmer should ensure this does not happen (use the inferable function)")
    | DProjR d' -> (match (inference' d' gamma ctx) with
		   | SAnd (f1, f2) -> f2
		   | _ -> failwith "the programmer should ensure this does not happen (use the inferable function)")
    | DOr (x', f', d', x'', f'', d'', d''') ->
       let f1 = inference' d' ((x',f')::gamma) ctx in
       let f2 = inference' d'' ((x'',f'')::gamma) ctx in
       let f3 = inference' d''' gamma ctx in
       if (unifiable f1 f2) && (unifiable (SOr(f',f'')) f3) then
	 unify f1 f2
       else
	 failwith "the programmer should ensure this does not happen (use the inferable function)"
    | DInjL d' -> SOr(inference' d' gamma ctx, SAnything)
    | DInjR d' -> SOr(SAnything, inference' d' gamma ctx)
  in
  let rec inferable' d gamma ctx =
    match d with
    | DVar x -> if find x gamma then true else
		  (if find_cst x ctx then true else
		     find_def x ctx)
    | DStar -> true
    | DLambda (x, f, d') -> inferable' d' ((x,f)::gamma) ctx
    | DApp (d', d'') ->
       if (inferable' d' gamma ctx && inferable' d'' gamma ctx) then
	 let f1 = inference' d'' gamma ctx in
	 match inference' d' gamma ctx with
	 | SFc (f', f2) -> unifiable f' f1
	 | _ -> false
       else false
    | DAnd (d', d'') -> inferable' d' gamma ctx && inferable' d'' gamma ctx
    | DProjL d' -> if inferable' d' gamma ctx then
		     match (inference' d' gamma ctx) with
		     | SAnd (_, _) -> true
		     | _ -> false
		   else false
    | DProjR d' -> if inferable' d' gamma ctx then
		     match (inference' d' gamma ctx) with
		     | SAnd (_, _) -> true
		     | _ -> false
		   else false
    | DOr (x', f', d', x'', f'', d'', d''') ->
       let f1' = inferable' d' ((x',f')::gamma) ctx in
       let f2' = inferable' d'' ((x'',f'')::gamma) ctx in
       let f3' = inferable' d''' gamma ctx in
       if f1' && f2' && f3' then
	 let f1 = inference' d' ((x',f')::gamma) ctx in
	 let f2 = inference' d'' ((x'',f'')::gamma) ctx in
	 let f3 = inference' d''' gamma ctx in
	 (unifiable f1 f2) && (unifiable (SOr(f',f'')) f3)
       else false
    | DInjL d' -> inferable' d' gamma ctx
    | DInjR d' -> inferable' d' gamma ctx
  in ((fun d ctx -> inference' d [] ctx), (fun d ctx -> inferable' d [] ctx))
