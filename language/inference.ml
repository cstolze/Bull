open Utils

let rec is_wellformed d =
  let rec to_bruijn d = (* convert d to a lambda-term with De Bruijn indexes, here d is supposed well-formed *)
    let rec update b x n =
      match b with
      | BVar (y,false,_) -> if (y = x) then BVar(y, true, n) else b
      | BVar (_,true,_) -> b
      | BLambda b' -> BLambda (update b' x (n+1))
      | BApp (b', b'') -> BApp (update b' x n, update b'' x n)
    in
    match d with
      | DVar x -> BVar(x, false, 0)
      | DLambda (x, f, d') -> BLambda (update (to_bruijn d') x 0)
      | DApp (d', d'') -> BApp (to_bruijn d', to_bruijn d'')
      | DAnd (d', _) -> to_bruijn d'
      | DProjL d' -> to_bruijn d'
      | DProjR d' -> to_bruijn d'
      | DOr (d', _) -> to_bruijn d'
      | DInjL d' -> to_bruijn d'
      | DInjR d' -> to_bruijn d'
  in
  let rec equal_bruijn b1 b2 =
    match (b1, b2) with
    | BVar (x, false,_), BVar(y, false, _) -> x = y
    | BVar (_, true, n), BVar(_, true, n') -> n = n'
    | BLambda b1', BLambda b2' -> equal_bruijn b1' b2'
    | BApp (b1', b1''), BApp (b2', b2'') -> equal_bruijn b1' b2' && equal_bruijn b1'' b2''
    | _, _ -> false
  in
  match d with
  | DVar x -> true
  | DLambda (x,f,d') -> is_wellformed d'
  | DApp (d', d'') -> (is_wellformed d') && (is_wellformed d'')
  | DAnd (d',d'') -> (is_wellformed d') && (is_wellformed d'') && (equal_bruijn (to_bruijn d') (to_bruijn d''))
  | DProjL d' -> is_wellformed d'
  | DProjR d' -> is_wellformed d'
  | DOr (d',d'') -> (is_wellformed d') && (is_wellformed d'') && (equal_bruijn (to_bruijn d') (to_bruijn d''))
  | DInjL d' -> is_wellformed d'
  | DInjR d' -> is_wellformed d'


(* IMPORTANT NOTE : THE DISJUNCTION IS NOT SUPPORTED YET *)
let (inference, inferable) =
  let rec foo d gamma ctx =
    match d with
    | DVar x -> if find x gamma then get x gamma else
		  (if find_cst x ctx then get_cst x ctx else
		     (if find_def x ctx then let (_, f) = get_def x ctx in f else
			failwith "the programmer should ensure this does not happen (use the inferable function)"))
    | DLambda (x, f, d') -> SFc (f, foo d' ((x,f)::gamma) ctx)
    | DApp (d', d'') ->
       let f1 = foo d'' gamma ctx in
       (match foo d' gamma ctx with
       | SFc (f', f2) -> if f' = f1 then f2 else failwith "the programmer should ensure this does not happen (use the inferable function)"
       | _ -> failwith "the programmer should ensure this does not happen (use the inferable function)")
    | DAnd (d', d'') -> SAnd (foo d' gamma ctx, foo d'' gamma ctx)
    | DProjL d' -> (match (foo d' gamma ctx) with
		   | SAnd (f1, f2) -> f1
		   | _ -> failwith "the programmer should ensure this does not happen (use the inferable function)")
    | DProjR d' -> (match (foo d' gamma ctx) with
		   | SAnd (f1, f2) -> f2
		   | _ -> failwith "the programmer should ensure this does not happen (use the inferable function)")
    | DOr (d', d'') -> failwith "not implemented yet"
    | DInjL d' -> failwith "not implemented yet"
    | DInjR d' -> failwith "not implemented yet"
  in
  let rec bar d gamma ctx =
    match d with
    | DVar x -> if find x gamma then true else
		  (if find_cst x ctx then true else
		     (if find_def x ctx then true else
			false))
    | DLambda (x, f, d') -> bar d' ((x,f)::gamma) ctx
    | DApp (d', d'') ->
       if (bar d' gamma ctx && bar d'' gamma ctx) then
	 let f1 = foo d'' gamma ctx in
	 match foo d' gamma ctx with
	 | SFc (f', f2) -> if f' = f1 then true else false
	 | _ -> false
       else false
    | DAnd (d', d'') -> bar d' gamma ctx && bar d'' gamma ctx
    | DProjL d' -> if bar d' gamma ctx then
		     match (foo d' gamma ctx) with
		     | SAnd (_, _) -> true
		     | _ -> false
		   else false
    | DProjR d' -> if bar d' gamma ctx then
		     match (foo d' gamma ctx) with
		     | SAnd (_, _) -> true
		     | _ -> false
		   else false
    | DOr (d', d'') -> false (* not implemented yet *)
    | DInjL d' -> false (* not implemented yet *)
    | DInjR d' -> false (* not implemented yet *)
  in ((fun d ctx -> foo d [] ctx), (fun d ctx -> bar d [] ctx))
