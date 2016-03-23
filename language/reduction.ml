open Utils

let rec brutal_sanitize delta env =
    match delta with
    | DVar x -> if find x env then DVar ("$"^x) else (* local variables shadow global ones *)
		  delta
    | DLambda (x, f, delta') -> DLambda ("$"^x, f, brutal_sanitize delta' ((x,f)::env))
    | DApp (delta', delta'') -> DApp (brutal_sanitize delta' env, brutal_sanitize delta'' env)
    | DAnd (delta', delta'') -> DAnd(brutal_sanitize delta' env, brutal_sanitize delta'' env)
    | DProjL delta' -> DProjL (brutal_sanitize delta' env)
    | DProjR delta' -> DProjR (brutal_sanitize delta' env)
    | DOr (x', f', delta', x'', f'', delta'', delta''') -> DOr ("$"^x',f',brutal_sanitize delta' ((x',f')::env),"$"^x'',f'',brutal_sanitize delta'' ((x'',f'')::env), brutal_sanitize delta''' env)
    | DInjL delta' -> DInjL (brutal_sanitize delta' env)
    | DInjR delta' -> DInjR (brutal_sanitize delta' env)

let compute d ctx =
  let rec compute' delta env =
    match delta with
    | DVar x -> if find x env then get x env else (* local variables shadow global ones *)
		  (if find_cst x ctx then DVar x else
		     (if find_def x ctx then let (delta', _) = get_def x ctx in compute' (brutal_sanitize delta' []) [] else
			DVar x))
    | DLambda (x, f, delta') -> DLambda (x, f, compute' delta' env)
    | DApp (delta', delta'') ->
       let d1 = compute' delta' env in
       let d2 = compute' delta'' env in
       (match d1 with
       | DLambda (x, _, d1') -> compute' d1' ((x,d2)::env)
       | _ -> DApp(d1, d2))
    | DAnd (delta', delta'') -> DAnd(compute' delta' env, compute' delta'' env)
    | DProjL delta' ->
       let d' = compute' delta' env in
       (match d' with
	| DAnd (d1, d2) -> d1
	| _ -> DProjL d')
    | DProjR delta' ->
       let d' = compute' delta' env in
       (match d' with
	| DAnd (d1, d2) -> d2
	| _ -> DProjR d')
    | DOr (x', f', delta', x'', f'', delta'', delta''') ->
       let d' = compute' delta' env in
       let d'' = compute' delta'' env in
       let d''' = compute' delta''' env in
       (match d''' with
       | DInjL d1''' -> compute' delta' ((x',d1''')::env)
       | DInjR d1''' -> compute' delta'' ((x'',d1''')::env)
       | _ -> DOr(x',f', d', x'', f'', d'', d'''))
    | DInjL delta' -> DInjL (compute' delta' env)
    | DInjR delta' -> DInjL (compute' delta' env)
  in
  compute' (brutal_sanitize d []) []
