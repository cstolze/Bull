open Utils

type bruijndelta =
  | BDVar of string * bool * int (* id * is_bound? * bruijn index *)
  | BDLambda of string * family * bruijndelta
  | BDApp of bruijndelta * bruijndelta
  | BDAnd of bruijndelta * bruijndelta
  | BDProjL of bruijndelta
  | BDProjR of bruijndelta
  | BDOr of string * family * bruijndelta * string * family * bruijndelta * bruijndelta
  | BDInjL of bruijndelta
  | BDInjR of bruijndelta


let to_bruijndelta delta ctx =
  let rec foo d env =
    let rec find_env x l =
      match l with
      | [] -> false
      | y :: l' -> if x = y then true else find_env x l'
    in
    let rec get_env x l n =
      match l with
      | [] -> failwith "use find_env"
      | y :: l' -> if x = y then n else get_env x l' (n+1)
    in
    match d with
    | DVar x -> if find_env x env then BDVar (x, true, get_env x env 0) (* local variables shadow global ones *)
		else if find_def x ctx then let (d', _) = get_def x ctx in foo d' [] (* definition-reduction *)
		else BDVar(x, false, 0)
    | DLambda (x, f, d') -> BDLambda (x, f, foo d' (x::env))
    | DApp (d', d'') -> BDApp (foo d' env, foo d'' env)
    | DAnd (d', d'') -> BDAnd (foo d' env, foo d'' env)
    | DProjL d' -> BDProjL (foo d' env)
    | DProjR d' -> BDProjR (foo d' env)
    | DOr (x', f', d', x'', f'', d'', d''') -> BDOr (x', f', foo d' (x'::env), x'', f'', foo d'' (x''::env), foo d''' env)
    | DInjL d' -> BDInjL (foo d' env)
    | DInjR d' -> BDInjR (foo d' env)
  in
  foo delta []

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

let rec to_delta bd =
  let rec replace bd x x' n = (* replace x (with n as a de Bruijn) index by x' in bd *)
    match bd with
    | BDVar (_,false,_) -> bd
    | BDVar (y, true, n') -> if (x = y) && (n = n') then BDVar(x', true, n') else bd
    | BDLambda (x0, f, bd') -> BDLambda(x0,f, replace bd' x x' (n+1))
    | BDApp (bd', bd'') -> BDApp(replace bd' x x' n, replace bd'' x x' n)
    | BDAnd (bd', bd'') -> BDAnd(replace bd' x x' n, replace bd'' x x' n)
    | BDProjL bd' -> BDProjL (replace bd' x x' n)
    | BDProjR bd' -> BDProjR (replace bd' x x' n)
    | BDOr (x0',f',bd',x'',f'',bd'',bd''') -> BDOr(x0', f', replace bd' x x' (n+1), x'', f'', replace bd'' x x' (n+1), replace bd''' x x' n)
    | BDInjL bd' -> BDInjL (replace bd' x x' n)
    | BDInjR bd' -> BDInjR (replace bd' x x' n)
  in
  let rec alpha_check x bd n =
    match bd with
    | BDVar (y,false,_) -> not (x = y)
    | BDVar (y, true, n') -> if (x = y) then (n = n') else true
    | BDLambda (x0, f, bd') -> alpha_check x bd' (n+1)
    | BDApp (bd', bd'') -> (alpha_check x bd' n) && (alpha_check x bd'' n)
    | BDAnd (bd', bd'') -> (alpha_check x bd' n) && (alpha_check x bd'' n)
    | BDProjL bd' -> alpha_check x bd n
    | BDProjR bd' -> alpha_check x bd n
    | BDOr (x',f',bd',x'',f'',bd'',bd''') -> (alpha_check x bd' (n+1)) && (alpha_check x bd'' (n+1)) && (alpha_check x bd''' n)
    | BDInjL bd' -> alpha_check x bd n
    | BDInjR bd' -> alpha_check x bd n
  in
  let rec alpha_convert x bd n =
    match n with
    | None -> if alpha_check x bd 0 then (x,bd) else alpha_convert x bd (Some 0)
    | Some n' ->
       let x' = x ^ (string_of_int n') in
       if alpha_check x' bd 0 then (x', replace bd x x' 0) else alpha_convert x bd (Some (n'+1))
  in
  match bd with
  | BDVar (x,_,_) -> DVar x
  | BDLambda (x, f, bd') -> let (x',bd0) = alpha_convert x bd' None in DLambda (x', f, to_delta bd0)
  | BDApp (bd', bd'') -> DApp (to_delta bd', to_delta bd'')
  | BDAnd (bd', bd'') -> DAnd (to_delta bd', to_delta bd'')
  | BDProjL bd' -> DProjL (to_delta bd')
  | BDProjR bd' -> DProjR (to_delta bd')
  | BDOr (x',f',bd',x'',f'',bd'',bd''') -> DOr (x',f',to_delta bd',x'',f'', to_delta bd'', to_delta bd''')
  | BDInjL bd' -> DInjL (to_delta bd')
  | BDInjR bd' -> DInjR (to_delta bd')

let compute delta ctx =
  let rec shift bd n m =
    match bd with
    | BDVar (_,false,_) -> bd
    | BDVar (x,true,n') -> BDVar(x,true,if n' < m then n' else n+n') (* we must verify whether the binding lies inside the current scope *)
    | BDLambda (x', f, bd') -> BDLambda (x', f, shift bd' n (m+1))
    | BDApp (bd', bd'') -> BDApp (shift bd' n m, shift bd'' n m)
    | BDAnd (bd', bd'') -> BDAnd (shift bd' n m, shift bd'' n m)
    | BDProjL bd' -> BDProjL (shift bd' n m)
    | BDProjR bd' -> BDProjR (shift bd' n m)
    | BDOr (x',f',bd',x'',f'',bd'',bd''') -> BDOr(x', f', shift bd' n (m+1), x'', f'', shift bd'' n (m+1), shift bd''' n m)
    | BDInjL bd' -> BDInjL (shift bd' n m)
    | BDInjR bd' -> BDInjR (shift bd' n m)
  in
  let rec replace bd x n =
    match bd with
    | BDVar (_,false,_) -> bd
    | BDVar (x',true,n') -> if n = n' then shift x n 0 else
			      if n < n' then BDVar (x',true, n'-1) else bd (* we must verify whether the binding lies inside the current scope *)
    | BDLambda (x', f, bd') -> BDLambda (x', f, replace bd' x (n+1))
    | BDApp (bd', bd'') -> BDApp (replace bd' x n, replace bd'' x n)
    | BDAnd (bd', bd'') -> BDAnd (replace bd' x n, replace bd'' x n)
    | BDProjL bd' -> BDProjL (replace bd' x n)
    | BDProjR bd' -> BDProjR (replace bd' x n)
    | BDOr (x',f',bd',x'',f'',bd'',bd''') -> BDOr(x', f', replace bd' x (n+1), x'', f'', replace bd'' x (n+1), replace bd''' x n)
    | BDInjL bd' -> BDInjL (replace bd' x n)
    | BDInjR bd' -> BDInjR (replace bd' x n)
  in
  let rec compute' bd =
    match bd with
    | BDVar (_,_,_) -> bd
    | BDLambda (x, f, bd') -> BDLambda (x, f, compute' bd')
    | BDApp (bd', bd'') ->
       let bd1 = compute' bd' in
       let bd2 = compute' bd'' in
       (match bd1 with
	| BDLambda (_,_,bd1') -> compute' (replace bd1' bd2 0)
	| _ -> BDApp (bd1, bd2))
    | BDAnd (bd', bd'') -> BDAnd (compute' bd', compute' bd'')
    | BDProjL bd' ->
       let bd1 = compute' bd' in
       (match bd1 with
       | BDAnd (bd1', _) -> bd1'
       | _ -> BDProjL bd1)
    | BDProjR bd' ->
       let bd1 = compute' bd' in
       (match bd1 with
	| BDAnd (_, bd1') -> bd1'
	| _ -> BDProjR bd1)
    | BDOr (x',f',bd',x'',f'',bd'',bd''') ->
       let bd1 = compute' bd''' in
       (match bd1 with
       | BDInjL bd1' -> compute' (replace bd' bd1' 0)
       | BDInjR bd1' -> compute' (replace bd'' bd1' 0)
       | _ -> BDOr(x', f', compute' bd', x'', f'', compute' bd'', bd1)
       )
    | BDInjL bd' -> BDInjL (compute' bd')
    | BDInjR bd' -> BDInjR (compute' bd')
  in
  to_delta (compute' (to_bruijndelta delta ctx))

