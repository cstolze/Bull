(* conversion functions bruijn <-> normal *)
(* TO FIX *)

(* TODO:
cf matita source code:
substitution
lift
fix_index => if the index are wrong and the ids are correct (for the lexer)
fix_id => if the ids are wrong and the index are correct (after beta-conversion)
also function for fixing Gamma
 *)

let (family_to_bruijn, delta_to_bruijn, delta_gamma) =
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
  let rec family_to_bruijn' f env =
    match f with
    | SFc (f1, f2) -> BSFc (family_to_bruijn' f1 env, family_to_bruijn' f2 ("" :: env))
    | SProd (id, f1, f2) -> BSProd (id, family_to_bruijn' f1 env, family_to_bruijn' f2 (id::env))
    | SLambda (id, f1, f2) -> BSLambda (id, family_to_bruijn' f1 env, family_to_bruijn' f2 (id::env))
    | SApp (f1, d2) -> BSApp (family_to_bruijn' f1 env, delta_to_bruijn' d2 env)
    | SAnd (f1, f2) -> BSAnd (family_to_bruijn' f1 env, family_to_bruijn' f2 env)
    | SOr (f1, f2) -> BSOr (family_to_bruijn' f1 env, family_to_bruijn' f2 env)
    | SAtom id -> BSAtom id
    | SOmega -> BSOmega
    | SAnything -> BSAnything
    and
      delta_to_bruijn' d env =
      match d with
      | DVar id -> if find_env id env then BDVar (id, true, get_env id env 0) (* local variables shadow global ones *)
		   else BDVar(id, false, 0)
      | DStar -> BDStar
      | DLambda (id, f1, d') -> BDLambda (id, family_to_bruijn' f1 env, delta_to_bruijn' d' (id::env))
      | DApp (d1, d2) -> BDApp (delta_to_bruijn' d1 env, delta_to_bruijn' d2 env)
      | DAnd (d1, d2) -> BDAnd (delta_to_bruijn' d1 env, delta_to_bruijn' d2 env)
      | DProjL d' -> BDProjL (delta_to_bruijn' d' env)
      | DProjR d' -> BDProjR (delta_to_bruijn' d' env)
      | DOr (id', f', d', id'', f'', d'', d''') -> BDOr (id', family_to_bruijn' f' env, delta_to_bruijn' d' (id'::env), id'', family_to_bruijn' f'' env, delta_to_bruijn' d'' (id''::env), delta_to_bruijn' d''' env)
      | DInjL d' -> BDInjL (delta_to_bruijn' d' env)
      | DInjR d' -> BDInjR (delta_to_bruijn' d' env)
  in ((fun f -> family_to_bruijn' f []), (fun d -> delta_to_bruijn' d []), (fun d -> fun g -> delta_to_bruijn' d g))

let rec kind_to_bruijn k =
  match k with
  | Type -> BType
  | KProd (id, f, k') -> BKProd (id, family_to_bruijn f, kind_to_bruijn k')

let rec alpha_conv id b n check replace =
  match n with
  | None -> if check id b 0 then (id, b) else alpha_conv id b (Some 0) check replace
  | Some n' ->
     let id' = id ^ (string_of_int n') in
     if check id' b 0 then (id', replace b id' 0) else alpha_conv id b (Some (n'+1)) check replace

let rec f_check id f n =
  match f with
  | BSFc (f1, f2) -> (f_check id f1 n) && (f_check id f2 (n+1))
  | BSProd (id', f1, f2) -> (f_check id f1 n) && (f_check id f2 (n+1))
  | BSLambda (id', f1, f2) -> (f_check id f1 n) && (f_check id f2 (n+1))
  | BSApp (f1, d2) -> (f_check id f1 n) && (d_check id d2 n)
  | BSAnd (f1, f2) -> (f_check id f1 n) && (f_check id f2 n)
  | BSOr (f1, f2) -> (f_check id f1 n) && (f_check id f2 n)
  | BSAtom id' -> true
  | BSOmega -> true
  | BSAnything -> true
  and
    d_check id d n =
    match d with
    | BDVar (id', false, n') -> not (id = id')
    | BDVar (id', true, n') -> if (id = id') then (n >= n') else true (* no free variable should be called id *)
    | BDStar -> true
    | BDLambda (id', f1, d') -> (f_check id f1 n) && (d_check id d' (n+1))
    | BDApp (d1, d2) -> (d_check id d1 n) && (d_check id d2 n)
    | BDAnd (d1, d2) -> (d_check id d1 n) && (d_check id d2 n)
    | BDProjL d' -> d_check id d' n
    | BDProjR d' -> d_check id d' n
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       (f_check id f' n) &&
	 (d_check id d' (n+1)) &&
	   (f_check id f'' n) &&
	     (d_check id d'' (n+1)) &&
	       (d_check id d''' n)
    | BDInjL d' -> d_check id d' n
    | BDInjR d' -> d_check id d' n

let rec f_replace f id n =
  match f with
  | BSFc (f1, f2) -> BSFc (f_replace f1 id n, f_replace f2 id (n+1))
  | BSProd (id', f1, f2) -> BSProd (id', f_replace f1 id n, f_replace f2 id (n+1))
  | BSLambda (id', f1, f2) -> BSLambda (id', f_replace f1 id n, f_replace f2 id (n+1))
  | BSApp (f1, d2) -> BSApp (f_replace f1 id n, d_replace d2 id n)
  | BSAnd (f1, f2) -> BSAnd (f_replace f1 id n, f_replace f2 id n)
  | BSOr (f1, f2) -> BSOr (f_replace f1 id n, f_replace f2 id n)
  | BSAtom id' -> f
  | BSOmega -> f
  | BSAnything -> f
  and
    d_replace d id n =
    match d with
    | BDVar (id', false, n') -> d
    | BDVar (id', true, n') -> if (n = n') then BDVar (id, true, n') else d
    | BDStar -> d
    | BDLambda (id', f1, d') -> BDLambda (id', f_replace f1 id n, d_replace d' id (n+1))
    | BDApp (d1, d2) -> BDApp (d_replace d1 id n, d_replace d2 id n)
    | BDAnd (d1, d2) -> BDAnd (d_replace d1 id n, d_replace d2 id n)
    | BDProjL d' -> BDProjL (d_replace d' id n)
    | BDProjR d' -> BDProjR (d_replace d' id n)
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       BDOr (id',
	     f_replace f' id n,
	     d_replace d' id (n+1),
	     id'',
	     f_replace f'' id n,
	     d_replace d'' id (n+1),
	     d_replace d''' id n)
    | BDInjL d' -> BDInjL (d_replace d' id n)
    | BDInjR d' -> BDInjR (d_replace d' id n)

let rec bruijn_to_family f =
  match f with
  | BSFc (f1, f2) -> SFc (bruijn_to_family f1, bruijn_to_family f2)
  | BSProd (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SProd (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSLambda (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SLambda (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSApp (f1, d2) -> SApp (bruijn_to_family f1, bruijn_to_delta d2)
  | BSAnd (f1, f2) -> SAnd (bruijn_to_family f1, bruijn_to_family f2)
  | BSOr (f1, f2) -> SOr (bruijn_to_family f1, bruijn_to_family f2)
  | BSAtom id -> SAtom id
  | BSOmega -> SOmega
  | BSAnything -> SAnything
  and
    bruijn_to_delta d =
    match d with
    | BDVar (id, b, n) -> DVar id
    | BDStar -> DStar
    | BDLambda (id, f1, d') -> let (id', d'') = alpha_conv id d' None d_check d_replace in DLambda (id', bruijn_to_family f1, bruijn_to_delta d'')
    | BDApp (d1, d2) -> DApp (bruijn_to_delta d1, bruijn_to_delta d2)
    | BDAnd (d1, d2) -> DAnd (bruijn_to_delta d1, bruijn_to_delta d2)
    | BDProjL d' -> DProjL (bruijn_to_delta d')
    | BDProjR d' -> DProjR (bruijn_to_delta d')
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       let (id'1, d'1) = alpha_conv id' d' None d_check d_replace in
       let (id''1, d''1) = alpha_conv id'' d'' None d_check d_replace in
       DOr (id'1, bruijn_to_family f', bruijn_to_delta d'1, id''1, bruijn_to_family f'', bruijn_to_delta d''1, bruijn_to_delta d''')
    | BDInjL d' -> DInjL (bruijn_to_delta d')
    | BDInjR d' -> DInjR (bruijn_to_delta d')

let rec bruijn_to_kind k =
  let rec k_check id k n =
    match k with
    | BType -> true
    | BKProd (id', f, k') -> (f_check id f n) && (k_check id k' (n+1))
  in
  let rec k_replace k id n =
    match k with
    | BType -> k
    | BKProd (id', f, k') -> BKProd (id', f_replace f id n, k_replace k' id (n+1))
  in
  match k with
  | BType -> Type
  | BKProd (id, f, k') -> let (id', k'') = alpha_conv id k' None k_check k_replace in KProd (id', bruijn_to_family f, bruijn_to_kind k'')
