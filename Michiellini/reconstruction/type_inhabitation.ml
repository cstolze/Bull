open Definitions

let rec find_sigma varlist d =
  let rec vartype x l =
    match l with
    | [] -> failwith "there's a free variable"
    | (x', s) :: _ when x' = x -> s
    | _ :: l -> vartype x l
  in
  match d with
  | DMark i -> vartype i varlist
  | DApp (delta1, delta2) ->
     (
       match find_sigma varlist delta1 with
       | SFc (sigma, sigma') when find_sigma varlist delta2 = sigma -> sigma'
       | _ -> failwith "no sigma"
     )
  | DAnd (delta1, delta2) ->
     SAnd (find_sigma varlist delta1, find_sigma varlist delta2)
  | DLeft delta ->
     (
       match find_sigma varlist delta with
       | SAnd (sigma1, sigma2) -> sigma1
       | _ -> failwith "no sigma"
     )
  | DRight delta ->
     (
       match find_sigma varlist delta with
       | SAnd (sigma1, sigma2) -> sigma2
       | _ -> failwith "no sigma"
     )
  | DLambda (i, sigma, delta) ->
     SFc (sigma, find_sigma ((i, sigma)::varlist) delta)

let rec aux_find_m gam delta sigma varlist : m =
  match delta with
  | DMark i ->
     MVar (find_x i sigma gam)
  | DApp (delta1, delta2) ->
     let m1 = aux_find_m gam delta1 (find_sigma varlist delta1) varlist
     and m2 = aux_find_m gam delta2 (find_sigma varlist delta2) varlist
     in
     MApp (m1, m2)
  | DLambda (i, sigma', delta') ->
     (
       match sigma with
       | SFc (sigma1, sigma2) when sigma1 = sigma' ->
	  let gam' = (i, i, sigma1) :: gam in
	  let m' = aux_find_m gam' delta' sigma2 ((i, sigma1)::varlist) in
	  MLambda (i, i, m')
       | _ -> failwith "wrong entry"
     )
  | DAnd (delta1, delta2) ->
     (
       match sigma with
       | SAnd (sigma1, sigma2) ->
	  let m = aux_find_m gam delta1 sigma1 varlist
	  and m' = aux_find_m gam delta2 sigma2 varlist in
	  if alpha_conversion m m'
	  then m else failwith "wrong entry"
       | _ -> failwith "wrong entry"
     )
  | DLeft delta' ->
     let sigma' = find_sigma varlist delta' in
     aux_find_m gam delta' sigma' varlist
  | DRight delta' ->
     let sigma' = find_sigma varlist delta' in
     aux_find_m gam delta' sigma' varlist

let find_m delta =
  let sigma = find_sigma [] delta in
  aux_find_m [] delta sigma [], sigma;;

let main_ti lbd =
  let d = Parser_delta.d Lexer_delta.read lbd
  in let m, sigma = find_m d in
     print_string ("\nHere is the lambda term you were looking for:\n" ^ (m_to_string m) ^ "\nIts type is:\n" ^
		     (sigma_to_string sigma) ^ "\n\n")
