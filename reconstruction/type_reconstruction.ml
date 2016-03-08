open Definitions

let rec find_type gam m delta : sigma =
  match m, delta with
  | _, DRight delta' -> (
    match find_type gam m delta' with
    | SAnd (sigma1, sigma2) -> sigma2
    | _ -> failwith "wrong entry"
  )
  | _, DLeft delta' -> (
    match find_type gam m delta' with
    | SAnd (sigma1, sigma2) -> sigma1
    | _ -> failwith "wrong entry"
  )
  | _, DAnd (delta1, delta2) ->
     let sigma1 = find_type gam m delta1
     and sigma2 = find_type gam m delta2 in
     SAnd (sigma1, sigma2)
  | MVar x, _ -> find_sigma x gam
  | MLambda (x, i, m'), DLambda (j, sigma1, delta') when i = j ->
     (
       try (let _ = find_sigma x gam in failwith "wrong entry")
       with Failure "empty list" ->
	 (
	   let sigma2 = find_type ((x, i, sigma1) :: gam) m' delta' in
	   SFc (sigma1, sigma2)
	 )
     )
  | MApp (m1, m2), DApp (delta1, delta2) ->
     let sigma1 = find_type gam m2 delta2 in (
       match find_type gam m1 delta1 with
       | SFc (sigma', sigma2) when sigma' = sigma1 -> sigma2
       | _ -> failwith "wrong entry"
     )
  | _ -> failwith "wrong entry"

let main_tr lbm lbd =
  let m = Parser_m.m Lexer_m.read lbm
  and d = Parser_delta.d Lexer_delta.read lbd in
  let sigma = find_type [] m d in
  print_string ("\nHere is the type of the lambda term you gave:\n" ^ (sigma_to_string sigma) ^ "\n\n")
