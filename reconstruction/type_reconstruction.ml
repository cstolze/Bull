open Definitions

let rec trouve_type gam m delta : sigma =
	match m, delta with
		| _, DDt delta' -> (
			match trouve_type gam m delta' with
				| SEt (sigma1, sigma2) -> sigma2
				| _ -> failwith "wrong entry"
			)
		| _, DGc delta' -> (
			match trouve_type gam m delta' with
				| SEt (sigma1, sigma2) -> sigma1
				| _ -> failwith "wrong entry"
			)
		| _, DEt (delta1, delta2) ->
			let sigma1 = trouve_type gam m delta1
			and sigma2 = trouve_type gam m delta2 in
			SEt (sigma1, sigma2)
		| MVar x, _ -> trouve_sigma x gam
		| MLambda (x, i, m'), DLambda (j, sigma1, delta') when i = j ->
			(
			try (let _ = trouve_sigma x gam in failwith "wrong entry")
			with Failure "vide wtf?" ->
				(
				let sigma2 = trouve_type ((x, i, sigma1) :: gam) m' delta' in
				SFc (sigma1, sigma2)
				)
			)
		| MApp (m1, m2), DApp (delta1, delta2) ->
			let sigma1 = trouve_type gam m2 delta2 in (
			match trouve_type gam m1 delta1 with
				| SFc (sigma', sigma2) when sigma' = sigma1 -> sigma2
				| _ -> failwith "wrong entry"
			)
		| _ -> failwith "wrong entry"

let main_tr lbm lbd =
	let m = Parser_m.m Lexer_m.lecture lbm
	and d = Parser_delta.d Lexer_delta.lecture lbd in
	let sigma = trouve_type [] m d in
	print_string ("\nhere is the type of the lambda term you gave:\n" ^ (sigma_to_string sigma) ^ "\n\n")
