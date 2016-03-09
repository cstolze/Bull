open Definitions

let rec find_sigma list_ =
	let rec associate x =
		function
		| [] -> failwith "there's a free variable"
		| (x', s) :: _ when x' = x -> s
		| _ :: l -> associate x l
	in
	function
	| DMark i -> associate i list_
	| DApp (delta1, delta2) ->
		(
		match find_sigma list_ delta1 with
			| SFc (sigma, sigma') when find_sigma list_ delta2 = sigma -> sigma'
			| _ -> failwith "no sigma"
		)
	| DAnd (delta1, delta2) ->
		SAnd (find_sigma list_ delta1, find_sigma list_ delta2)
	| DLeft delta ->
		(
		match find_sigma list_ delta with
			| SAnd (sigma1, sigma2) -> sigma1
			| _ -> failwith "no sigma"
		)
	| DRight delta ->
		(
		match find_sigma list_ delta with
			| SAnd (sigma1, sigma2) -> sigma2
			| _ -> failwith "no sigma"
		)
	| DLambda (i, sigma, delta) ->
		SFc (sigma, find_sigma ((i, sigma)::list_) delta)

let rec aux_find_m gam delta sigma p list_ : m =
	let f =
		function
		| 0 -> "x"
		| 1 -> "y"
		| 2 -> "z"
		| 3 -> "t"
		| p -> "x"^(string_of_int (p-4))
	in
	match delta with
		| DMark i ->
			MVar (find_x i sigma gam)
		| DApp (delta1, delta2) ->
			let m1 = aux_find_m gam delta1 (find_sigma list_ delta1) p list_
			and m2 = aux_find_m gam delta2 (find_sigma list_ delta2) p list_
			in
			MApp (m1, m2)
		| DLambda (i, sigma', delta') ->
			(
			match sigma with
				| SFc (sigma1, sigma2) when sigma1 = sigma' ->
					let x = f !p in
					let gam' = (x, i, sigma1) :: gam in
					p := !p +1;
					let m' = aux_find_m gam' delta' sigma2 p ((i, sigma1)::list_) in
					MLambda (x, i, m')
				| _ -> failwith "wrong entry"
			)
		| DAnd (delta1, delta2) ->
			(
			match sigma with
				| SAnd (sigma1, sigma2) ->
					let m = aux_find_m gam delta1 sigma1 p list_
					and m' = aux_find_m gam delta2 sigma2 p list_ in
					if alpha_conversion m m'
						then m else failwith "wrong entry"
				| _ -> failwith "wrong entry"
			)
		| DLeft delta' ->
			let sigma' = find_sigma list_ delta' in
			aux_find_m gam delta' sigma' p list_
		| DRight delta' ->
			let sigma' = find_sigma list_ delta' in
			aux_find_m gam delta' sigma' p list_

let find_m delta =
	let p = ref 0
	and sigma = find_sigma [] delta in
	aux_find_m [] delta sigma p [], sigma;;

let main_ti lbd =
	let d = Parser_delta.d Lexer_delta.read lbd
	in let m, sigma = find_m d in
	print_string ("\nHere is the lambda term you were looking for:\n" ^ (m_to_string m) ^ "\nIts type is:\n" ^
				(sigma_to_string sigma) ^ "\n\n")
