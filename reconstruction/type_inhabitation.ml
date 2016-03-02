open Definitions

let rec trouve_sigma liste =
	let rec associe x =
		function
		| [] -> failwith "wtf"
		| (x', s) :: _ when x' = x -> s
		| _ :: l -> associe x l
	in
	function
	| DMark i -> associe i liste
	| DApp (delta1, delta2) ->
		(
		match trouve_sigma liste delta1 with
			| SFc (sigma, sigma') when trouve_sigma liste delta2 = sigma -> sigma'
			| _ -> failwith "pas de bon sigma"
		)
	| DEt (delta1, delta2) ->
		SEt (trouve_sigma liste delta1, trouve_sigma liste delta2)
	| DGc delta ->
		(
		match trouve_sigma liste delta with
			| SEt (sigma1, sigma2) -> sigma1
			| _ -> failwith "pas de bon sigma"
		)
	| DDt delta ->
		(
		match trouve_sigma liste delta with
			| SEt (sigma1, sigma2) -> sigma2
			| _ -> failwith "pas de bon sigma"
		)
	| DLambda (i, sigma, delta) ->
		SFc (sigma, trouve_sigma ((i, sigma)::liste) delta)

let rec aux_trouve_m gam delta sigma p liste : m =
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
			MVar (trouve_x i sigma gam)
		| DApp (delta1, delta2) ->
			let m1 = aux_trouve_m gam delta1 (trouve_sigma liste delta1) p liste
			and m2 = aux_trouve_m gam delta2 (trouve_sigma liste delta2) p liste
			in
			MApp (m1, m2)
		| DLambda (i, sigma', delta') ->
			(
			match sigma with
				| SFc (sigma1, sigma2) when sigma1 = sigma' -> 
					let x = f !p in
					let gam' = (x, i, sigma1) :: gam in
					p := !p +1;
					let m' = aux_trouve_m gam' delta' sigma2 p ((i, sigma1)::liste) in
					MLambda (x, i, m')
				| _ -> failwith "wrong entry"
			)
		| DEt (delta1, delta2) ->
			(
			match sigma with
				| SEt (sigma1, sigma2) ->
					let m = aux_trouve_m gam delta1 sigma1 p liste
					and m' = aux_trouve_m gam delta2 sigma2 p liste in
					if alpha_conversion m m'
						then m else failwith "wrong entry"
				| _ -> failwith "wrong entry"
			)
		| DGc delta' ->
			let sigma' = trouve_sigma liste delta' in
			aux_trouve_m gam delta' sigma' p liste
		| DDt delta' ->
			let sigma' = trouve_sigma liste delta' in
			aux_trouve_m gam delta' sigma' p liste

let trouve_m delta =
	let p = ref 0
	and sigma = trouve_sigma [] delta in
	aux_trouve_m [] delta sigma p [], sigma;;

let main_ti lbd =
	let d = Parser_delta.d Lexer_delta.lecture lbd
	in let m, sigma = trouve_m d in
	print_string ("\nhere is the lambda term you were searching for:\n" ^ (m_to_string m) ^ "\nits type is:\n" ^
				(sigma_to_string sigma) ^ "\n\n") 
