open Definitions
open String

let is_var_k s =
	let l = length s in
	if get s 0 <> 'x'
		then failwith "false"
		else
			try
			(int_of_string (sub s 1 (l-1)))
			with _ -> failwith "false"
				

let rec trouve_max kmax =
	function
	| MVar _ -> kmax
	| MLambda (_, k, m) ->
		trouve_max (max kmax k) m
	| MApp (m, n) ->
		max (trouve_max kmax m) (trouve_max kmax n)

let rec decale k liste =
	function
	| MVar x ->
		(
		try (
			let i = is_var_k x in
			if List.exists (fun j -> i = j) liste
				then MVar (var (k+i))
				else MVar x
			)
		with Failure "false" ->
			MVar x
		)
	| MLambda (x, i, m) ->
		(
		try (
			let j = is_var_k x in
			let y = var (k+j) in
			MLambda (y, i+k, decale k (j::liste) m)
			)
		with Failure "false" ->
			MLambda (x, i, decale k liste m)
		)
	| MApp (m, n) -> MApp (decale k liste m, decale k liste n)

let rec remplace m x y =
	match m with
		| MVar z -> MVar (if z = x then y else x)
		| MLambda (z, i, n) -> MLambda ((if z = x then y else x), i, remplace n x y)
		| MApp (p, q) -> MApp (remplace p x y, remplace q x y)

let rec est_present x sigma =
	match sigma with
		| [] -> false
		| (y, _) :: _ when x = y -> true
		| _ :: l -> est_present x l

let rec reduit_cbv (sigma : (string * value) list) m : value =
	match m with
		| MVar x ->
			(
			try (List.assoc x sigma)
			with Not_found -> M (MVar x, sigma)
			)
		| MLambda (x, i, n) ->
			M (MLambda (x, i, n), sigma)
		| MApp (p, q) ->
			let k = trouve_max 0 p in
			let q_bis = decale k [] q in
			let rpb = reduit_cbv sigma p in
			match rpb with
				| M (MLambda (x, i, n), sigma') ->
					let rq = reduit_cbv sigma q_bis in
					if est_present x sigma'
						then
							let y = var (k+1) in
							let n_bis = remplace n x y in
							reduit_cbv ((y, rq) :: sigma') n_bis
						else reduit_cbv ((x, rq) :: sigma') n
				| M (MVar x, sigma') ->
					let rq = reduit_cbv sigma q in
					match rq with
						| M (r, s) -> M (MApp (MVar x, r), sigma)
						
let rec reduit_cbn (sigma : (string * value) list) m : value =
	match m with
		| MVar x ->
			(
			try (List.assoc x sigma)
			with Not_found -> M (MVar x, sigma)
			)
		| MLambda (x, i, n) ->
			M (MLambda (x, i, n), sigma)
		| MApp (p, q) ->
			let k = trouve_max 0 p in
			let q_bis = decale k [] q in
			let rpb = reduit_cbn sigma p in
			match rpb with
				| M (MLambda (x, i, n), sigma') ->
					if est_present x sigma
						then
							let y = var (k+1) in
							let n_bis = remplace n x y in
							reduit_cbn ((x, M (q_bis, sigma)) :: sigma') n
						
				| M (MVar x, sigma') ->
					M (MApp (MVar x, q_bis), sigma)

let rec reduit_s (sigma : (string * value) list) m : value =
	match m with
		| MVar x ->
			(
			try (List.assoc x sigma)
			with Not_found -> M (MVar x, sigma)
			)
		| MLambda (x, i, n) ->
		(
			match reduit_s sigma n
			with M (p, s) -> M (MLambda (x, i, p), sigma)
		)
		| MApp (p, q) ->
			let k = trouve_max 0 p in
			let q_bis = decale k [] q in
			let rpb = reduit_s sigma p in
			match rpb with
				| M (MLambda (x, i, n), sigma') ->
					let rq = reduit_s sigma q_bis in
					reduit_s ((x, rq) :: sigma') n
				| M (MVar x, sigma') ->
					let rq = reduit_s sigma q in
					match rq with
						| M (r, s) -> M (MApp (MVar x, r), sigma)
