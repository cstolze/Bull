open Definitions

let rec reconstruit_delta arbuste =
	match arbuste with
	| AMark i -> DMark i
	| AFcI (t, a) ->
		(
		match (t.m, t.s) with
			| (MLambda (_, i, _), SFc (s1, s2)) ->
				DLambda (i, s1, reconstruit_delta a)
			| _ -> failwith "wrong tree"
		)
	| AFcE (_, a1, a2) ->
		DApp (reconstruit_delta a1, reconstruit_delta a2)
	| AEtI (_, a1, a2) ->
		DEt (reconstruit_delta a1, reconstruit_delta a2)
	| AEtEL (_, a) ->
		DGc (reconstruit_delta a)
	| AEtER (_, a) ->
		DDt (reconstruit_delta a)
	| ARien -> failwith "comment veux-tu reconstuire un arbuste non rempli ?"

let remplace arbuste feuille =
	let rec regarde (arbuste : arbuste) =
		match arbuste with
			| ARien -> feuille
			| AMark _ -> failwith "rempli"
			| AFcI (t, a) -> AFcI (t, regarde a)
			| AFcE (t, a1, a2) ->
				(
					try (
						let a1' = regarde a1 in
						AFcE (t, a1', a2)
					)
					with Failure "rempli" ->
						let a2' = regarde a2 in
						AFcE (t, a1, a2')
				)
			| AEtI (t, a1, a2) ->
				(
					try (
						let a1' = regarde a1 in
						AEtI (t, a1', a2)
					)
					with Failure "rempli" ->
						let a2' = regarde a2 in
						AEtI (t, a1, a2')
				)
			| AEtEL (t, a) -> AEtEL (t, regarde a)
			| AEtER (t, a) -> AEtER (t, regarde a)	
	in regarde arbuste

let copie_pb pb =
	let pb' = {
		prems = Rien;
		deuz = [];
		arbuste = ARien
		}
	in
	pb'.prems <- pb.prems;
	pb'.deuz <- pb.deuz;
	pb'.arbuste <- pb.arbuste;
	pb'
	

let decale pb =
	match pb.deuz with
		| [] ->
			begin
				pb.prems <- Rien;
				pb.deuz <- []
			end
		| t :: l ->
			begin
				pb.prems <- Qqch t;
				pb.deuz <- l
			end
			
let choisit_var pb =
	(
		match pb.prems with
			| Qqch t ->
				(
				match t.m with
					| MVar x ->
						let i = trouve_i x t.s t.g in
						pb.arbuste <- remplace pb.arbuste (AMark i);
						
					| _ -> failwith "var"
				)
			| _ -> failwith "var"
	);
	decale pb

let choisit_fci pb =
	match pb.prems with
		| Qqch t ->
			(
			match t.m, t.s with
				| MLambda (x, i, m), SFc (s1, s2) ->
					begin
						pb.arbuste <- remplace pb.arbuste (AFcI (t, ARien));
						pb.prems <- Qqch {g = (x, i, s1)::t.g; m = m; s = s2}
					end
				| _ -> failwith "fci"
			)
		| _ -> failwith "fci"

let choisit_fce pb a =
	match pb.prems with
		| Qqch t ->
			(
			match t.m with
				| MApp (m1, m2) ->
					begin
						pb.arbuste <- remplace pb.arbuste (AFcE (t, ARien, ARien));
						pb.prems <- Qqch {g = t.g; m = m1; s = SFc (a, t.s)};
						pb.deuz <- {g = t.g; m = m2; s = a} :: pb.deuz
					end
				| _ -> failwith "fce"
			)
		| _ -> failwith "fce"

let choisit_eti pb =
	match pb.prems with
		| Qqch t ->
			(
			match t.s with
				| SEt (s1, s2) ->
					begin
						pb.arbuste <- remplace pb.arbuste (AEtI (t, ARien, ARien));
						pb.prems <- Qqch {g = t.g; m = t.m; s = s1};
						pb.deuz <- {g = t.g; m = t.m; s = s2} :: pb.deuz
					end
				| _ -> failwith "eti"
			)
		| _ -> failwith "eti"

let choisit_etel pb a =
	match pb.prems with
		| Qqch t ->
			begin
				pb.arbuste <- remplace pb.arbuste (AEtEL (t, ARien));
				pb.prems <- Qqch {g = t.g; m = t.m; s = SEt (t.s, a)}
			end
		| _ -> failwith "etel"

let choisit_eter pb a =
	match pb.prems with
		| Qqch t ->
			begin
				pb.arbuste <- remplace pb.arbuste (AEtER (t, ARien));
				pb.prems <- Qqch {g = t.g; m = t.m; s = SEt (a, t.s)}
			end
		| _ -> failwith "eter"

let possibilites (t : trip) bol =
	let regarde_fci l =
		match t.m, t.s with
			| MLambda _, SFc _ -> "->I" :: l
			| _ -> l
	and regarde_fce l =
		match t.m with
			| MApp _ -> "->E" :: l
			| _ -> l
	and regarde_var l =
		match t.m with
			| MVar x ->
			(
				try (
				let _ = trouve_i x t.s t.g in
				"var" :: l
				)
				with Failure "vide wtf?" -> l
			)
			| _ -> l
	and regarde_eti l =
		match t.s with
			| SEt _ -> "&I" :: l
			| _ -> l
	in regarde_fci (regarde_fce (regarde_var (regarde_eti ("&El" :: "&Er" :: (if bol then ["backtrack"] else [])))))

let choisit pb bol =
	let rec aux =
		function
		| [] -> print_string "\n\n"
		| op :: l ->
			begin
				print_string op;
				if l = [] then () else print_string " ; ";
				aux l
			end
	in
	let rec choisit_type () =
		print_string "\ntape the intermediate type you want, or 'cancel' to come back to rules\n\n";
		let l = read_line () in
		match l with
			| "cancel" -> failwith "annul"
			| _ -> 
				try (
					let lb = Lexing.from_string l in
					Parser_sigma.s Lexer_sigma.lecture lb
				)
				with _ ->
					begin
						print_string "\nwhat you taped is understandable...\n\n";
						choisit_type ()
					end
	and boucle () =
	(
		match pb.prems with
			| Rien -> failwith "pas normal"
			| Qqch t ->
				(
					print_string "\n";
					print_pb pb;
					print_string "choose your rule :\n\n";
					let lp = possibilites t bol in
					aux lp;
					let opt = read_line () in
					if List.exists (fun o -> opt = o) lp
					then
						match opt with
							| "->I" -> OFcI
							| "var" -> OVar
							| "backtrack" -> OBacktrack
							| "&I" -> OEtI
							| "->E" ->
								(
								try OFcE (choisit_type ())
								with Failure "annul" -> boucle ()
								)
							| "&El" ->
								(
								try OEtEL (choisit_type ())
								with Failure "annul" -> boucle ()
								)
							| "&Er" ->
								(
								try OEtER (choisit_type ())
								with Failure "annul" -> boucle ()
								)
							| _ -> failwith "n'arrive jamais"
					else
						begin
							print_string "\nyou cannot take this option yet, or you taped something wrong\n\n";
							boucle ()
						end
				)
	)
	in
	boucle ()

let rec algorithme pb_tot =
	match pb_tot with
		| [] -> failwith "ne devrait pas arriver"
		| pb :: lsuiv ->
			match pb.prems with
				| Rien ->
					print_string ("\nyou succeded, here is the delta you were searching for:\n"^(delta_to_string (reconstruit_delta pb.arbuste))^ "\n\n")
				| _	 ->
					let pb' = copie_pb pb in
					let opt = choisit pb' (if lsuiv = [] then false else true) in
					match opt with
						| OFcI ->
							begin
								choisit_fci pb';
								algorithme (pb' :: pb_tot)
							end
						| OFcE a ->
							begin
								choisit_fce pb' a;
								algorithme (pb' :: pb_tot)
							end
						| OEtI ->
							begin
								choisit_eti pb';
								algorithme (pb' :: pb_tot)
							end
						| OEtEL a ->
							begin
								choisit_etel pb' a;
								algorithme (pb' :: pb_tot)
							end
						| OEtER a ->
							begin
								choisit_eter pb' a;
								algorithme (pb' :: pb_tot)
							end
						| OVar ->
							begin
								choisit_var pb';
								algorithme (pb' :: pb_tot)
							end
						| OBacktrack -> algorithme lsuiv

let main_pr m lbs =
	let s = Parser_sigma.s Lexer_sigma.lecture lbs
	in
	let pb = {
		prems = Qqch {g = []; m = m; s = s};
		deuz =  [];
		arbuste = ARien
		}
	in algorithme [pb]
