let main () =
	print_string "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n";
	print_string "\t\t\t\t\t$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n";
	print_string "\t\t\t\t\t$$$$\t\t\t\t\t\t$$$$\n";
	print_string "\t\t\t\t\t$$$$\t\t\tWELCOME\t\t\t$$$$\n";
	print_string "\t\t\t\t\t$$$$\t\t\t\t\t\t$$$$\n";
	print_string "\t\t\t\t\t$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n\n\n\n\n";
	let rec boucle () =
		print_string "\t\t\t\t\t\t$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n";
		print_string "\t\t\t\t\t\t$$$\t\t\t      $$$\n";
		print_string "\t\t\t\t\t\t$$$  what do you want to do?  $$$\n\t\t\t\t\t\t$$$\t\t\t      $$$\n";
		print_string "\t\t\t\t\t\t$$$   - type reconstruction   $$$\n\t\t\t\t\t\t$$$\t\t\t      $$$\n";
		print_string "\t\t\t\t\t\t$$$   - type inhabitation     $$$\n\t\t\t\t\t\t$$$\t\t\t      $$$\n";
		print_string "\t\t\t\t\t\t$$$   - proof reconstruction  $$$\n\t\t\t\t\t\t$$$\t\t\t      $$$\n";
		print_string "\t\t\t\t\t\t$$$   q to quit\t\t      $$$\n\t\t\t\t\t\t$$$\t\t\t      $$$\n";
		print_string "\t\t\t\t\t\t$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n";
		let l = read_line () in
		match l with
			| "type reconstruction" ->
				let rec boucle1 () =
					begin
						print_string "\nenter the lambda term you want to consider, it has to be close.\nOr enter 'cancel' to come back to menu\n\n";
						let lm = read_line () in
						if lm = "cancel"
							then begin print_string "\n"; failwith "cancel" end
							else
								begin
									print_string "\nenter the delta proof you want to consider, it has to be close.\nOr enter 'cancel' to come back to menu\n\n";
									let ld = read_line () in
									if ld = "cancel"
										then begin print_string "\n"; failwith "cancel" end
										else
											(
											try (Type_reconstruction.main_tr (Lexing.from_string lm) (Lexing.from_string ld))
											with _ -> 
												begin
													print_string "\nyou typed something wrong\n";
													boucle1()
												end
											)
								end
					end
				in
				begin
					(
					try (boucle1 ())
					with Failure "cancel" -> ()
					);
					boucle ()
				end
			| "type inhabitation" ->
				let rec boucle2 () =
					begin
						print_string "\nenter the delta proof you want to consider, it has to be close.\nOr enter 'cancel' to come back to menu\n\n";
						let ld = read_line () in
						if ld = "cancel"
							then begin print_string "\n"; failwith "cancel" end
							else
								(
								try (Type_inhabitation.main_ti (Lexing.from_string ld))
								with _ ->
									begin
										print_string "\nyou typed something wrong\n";
										boucle2 ()
									end
								)
					end
				in
				begin
					(
					try (boucle2 ())
					with Failure "cancel" -> ()
					);
					boucle ()
				end
			| "proof reconstruction" ->
				let rec boucle3 ()=
					begin
						print_string "\nenter the lambda_term you want to consider, it has to be close.\nOr enter 'cancel' to come back to menu\n\n";
						let lm = read_line () in
						if lm = "cancel" 
							then begin print_string "\n"; failwith "cancel" end
							else
								begin
									print_string "\nenter its type\n\n";
									let ls = read_line () in
									if ls = "cancel"
										then begin print_string "\n"; failwith "cancel" end
										else
											(
											try (Proof_reconstruction.main_pr (Lexing.from_string lm) (Lexing.from_string ls));
											with _ ->
												begin
													print_string "\nyou typed something wrong\n";
													boucle3 ()
												end
											)
								end
					end
				in
				begin
					(
					try (boucle3 ())
					with Failure "cancel" -> ()
					);
					boucle ()
				end
			| "q" ->
				begin
					print_string "\n\n\t\t\t\t\t\t\t$$$$$$$$$$$$$$$$\n";
					print_string "\t\t\t\t\t\t\t$$$          $$$\n";
					print_string "\t\t\t\t\t\t\t$$$ SEE YOU! $$$\n";
					print_string "\t\t\t\t\t\t\t$$$          $$$\n";
					print_string "\t\t\t\t\t\t\t$$$$$$$$$$$$$$$$\n\n\n\n\n\n\n\n\n\n"
				end
			| _ ->
				begin
					print_string "\nwhat you typed is understandable..\n\n";
					boucle ()
				end
	in boucle ();;

main ()
