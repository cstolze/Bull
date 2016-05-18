open Lexer
open Definitions
(*open Reduction*)

let main fich =
	let flux = open_in fich in
	let lx = Lexing.from_channel flux in
	let ps = Parser.p Lexer.lecture lx in
	print_string "here is the lambda-term of your program:\n\n";
	print_string (m_to_string ps.m);
	print_string "\n\nenter the type of the program\n\n";
	let ln = read_line () in
	Proof_reconstruction.main_pr ps.m (Lexing.from_string ln);
	(*
	let rec boucle () =
		print_string "which reduction do you want?\n\n1 - call by name\n\n2 - call by value\n\n3 - strong reduction\n\n4 to quit\n\n";
		let i = read_int () in
			match i with
				| 4 -> ()
				| _ ->
					let m =
						match i with
							| 1 -> reduit_cbn [] ps.m
							| 2 -> reduit_cbv [] ps.m
							| 3 -> reduit_s [] ps.m
					in
					match m with
						| M (m', _) -> print_string ("\nhere is the result of your program:\n" ^ (m_to_string m') ^ "\n\n"); boucle ()
	in
	boucle ()
	*);;

main Sys.argv.(1)
