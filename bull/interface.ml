(*
    Bull, a theorem prover based on intersection types and Curry-Howard isomorphism.
    Copyright (C) 2016 Claude Stolze, ENS Rennes, UPMC, INRIA

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

open Utils
open Parser
open Lexer
open Bruijn
open Reduction
open Reconstruction
open Printer
open Lexing

(* cli arguments *)

let initfile = ref ""
let arg_file arg = initfile := arg

let version () = print_endline version_text; exit 0
let options = (version_option, Arg.Unit (version), version_doc) :: []

(* commands *)

let help () = print_endline help_text

let print id id_list sigma esigma =
  match find id sigma with
  | None -> prerr_endline (error_not_declared id)
  | Some n -> let t1, t2 = get_from_context sigma n in
              let t3, t4 = get_from_context esigma n in
     print_endline (pretty_print_let (t1,t2,t3,t4) id_list)

let rec print_all id_list sigma esigma =
  match (id_list, sigma, esigma) with
  | ([],[],[]) -> ()
  | (_::ll,DefAxiom(id,t1)::l',DefAxiom (_,t2)::s') ->
     begin
       print_all ll l' s';
       print_endline (string_of_axiom id t1 t2 ll);
     end
  | (_::ll, DefLet(id,t1,t2)::l', DefLet (_,t3,t4)::s') ->
     begin
       print_all ll l' s';
       print_endline (string_of_let id (t1,t2,t3,t4) ll);
     end
  | _ -> assert false

let proof id str t id_list sigma esigma verbose =
  prerr_endline "Error: proof system not implemented.\n"; (id_list, sigma, esigma)

let add_axiom id str t id_list sigma esigma verbose =
  match find id sigma with
  | Some n -> prerr_endline (error_declared id); (id_list, sigma, esigma)
  | None -> let t = (fix_index id_list t) in
            try
	      let (m,em,t,et) = check_axiom str id_list sigma t in
	      begin
		if verbose then
		  print_endline (axiom_message id)
		else ();
		(id :: id_list, DefAxiom (id,t) :: sigma, DefAxiom(id,et) :: esigma)
	      end
            with
              Err (reason) ->
              begin
	        prerr_endline reason; (id_list, sigma, esigma)
              end

let add_let id str d o id_list sigma esigma verbose =
  match find id sigma with
  | Some n -> prerr_endline (error_declared id); (id_list, sigma, esigma)
  | None -> let d = (fix_index id_list d) in
            let t2 =
              match o with
              | Underscore _ -> None
              | _ -> Some o
            in
	    try
              let (m, em, t1, t2, et1, et2) =
                check_term str id_list sigma d t2 in
	      if verbose then
		print_endline (let_message id)
	      else ();
	      (id :: id_list, DefLet (id, t1, t2) :: sigma, DefLet (id, et1, et2) :: esigma)
            with
              Err reason -> prerr_endline reason; (id_list, sigma, esigma)

let normalize id id_list sigma esigma =
  match find id sigma with
  | None -> prerr_endline (error_not_declared id)
  | Some n -> let (t1, t2) = get_from_context sigma n in
              let (t3, t4) = get_from_context esigma n in
	      let t1 = strongly_normalize sigma t1 in
	      let t2 = strongly_normalize sigma t2 in
	      let t3 = strongly_normalize esigma t3 in
	      let t4 = strongly_normalize esigma t4 in
	      print_endline (pretty_print_let (t1,t2,t3,t4) id_list)

(* repl *)

exception Exc_quit

let rec repl lx id_list sigma esigma verbose =
  let rec loop (id_list, sigma, esigma) =
    begin
      try
	if verbose then (Lexing.flush_input lx; print_string prompt; flush stdout) else ();
	let buf = Buffer.create 80 in
	let rule = Parser.s (Lexer.read buf) lx in
	let str = Buffer.contents buf in
        let foo (id_list, sigma, esigma) rule =
          match rule with
	  | Quit -> raise Exc_quit
	  | Load id -> let lx = Lexing.from_channel (open_in id)
		       in
		       begin
		         lx.lex_curr_p <- {lx.lex_curr_p with Lexing.pos_fname = id};
		         repl lx id_list sigma esigma false
		       end
	  | Proof (id, t) -> proof id str t id_list sigma esigma verbose
	  | Axiom (id, t) -> add_axiom id str t id_list sigma esigma verbose
	  | Definition (id, t, o)
	    -> add_let id str t o id_list sigma esigma verbose
	  | Print id -> print id id_list sigma esigma; (id_list, sigma, esigma)
	  | Print_all -> print_all id_list sigma esigma; (id_list, sigma, esigma)
	  | Compute id -> normalize id id_list sigma esigma; (id_list, sigma, esigma)
	  | Help -> help (); (id_list, sigma, esigma)
	  | Error -> prerr_endline (syntaxerror str lx);
		     Lexing.flush_input lx; (id_list, sigma, esigma)
        in
        loop (List.fold_left foo (id_list, sigma, esigma) rule)
      with
      | Failure a -> prerr_endline (failure a);
		     loop (id_list, sigma, esigma)
      | Sys_error a -> prerr_endline (syserror a);
		       loop (id_list, sigma, esigma)
      | Exc_quit -> (id_list, sigma, esigma)
      | e -> prerr_endline (Printexc.to_string e);
	     loop (id_list, sigma, esigma)
    end
  in loop (id_list, sigma, esigma)

(* main *)

let main () =
  let lx = Lexing.from_channel stdin
  in
  begin
    Arg.parse options arg_file usage;
    print_endline welcome_message;
    let (id_list, sigma, esigma) =
      if (!initfile) = "" then
	([],[],[])
      else
	try
	  repl (Lexing.from_channel (open_in !initfile)) [] [] [] false
	with
	| Sys_error a -> prerr_endline (syserror a); ([],[],[])
    in
    repl lx id_list sigma esigma true
  end
