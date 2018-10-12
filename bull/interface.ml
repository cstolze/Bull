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

let print id id_list sigma =
  match find id id_list with
  | None -> prerr_endline (error_not_declared id)
  | Some n -> print_endline (pretty_print_let (get_from_context sigma n) id_list)

let rec print_all id_list sigma =
  match (id_list, sigma) with
  | ([],[]) -> ()
  | (id::l',DefAxiom (_,t)::s') ->
     begin
       print_all l' s';
       print_endline (string_of_axiom id t.delta t.essence l');
     end
  | (id::l',DefLet (_,t1,t2)::s') ->
     begin
       print_all l' s';
       print_endline (string_of_let id (t1,t2) l');
     end
  | _ -> assert false

let proof id str t id_list sigma verbose =
  prerr_endline "Error: proof system not implemented.\n"; (id_list, sigma)


let add_axiom id str t id_list sigma verbose =
  match find id id_list with
  | Some n -> prerr_endline (error_declared id); (id_list, sigma)
  | None -> let t = (fix_index id_list t) in
            try
	      let (m,t,t') = force_type (0,[]) sigma [] t in
	      begin
		if verbose then
		  print_endline (axiom_message id)
		else ();
		(id :: id_list, DefAxiom (id,t) :: sigma)
	      end
            with
              Err (reason) ->
              begin
	        prerr_endline reason; (id_list, sigma)
              end

let add_let id str d o id_list sigma verbose =
  match find id id_list with
  | Some n -> prerr_endline (error_declared id); (id_list, sigma)
  | None -> let d = (fix_index id_list d) in
	    try
              let (m, t1, t2) = reconstruct_with_type (0,[]) sigma [] d o in
	      if verbose then
		print_endline (let_message id)
	      else ();
	      (id :: id_list, DefLet (id, t1, t2) :: sigma)
            with
              Err reason -> prerr_endline reason; (id_list, sigma)

let normalize id id_list sigma =
  match find id id_list with
  | None -> prerr_endline (error_not_declared id)
  | Some n -> let (t1, t2) = get_from_context sigma n in
	      let t1 = strongly_normalize_full sigma t1 in
	      let t2 = strongly_normalize_full sigma t2 in
	      print_endline (pretty_print_let (t1,t2) id_list)

(* repl *)

exception Exc_quit

let rec repl lx id_list sigma verbose =
  let rec loop (id_list,sigma) =
    begin
      try
	if verbose then (Lexing.flush_input lx; print_string prompt; flush stdout) else ();
	let buf = Buffer.create 80 in
	let rule = Parser.s (Lexer.read buf) lx in
	let str = Buffer.contents buf in
        let foo (id_list, sigma) rule =
          match rule with
	  | Quit -> raise Exc_quit
	  | Load id -> let lx = Lexing.from_channel (open_in id)
		       in
		       begin
		         lx.lex_curr_p <- {lx.lex_curr_p with Lexing.pos_fname = id};
		         repl lx id_list sigma false
		       end
	  | Proof (id, t) -> proof id str t id_list sigma verbose
	  | Axiom (id, t) -> add_axiom id str t id_list sigma verbose
	  | Definition (id, t, o)
	    -> add_let id str t o id_list sigma verbose
	  | Print id -> print id id_list sigma; (id_list, sigma)
	  | Print_all -> print_all id_list sigma; (id_list, sigma)
	  | Compute id -> normalize id id_list sigma; (id_list, sigma)
	  | Help -> help (); (id_list, sigma)
	  | Error -> prerr_endline (syntaxerror str lx);
		     Lexing.flush_input lx; (id_list, sigma)
        in
        loop (List.fold_left foo (id_list, sigma) rule)
      with
      | Failure a -> prerr_endline (failure a);
		     loop (id_list, sigma)
      | Sys_error a -> prerr_endline (syserror a);
		       loop (id_list, sigma)
      | Exc_quit -> (id_list, sigma)
      | e -> prerr_endline (Printexc.to_string e);
	     loop (id_list, sigma)
    end
  in loop (id_list, sigma)

(* main *)

let main () =
  let lx = Lexing.from_channel stdin
  in
  begin
    Arg.parse options arg_file usage;
    print_endline welcome_message;
    let (id_list, sigma) =
      if (!initfile) = "" then
	([],[])
      else
	try
	  repl (Lexing.from_channel (open_in !initfile)) [] [] false
	with
	| Sys_error a -> prerr_endline (syserror a); ([],[])
    in
    repl lx id_list sigma true
  end
