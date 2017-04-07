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
open Printer

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
  | (id::l',DefAxiom t::s') ->
     begin
       print_endline (string_of_axiom id t id_list);
       print_all l' s';
     end
  | (id::l',DefLet (t1,t2,t3)::s') ->
     begin
       print_endline (string_of_let id (t1,t2,t3) id_list);
       print_all l' s';
     end
  | _ -> assert false

let addaxiom id l t id_list sigma verbose = prerr_endline "TODO"; (id_list, sigma)

let proof id l t id_list sigma verbose =
  prerr_endline "Error: proof system not implemented.\n"; (id_list, sigma)

let addlet id l t o id_list sigma verbose = prerr_endline "TODO"; (id_list, sigma)

let normalize id id_list sigma = prerr_endline "TODO"

(* repl *)

let rec repl lx id_list sigma verbose =
  let rec loop (id_list,sigma) =
    begin
      try
	Lexing.flush_input lx;
	if verbose then (print_string prompt; flush stdout) else ();
	let str = Sentence.get lx in
	match Parser.s Lexer.read (Lexing.from_string str) with
	| Quit -> (id_list, sigma)
	| Load id -> loop (repl (Lexing.from_channel (open_in id)) id_list sigma false)
	| Proof (id, l, t) -> loop (proof id l t id_list sigma verbose)
	| Axiom (id, l, t) -> loop (addaxiom id l t id_list sigma verbose)
	| Definition (id, l, t, o)
	  -> loop (addlet id l t o id_list sigma verbose)
	| Print id -> print id id_list sigma; loop (id_list, sigma)
	| Print_all -> print_all id_list sigma; loop (id_list, sigma)
	| Compute id -> normalize id id_list sigma;
			loop (id_list, sigma)
	| Help -> help (); loop (id_list, sigma)
	| Error -> prerr_endline syntaxerror;
		   loop (id_list, sigma)
      with
      | Failure a -> prerr_endline (failure a);
		     loop (id_list, sigma)
      | Sys_error a -> prerr_endline (syserror a);
		       loop (id_list, sigma)
      | _ -> prerr_endline unknownerror;
	     loop (id_list, sigma)
    end
  in loop (id_list, sigma)

(* main *)

let () =
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
    ignore (repl lx id_list sigma true)
  end
