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
  | (id::l',DefAxiom (t1,t2)::s') ->
     begin
       print_all l' s';
       print_endline (string_of_axiom id t1 t2 l');
     end
  | (id::l',DefLet (t1,t2,t3,t4)::s') ->
     begin
       print_all l' s';
       print_endline (string_of_let id (t1,t2,t3,t4) l');
     end
  | _ -> assert false

let proof id str l t id_list sigma verbose =
  prerr_endline "Error: proof system not implemented.\n"; (id_list, sigma)


let add_axiom id str l t id_list sigma verbose =
  match find id id_list with
  | Some n -> prerr_endline (error_declared id); (id_list, sigma)
  | None -> let t = (fix_index id_list t) in
	    match check_axiom str id_list sigma l t with
	    | Result.Ok (t') ->
	       begin
		 if verbose then
		   print_endline (axiom_message id)
		 else ();
		 (id :: id_list, DefAxiom (t,t') :: sigma)
	       end
	    | Result.Error (reason) ->
		 prerr_endline reason; (id_list, sigma)

let add_let id str l d o id_list sigma verbose =
  match find id id_list with
  | Some n -> prerr_endline (error_declared id); (id_list, sigma)
  | None -> let d = (fix_index id_list d) in
	    match reconstruction str id_list sigma l d with
	    | Result.Error (reason) ->
	       prerr_endline reason; (id_list, sigma)
	    | Result.Ok (t, e, et) ->
	       match o with
	       | None ->
		  begin
		    if verbose then
		      print_endline (let_message id)
		    else ();
		    (id :: id_list, DefLet (d,t,e,et) :: sigma)
		  end
	       | Some (l', t') ->
		  match reconstruction str id_list sigma
				       l' (fix_index id_list t') with
		  | Result.Error (reason) ->
		     prerr_endline reason; (id_list, sigma)
		  | Result.Ok (_,et',_)
		    -> if is_equal sigma et et'
		       then
			 begin
			   if verbose then
			     print_endline (let_message id)
			   else ();
			   (id :: id_list, DefLet(d,t',e,et')::sigma)
			 end
		       else
			 begin
			   prerr_endline (let_error t t' id_list);
			   (id_list, sigma)
			 end

let normalize id id_list sigma =
  match find id id_list with
  | None -> prerr_endline (error_not_declared id)
  | Some n -> let (d, t, e, et) = get_from_context sigma n in
	      let d = strongly_normalize sigma d in
	      let t = strongly_normalize sigma t in
	      let e = strongly_normalize sigma e in
	      let et = strongly_normalize sigma et in
	      print_endline (pretty_print_let (d,t,e,et) id_list)

(* repl *)

let rec repl lx id_list sigma verbose =
  let rec loop (id_list,sigma) =
    begin
      try
	if verbose then (Lexing.flush_input lx; print_string prompt; flush stdout) else ();
	let buf = Buffer.create 80 in
	let rule = Parser.s (Lexer.read buf) lx in
	let str = Buffer.contents buf in
	match rule with
	| Quit -> (id_list, sigma)
	| Load id -> loop (let lx = Lexing.from_channel (open_in id)
			   in
			   begin
			     lx.lex_curr_p <- {lx.lex_curr_p with Lexing.pos_fname = id};
			     repl lx id_list sigma false
			   end
			  )
	| Proof (id, l, t) -> loop (proof id str l t id_list sigma verbose)
	| Axiom (id, l, t) -> loop (add_axiom id str l t id_list sigma verbose)
	| Definition (id, l, t, o)
	  -> loop (add_let id str l t o id_list sigma verbose)
	| Print id -> print id id_list sigma; loop (id_list, sigma)
	| Print_all -> print_all id_list sigma; loop (id_list, sigma)
	| Compute id -> normalize id id_list sigma;
			loop (id_list, sigma)
	| Help -> help (); loop (id_list, sigma)
	| Error -> prerr_endline (syntaxerror str lx);
		   Lexing.flush_input lx;
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
