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

let rec print_meta id_list sigma e_sigma (n,meta) =
  let rec list_2_string id_list ctx =
    match ctx with
    | [] -> "", id_list
    | [DefAxiom(id,t)] ->
       id ^ " : " ^ (string_of_term false id_list t) ^ ", ", id :: id_list
    | DefAxiom(id,t) :: ctx ->
       let s, id_list = list_2_string id_list ctx in
       s ^ id ^ " : " ^ (string_of_term false id_list t) ^ ", ", id :: id_list
    | _ -> failwith "TODO"
  in
  let rec print_evar id_list ctx n t =
    let s,id_list = list_2_string id_list ctx in
    print_string s;
    print_string ("|- ?" ^ (string_of_int n));
    print_string " : ";
    print_endline (string_of_term false id_list t)
  in (* TODO: factorize code *)
  let rec print_subst id_list ctx n t1 t2 =
    let s,id_list = list_2_string id_list ctx in
    print_string s;
    print_string ("|- ?" ^ (string_of_int n) ^ " := ");
    print_string (string_of_term false id_list t1);
    print_string " : ";
    print_endline (string_of_term false id_list t2)
  in
  match meta with
  | [] -> ()
  | IsSort m :: meta -> print_endline ("|- ?" ^ (string_of_int m) ^
                                         " is a sort");
                print_meta id_list sigma e_sigma (n,meta)
  | SubstSort (m,t) :: meta -> print_endline ("|- ?" ^ (string_of_int m) ^
                                                " := " ^ (string_of_term false id_list t));
                print_meta id_list sigma e_sigma (n,meta)
  | DefMeta(ctx,m,t) :: meta -> print_evar id_list ctx m t;
                                print_meta id_list sigma e_sigma (n,meta)
  | Subst(ctx,m,t1,t2) :: meta -> print_subst id_list ctx m t1 t2;
                                  print_meta id_list sigma e_sigma (n,meta)


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

let normalize d str id_list sigma esigma =
  let d = (fix_index id_list d) in
  try
    let (m, em, t1, t2, et1, et2) =
      check_term str id_list sigma d None
    in
    let t1 = strongly_normalize sigma t1 in
    let t2 = strongly_normalize sigma t2 in
    let t3 = strongly_normalize esigma et1 in
    let t4 = strongly_normalize esigma et2 in
    print_endline (pretty_print_let (t1,t2,t3,t4) id_list)
  with
    Err reason -> prerr_endline reason

(* repl *)

exception Exc_quit

let rec repl lx id_list sigma esigma verbose : (string list * Utils.declaration list * Utils.declaration list) *
         (int * Utils.metadeclaration list) =
  let rec loop ((id_list, sigma, esigma), meta) =
    begin
      try
	if verbose then (Lexing.flush_input lx; print_string prompt; flush stdout) else ();
	let buf = Buffer.create 80 in
	let rule = Parser.s (Lexer.read buf) lx in
	let str = Buffer.contents buf in
        let foo ((id_list, sigma, esigma), meta) rule =
          match rule with
	  | Quit -> raise Exc_quit
	  | Load id -> let lx = Lexing.from_channel (open_in id)
		       in
		       begin
		         lx.lex_curr_p <- {lx.lex_curr_p with Lexing.pos_fname = id};
		         repl lx id_list sigma esigma false
		       end
	  | Proof (id, t) -> (proof id str t id_list sigma esigma verbose, meta)
	  | Axiom (id, t) -> (add_axiom id str t id_list sigma esigma verbose, meta)
	  | Definition (id, t, o)
	    -> (add_let id str t o id_list sigma esigma verbose, meta)
	  | Print id -> print id id_list sigma esigma; ((id_list, sigma, esigma), meta)
	  | Print_all -> print_all id_list sigma esigma; ((id_list, sigma, esigma), meta)
          | Show -> print_meta id_list sigma esigma meta; ((id_list, sigma, esigma), meta)
          (* TODO : change for proofs *)
	  | Compute t -> normalize t str id_list sigma esigma; ((id_list, sigma, esigma), meta)
	  | Help -> help (); ((id_list, sigma, esigma), meta)
	  | Error -> prerr_endline (syntaxerror str lx);
		     Lexing.flush_input lx; ((id_list, sigma, esigma), meta)

          | Beginmeta -> ((id_list, sigma, esigma), (0,[]))
          | Endmeta -> ((id_list, sigma, esigma), (0,[]))
          | Unify (t1,t2) ->
             begin
               let (t1,t2) = (fix_index id_list t1, fix_index id_list t2) in
               ((id_list, sigma, esigma), Unification.unification meta sigma [] t1 t2)
             end
          | Add (l,t) ->
             begin
               let id_list_old = id_list in
               let rec tmp (id_list,ctx) =
                 function
                 | [] -> (id_list, ctx)
                 | (x,t) :: l ->
                    let id_list,ctx = x :: id_list, DefAxiom(x,fix_index id_list t) :: ctx in
                    tmp (id_list,ctx) l
               in
               let (id_list, l) = tmp (id_list,[]) l in
               let t = fix_index id_list t in
               let (meta, _) = Unification.meta_add meta l t dummy_loc in
               ((id_list_old, sigma, esigma), meta)
             end
          | UAxiom (id,t)->
             begin
               match find id sigma with
               | Some n -> prerr_endline (error_declared id); ((id_list, sigma, esigma),meta)
               | None -> let t = (fix_index id_list t) in
                         ((id :: id_list, DefAxiom(id,t) :: sigma, DefAxiom(id,t) :: esigma), meta)
             end
          | UDefinition (id,t1,t2) ->
             begin
               match find id sigma with
               | Some n -> prerr_endline (error_declared id); ((id_list, sigma, esigma),meta)
               | None -> let (t1,t2) = (fix_index id_list t1, fix_index id_list t2) in
                         ((id :: id_list, DefLet(id,t1,t2) :: sigma, DefLet(id,t1,t2) :: esigma), meta)
             end
        in
        (* TODO: better error management,
           e.g. what if a type-checking error cancels only
         one axiom when we declared several ones. *)
        loop (List.fold_left foo ((id_list, sigma, esigma),meta) rule)
      with
      | Failure a -> prerr_endline (failure a);
		     loop ((id_list, sigma, esigma), meta)
      | Sys_error a -> prerr_endline (syserror a);
		       loop ((id_list, sigma, esigma), meta)
      | Exc_quit -> ((id_list, sigma, esigma), meta)
      | e -> prerr_endline (Printexc.to_string e);
	     loop ((id_list, sigma, esigma), meta)
    end
  in loop ((id_list, sigma, esigma), (0,[]))

(* main *)

let main () =
  let lx = Lexing.from_channel stdin
  in
  begin
    Arg.parse options arg_file usage;
    print_endline welcome_message;
    let ((id_list, sigma, esigma), meta) =
      if (!initfile) = "" then
	(([],[],[]), (0,[]))
      else
	try
	  repl (Lexing.from_channel (open_in !initfile)) [] [] [] false
	with
	| Sys_error a -> prerr_endline (syserror a); (([],[],[]), (0,[]))
    in
    repl lx id_list sigma esigma true
  end
