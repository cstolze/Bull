(*
    Bull, a theorem prover based on intersection types and Curry-Howard isomorphism.
    Copyright (C) 2019 Claude Stolze, INRIA, UCA

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
open Env
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

(* this function is for debugging purposes *)
let rec print_meta env (n,meta) =
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
                print_meta env (n,meta)
  | SubstSort (m,t) :: meta -> print_endline ("|- ?" ^ (string_of_int m) ^
                                                " := " ^ (string_of_term false [] t));
                print_meta env (n,meta)
  | DefMeta(ctx,m,t) :: meta -> print_evar [] ctx m t;
                                print_meta env (n,meta)
  | Subst(ctx,m,t1,t2) :: meta -> print_subst [] ctx m t1 t2;
                                  print_meta env (n,meta)

let print env id =
  if is_const_new env id then
    prerr_endline (error_not_declared id)
  else
    match notnone @@ find_printer env id with
    | DefAxiom(id,t1), DefAxiom(_,t2) ->
       print_endline (string_of_axiom id t1 t2 [])
    | DefLet(id,t1,t2), DefLet(_, t3,t4) ->
       print_endline (string_of_let id (t1,t2,t3,t4) [])
    | _ -> failwith "print"

let rec print_all env =
  List.iter (print env) (List.rev (to_id_list_const env))

let proof verbose str env id t =
  prerr_endline "Error: proof system not implemented.\n"; env

let add_axiom verbose str env id t =
  if Env.is_const_new env id then
    let t = fix_index [] t in
    try
      let (m,em,t,et) = check_axiom env [] t in
      begin
	if verbose then
          begin
	    print_endline (axiom_message id);
            let (_,meta) = m in
            if meta <> [] then
              begin
                print_endline "=== UNRESOLVED META-VARIABLES ===";
                print_meta env m;
                print_endline "\n=== ESSENCE ===";
                print_meta env em
              end
          end;
        Env.add_const env (DefAxiom (id,t)) (DefAxiom(id,et))
      end
    with
      Err reason ->
      begin
	prerr_endline (string_of_error reason str); env
      end
  else
    begin
      prerr_endline (error_declared id);
      env
    end

let add_let verbose str env id t opt =
  if Env.is_const_new env id then
    let t1 = (fix_index [] t) in
    let t2 =
      match opt with
      | Underscore _ -> None
      | _ -> Some (fix_index [] opt)
    in
    try
      let (m, em, t1, t2, et1, et2) =
        check_term env [] t1 t2 in
      if verbose then
        begin
	  print_endline (let_message id);
            let (_,meta) = m in
            if meta <> [] then
              begin
                print_endline "=== UNRESOLVED META-VARIABLES ===";
                print_meta env m;
                print_endline "\n=== ESSENCE ===";
                print_meta env em
              end
        end;
       Env.add_const env (DefLet (id, t1, t2)) (DefLet (id, et1, et2))
    with
      Err reason -> prerr_endline (string_of_error reason str)
                  ; env
  else
    begin
      prerr_endline (error_declared id);
      env
    end

let normalize str env t =
  let t = fix_index [] t in
  try
    let (m, em, t1, t2, et1, et2) =
      check_term env [] t None
    in
    let t1 = strongly_normalize false env [] t1 in
    let t2 = strongly_normalize false env [] t2 in
    let t3 = strongly_normalize true env [] et1 in
    let t4 = strongly_normalize true env [] et2 in
    print_endline (pretty_print_let (t1,t2,t3,t4) [])
  with
    Err reason -> prerr_endline (string_of_error reason str)

(* repl *)

exception Exc_quit

let rec repl lx env verbose =
  let rec loop (env, meta) =
    begin
      try
	if verbose then (Lexing.flush_input lx; print_string prompt; flush stdout) else ();
	let buf = Buffer.create 80 in
	let rule = Parser.s (Lexer.read buf) lx in
	let str = Buffer.contents buf in
        let foo (env, meta) rule =
          match rule with
	  | Quit -> raise Exc_quit
	  | Load id -> let lx = Lexing.from_channel (open_in id)
		       in
		       begin
		         lx.lex_curr_p <- {lx.lex_curr_p with Lexing.pos_fname = id};
		         repl lx env false
		       end
	  | Proof (id, t) -> (proof verbose str env id t, meta)
	  | Axiom (id, t) -> (add_axiom verbose str env id t, meta)
	  | Definition (id, t, opt)
	    -> (add_let verbose str env id t opt, meta)
	  | Print id -> print env id; (env, meta)
	  | Print_all -> print_all env; (env, meta)
          | Show -> print_meta env meta; (env, meta)
          (* TODO : change for proofs *)
	  | Compute t -> normalize str env t; (env, meta)
	  | Help -> help (); (env, meta)
	  | Error -> prerr_endline (syntaxerror str lx);
		     Lexing.flush_input lx; (env, meta)

          | Beginmeta -> (env, (0,[]))
          | Endmeta -> (env, (0,[]))
          | Unify (t1,t2) ->
             begin
               let (t1,t2) = (fix_index [] t1, fix_index [] t2) in
               (env, Unification.unification false meta env [] t1 t2)
             end
          | Add (l,t) ->
             begin
               let rec tmp (id_list,ctx) =
                 function
                 | [] -> (id_list, ctx)
                 | (x,t) :: l ->
                    let id_list,ctx = x :: id_list, DefAxiom(x,fix_index id_list t) :: ctx in
                    tmp (id_list,ctx) l
               in
               let (id_list, l) = tmp ([],[]) l in
               let t = fix_index id_list t in
               let (meta, _) = Unification.meta_add meta l t dummy_loc in
               (env, meta)
             end
          | UAxiom (id,t)->
             begin
               match Env.find_const false env id with
               | Some n -> prerr_endline (error_declared id); (env,meta)
               | None -> let t = (fix_index [] t) in
                         (Env.add_const env (DefAxiom(id,t)) (DefAxiom(id,t)), meta)
             end
          | UDefinition (id,t1,t2) ->
             begin
               match Env.find_const false env id with
               | Some n -> prerr_endline (error_declared id); (env,meta)
               | None -> let (t1,t2) = (fix_index [] t1, fix_index [] t2) in
                         (Env.add_const env (DefLet(id,t1,t2)) (DefLet(id,t1,t2)), meta)
             end
        in
        (* TODO: better error management,
           e.g. what if a type-checking error cancels only
         one axiom when we declared several ones. *)
        loop (List.fold_left foo (env,meta) rule)
      with
      | Failure a -> prerr_endline (failure a);
		     loop (env, meta)
      | Sys_error a -> prerr_endline (syserror a);
		       loop (env, meta)
      | Exc_quit -> (env, meta)
      | e -> prerr_endline (Printexc.to_string e);
	     loop (env, meta)
    end
  in loop (env, (0,[]))

(* main *)

let main () =
  let lx = Lexing.from_channel stdin
  in
  begin
    Arg.parse options arg_file usage;
    print_endline welcome_message;
    let (env, meta) =
      if (!initfile) = "" then
	([], (0,[]))
      else
	try
	  repl (Lexing.from_channel (open_in !initfile)) [] false
	with
	| Sys_error a -> prerr_endline (syserror a); ([], (0,[]))
    in
    repl lx env true
  end
