(*
    <one line to give the program's name and a brief idea of what it does.> :-D
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

(* cli arguments *)

let usage = "Usage: ./main.native [-v] [FILE]\n"

let version _ = print_string "<program>  Copyright (C) 2016  Claude Stolze, ENS Rennes, UPMC, INRIA\nLicense GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n"; exit 0

let versiondoc = "output version information and exit\n"

let initfile = ref ""
let arg_file arg = initfile := arg

let options = ("-v", Arg.Unit (version), versiondoc) :: []

(* commands *)

let help () = print_endline "List of commands:\nHelp;\t\t\t\t\tshow this help\nLoad file;\t\t\t\tload a script file\nType typename : kind;\t\t\tdefine a type constant in the signature\nConstant cstname : type;\t\tdefine a constant in the signature\nProof proofname : type;\t\t\tstart an interactive proof\nDefinition name = deltaterm [: type];\tdefine a delta-term\nPrint name;\t\t\t\tprint the definition of name\nPrint_all;\t\t\t\tprint the signature\nQuit;\t\t\t\t\tquit\n"

let print id ctx = if find_type id ctx then
		     print_endline (typecst_to_string id (get_type id ctx))
		   else
		     (if find_cst id ctx then
			print_endline (cst_to_string id (get_cst id ctx))
		      else
			(if find_def id ctx then
			   print_endline (def_to_string id (get_def id ctx))
			 else
			   prerr_endline (id ^ "has not been declared yet.\n")
			)
		     )

let print_all ctx =
  let rec all_typecst l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (typecst_to_string x y) ^ (all_typecst l')
  in
  let rec all_cst l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (cst_to_string x y) ^ (all_cst l')
  in
  let rec all_def l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (def_to_string x y) ^ (all_def l')
  in
  let Sig (a,b,c) = ctx in
  print_endline ((all_typecst a) ^ (all_cst b) ^ (all_def c))

let typecst id k ctx =
  if find_all id ctx then
    begin
      prerr_endline ("Error: " ^ id ^ " already exists.\n");
      ctx
    end
  else
    match ctx with
    | Sig (a,b,c) -> Sig ((id,k) :: a , b, c)

let cst id f ctx =
  if find_all id ctx then
    begin
      prerr_endline ("Error: " ^ id ^ " already exists.\n");
      ctx
    end
  else
    let Sig (a,b,c) = ctx in
    let error = is_family_sound f ctx in
    if error = "" then Sig (a, (id,f) :: b, c)
    else
      begin
	prerr_endline error; (* the type may be unsound (ie it relies on undeclared basic types *)
	ctx
      end

let proof id f ctx = print_string "Not implemented yet\n"; ctx

let typecheck id d f ctx verb =
  if find_all id ctx then
    begin
      prerr_endline ("Error: " ^ id ^ " already exists.\n");
      ctx
    end
  else
    let Sig (a,b,c) = ctx in
    if Inference.is_wellformed d then
      (if Inference.inferable d ctx then
	 let f' = Inference.inference d ctx in
	 (if Inference.unifiable f f' then
	    (begin
		(if verb then print_endline (def_to_string id (d,Inference.unify f f')) else ());
		Sig (a, b, (id,(d,f)):: c)
	      end)
	  else
	    begin
	      prerr_endline ("Error: type-checking failed for " ^ (def_to_string id (d,f)) ^ " (its type should be " ^ (family_to_string f') ^ ").\n");
	      ctx
	    end
	 )
       else
	 begin
	   prerr_endline ("Error: type not inferable for " ^ (delta_to_string d) ^ ".\n");
	   ctx
	 end
      )
    else
      begin
	prerr_endline ("Error: " ^ (delta_to_string d) ^ " is ill-formed.\n");
	ctx
      end

let typeinfer id d ctx verb =
  if find_all id ctx then
    begin
      prerr_endline ("Error: " ^ id ^ " already exists.\n");
      ctx
    end
  else
    let Sig (a,b,c) = ctx in
    if Inference.is_wellformed d then
      (if Inference.inferable d ctx then
	 let f = Inference.inference d ctx in
	 (begin
	     (if verb then print_endline (def_to_string id (d,f)) else ());
	     Sig (a, b, (id,(d,f)):: c)
	   end)
       else
	 begin
	   prerr_endline ("Error: type not inferable for " ^ (delta_to_string d) ^ ".\n");
	   ctx
	 end
      )
    else
      begin
	prerr_endline ("Error: " ^ (delta_to_string d) ^ " is ill-formed.\n");
	ctx
      end

let rec load file ctx =
  let rec load_loop lx ctx =
    begin
      try
	match Parser.s Lexer.read lx with
	| Quit -> ctx
	| Load id -> load_loop lx (load id ctx)
	| Proof (id, f) -> load_loop lx (proof id f ctx)
	| Typecst (id, k) -> load_loop lx (typecst id k ctx)
	| Cst (id, f) -> load_loop lx (cst id f ctx)
	| Typecheck (id, d, f) -> load_loop lx (typecheck id d f ctx false)
	| Typeinfer (id, d) -> load_loop lx (typeinfer id d ctx false)
	| Print id -> print id ctx; load_loop lx ctx
	| Print_all -> print_all ctx; load_loop lx ctx
	| Help -> help (); load_loop lx ctx
	| Error -> prerr_endline "Syntax error.\n"; load_loop lx ctx
      with
      | Failure a -> Lexing.flush_input lx; prerr_endline ("Error: " ^ a ^ ".\n"); load_loop lx ctx
      | _ -> Lexing.flush_input lx; prerr_endline ("Error.\n"); load_loop lx ctx
    end
  in
  let channel = open_in file in
  let lx = Lexing.from_channel channel in
  load_loop lx ctx


(* main *)

let main =
  let rec main_loop lx ctx =
  begin
    print_string "> "; flush stdout;
    try
      match Parser.s Lexer.read lx with
      | Quit -> ()
      | Load id -> main_loop lx (load id ctx)
      | Proof (id, f) -> main_loop lx (proof id f ctx)
      | Typecst (id, k) -> main_loop lx (typecst id k ctx)
      | Cst (id, f) -> main_loop lx (cst id f ctx)
      | Typecheck (id, d, f) -> main_loop lx (typecheck id d f ctx true)
      | Typeinfer (id, d) -> main_loop lx (typeinfer id d ctx true)
      | Print id -> print id ctx; main_loop lx ctx
      | Print_all -> print_all ctx; main_loop lx ctx
      | Help -> help (); main_loop lx ctx
      | Error -> prerr_endline "Syntax error.\n"; main_loop lx ctx
    with
    | Failure a -> Lexing.flush_input lx; prerr_endline ("Error: " ^ a ^ ".\n"); main_loop lx ctx
    | _ -> Lexing.flush_input lx; prerr_endline ("Error.\n"); main_loop lx ctx
  end
  in
  let lx = Lexing.from_channel stdin
  in
  begin
    Arg.parse options arg_file usage;
    print_endline "Type \"Help;\" for help.\n";
    if (!initfile) = "" then
      main_loop lx (Sig ([], [], []))
    else
      main_loop lx (load (!initfile) (Sig ([], [], [])))
  end
;;

main
