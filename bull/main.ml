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

(* cli arguments *)

let usage = "Usage: ./main.native [-v] [FILE]\n"

let version _ = print_string "<program>  Copyright (C) 2016  Claude Stolze, ENS Rennes, UPMC, INRIA\nLicense GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n"; exit 0

let versiondoc = "output version information and exit\n"

let initfile = ref ""
let arg_file arg = initfile := arg

let options = ("-v", Arg.Unit (version), versiondoc) :: []

(* commands *)

let help () = print_endline "List of commands:\nHelp;\t\t\t\t\tshow this help\nLoad FILE;\t\t\t\tload a script file\nType NAME : KIND;\t\t\tdeclare a type constant\nConstant NAME : TYPE;\t\t\tdeclare a constant\nProof NAME : TYPE;\t\t\tstart an interactive proof\nDefinition NAME = DELTATERM [: TYPE];\tdefine a delta-term\nPrint NAME;\t\t\t\tprint the definition of NAME\nPrint_all;\t\t\t\tprint all the terms declared or defined during this session\nCompute NAME;\t\t\t\tprint the normalized form of NAME\nQuit;\t\t\t\t\tquit\n"

let print id ctx = if find_type id ctx then
		     print_endline (typecst_to_string id (get_type id ctx))
		   else
		     (if find_cst id ctx then
			print_endline (cst_to_string id (get_cst id ctx))
		      else
			(if find_def id ctx then
			   print_endline (def_to_string id (get_def id ctx))
			 else
			   prerr_endline (id ^ " has not been declared yet.\n")
			)
		     )

let print_all ctx =
  let rec all_typecst l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (all_typecst l') ^ (typecst_to_string x y)
  in
  let rec all_cst l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (all_cst l') ^ (cst_to_string x y)
  in
  let rec all_def l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (all_def l') ^ (def_to_string x y)
  in
  let Sig (a,b,c) = ctx in
  print_endline ((all_typecst a) ^ (all_cst b) ^ (all_def c))

let typecst id k ctx =
  if Inference.wellformed_kind k ctx then
    let err = Inference.typecstcheck id k ctx in
    if err = "" then
      match ctx with
      | Sig (a,b,c) -> Sig ((id,k) :: a , b, c)
    else
      begin
	prerr_endline err;
	ctx
      end
  else
    begin
      prerr_endline ("Error: " ^ (kind_to_string (bruijn_to_kind k)) ^ " is ill-formed.\n");
      ctx
    end

let cst id f ctx =
  if Inference.wellformed_family f ctx then
    let err = Inference.cstcheck id f ctx in
    if err = "" then
      match ctx with
      | Sig (a,b,c) -> Sig (a , (id,f) :: b, c)
    else
      begin
	prerr_endline err;
	ctx
      end
  else
    begin
      prerr_endline ("Error: " ^ (family_to_string (bruijn_to_family f)) ^ " is ill-formed.\n");
      ctx
    end

let proof id f lx ctx verb =
  if find_all id ctx then
    begin
      prerr_endline ("Error: " ^ id ^ " already exists.\n");
      ctx
    end
  else
    let rec gamma_to_string gamma =
      match gamma with
      | [] -> ""
      | (id, f) :: gamma' -> (gamma_to_string gamma') ^ (cst_to_string id f)
    in
    let rec proofloop pr past =
      let (goal, gamma) =
	match pr with
	| (_,[]) -> failwith "should not happen"
	| (_, (g, _, g') :: _) -> (g, g')
      in
      begin
	(if verb then
	   (print_string ("Goal to prove : " ^ (family_to_string (bruijn_to_family goal)) ^ "\nHypotheses:\n" ^ (gamma_to_string gamma) ^ "End of hypotheses.\n" ^ id ^ ">>> "); flush stdout;)
	 else ());
	try
	  match Parser.proof Lexer.read lx with
	  | PError -> prerr_endline "Syntax error.\n"; proofloop pr past
	  | PAbort -> ctx
	  | PBacktrack -> (match past with
			   | [] -> proofloop pr past
			   | x :: l -> proofloop x l
			  )
	  | rule -> (try
			let (tree, goal') = Proof.proofstep pr rule ctx in
			(if (Proof.essence_trick tree ctx) then
			      match goal' with
			      | [] -> let Sig (a, b, c) = ctx in
				      begin
					(if verb then print_endline (def_to_string id (tree,f)) else ());
					Sig (a, b, (id, (tree, f)) :: c) (* Proof completed *)
				      end
			      | _ -> proofloop (tree, goal') (pr :: past)
			    else
			      failwith "essence error")
		      with
		      | Failure err -> prerr_endline err; proofloop pr past
		      | _ -> failwith "oops"
		    )
	with
	| Failure a -> Lexing.flush_input lx; prerr_endline ("Error: " ^ a ^ ".\n"); proofloop pr past
	| _ -> Lexing.flush_input lx; prerr_endline ("Error.\n"); proofloop pr past
      end
    in
    proofloop (Proof.newproof f) []

let typecheck id d f ctx verb =
  if find_all id ctx then
    begin
      prerr_endline ("Error: " ^ id ^ " already exists.\n");
      ctx
    end
  else
    let err = Inference.familycheck f [] ctx in
    if err = "" then
      let Sig (a,b,c) = ctx in
      if Inference.wellformed_delta d ctx then
	let err = Inference.deltacheck d [] ctx in
	if err = "" then
	  if Inference.wellformed_family f ctx then
	    let f' = Inference.deltainfer d [] ctx in
	    if Inference.unifiable f f' ctx then
	      begin
		(if verb then print_endline (def_to_string id (d,f)) else ());
		Sig (a, b, (id,(d,f)) :: c)
	      end
	    else
	      begin
		prerr_endline ("Error: type-checking failed for " ^ (def_to_string id (d,f)) ^ " (its type should be " ^ (family_to_string (bruijn_to_family f')) ^ ").\n");
		ctx
	      end
	  else
	    begin
	      prerr_endline ("Error: " ^ (family_to_string (bruijn_to_family f)) ^ " is ill-formed.\n");
	      ctx
	    end
	else
	  begin
	    prerr_endline err;
	    ctx
	  end
      else
	begin
	  prerr_endline ("Error: " ^ (delta_to_string (bruijn_to_delta d)) ^ " is ill-formed.\n");
	  ctx
	end
    else
      begin
	prerr_endline err;
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
    if Inference.wellformed_delta d ctx then
      (let err = Inference.deltacheck d [] ctx in
       if err = "" then
	 let f = Inference.deltainfer d [] ctx in
	 (begin
	     (if verb then print_endline (def_to_string id (d,f)) else ());
	     Sig (a, b, (id,(d,f)):: c)
	   end)
       else
	 begin
	   prerr_endline err;
	   ctx
	 end
      )
    else
      begin
	prerr_endline ("Error: " ^ (delta_to_string (bruijn_to_delta d)) ^ " is ill-formed.\n");
	ctx
      end

let normalize id ctx =
  if find_def id ctx then
    let (d,f) = get_def id ctx in
    print_endline ((delta_to_string (bruijn_to_delta (Reduction.delta_compute d ctx))) ^ " : " ^ (family_to_string (bruijn_to_family (Reduction.family_compute f ctx))) ^ "\n")
  else
    prerr_endline (id ^ " has not been declared yet.\n")

let rec load file ctx =
  let rec load_loop lx ctx =
    begin
      try
	match Parser.s Lexer.read lx with
	| Quit -> ctx
	| Load id -> load_loop lx (load id ctx)
	| Proof (id, f) -> load_loop lx (proof id (family_to_bruijn f) lx ctx false)
	| Typecst (id, k) -> load_loop lx (typecst id (kind_to_bruijn k) ctx)
	| Cst (id, f) -> load_loop lx (cst id (family_to_bruijn f) ctx)
	| Typecheck (id, d, f) -> load_loop lx (typecheck id (delta_to_bruijn d) (family_to_bruijn f) ctx false)
	| Typeinfer (id, d) -> load_loop lx (typeinfer id (delta_to_bruijn d) ctx false)
	| Print id -> print id ctx; load_loop lx ctx
	| Print_all -> print_all ctx; load_loop lx ctx
	| Compute id -> normalize id ctx; load_loop lx ctx
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

let () =
  let rec main_loop lx ctx =
    begin
      print_string "> "; flush stdout;
      try
	match Parser.s Lexer.read lx with
	| Quit -> ()
	| Load id -> main_loop lx (load id ctx)
	| Proof (id, f) -> main_loop lx (proof id (family_to_bruijn f) lx ctx true)
	| Typecst (id, k) -> main_loop lx (typecst id (kind_to_bruijn k) ctx)
	| Cst (id, f) -> main_loop lx (cst id (family_to_bruijn f) ctx)
	| Typecheck (id, d, f) -> main_loop lx (typecheck id (delta_to_bruijn d) (family_to_bruijn f) ctx true)
	| Typeinfer (id, d) -> main_loop lx (typeinfer id (delta_to_bruijn d) ctx true)
	| Print id -> print id ctx; main_loop lx ctx
	| Print_all -> print_all ctx; main_loop lx ctx
	| Compute id -> normalize id ctx; main_loop lx ctx
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
