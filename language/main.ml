(*
    <one line to give the program's name and a brief idea of what it does.> :-D
    Copyright (C) 2016 Vincent Michielini, Claude Stolze

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

let version _ = print_string "<program>  Copyright (C) 2016  Vincent Michielini, Claude Stolze\nLicense GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n"; exit 0

let versiondoc = "output version information and exit\n"

let arg_file arg = print_string ("loading " ^ arg ^ " not implemented yet\n")

let options = ("-v", Arg.Unit (version), versiondoc) :: []

(* commands *)

let print id ctx = if find_type id ctx then
		     print_endline (typecst_to_string id (get_type id ctx))
		   else
		     (if find_cst id ctx then
			print_endline (cst_to_string id (get_cst id ctx))
		      else
			(if find_def id ctx then
			   print_endline (def_to_string id (get_def id ctx))
			 else
			   print_string (id ^ "has not been declared yet.\n\n")
			)
		     )

let print_all ctx =
  let rec empty_typecst l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (typecst_to_string x y) ^ (empty_typecst l')
  in
  let rec empty_cst l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (cst_to_string x y) ^ (empty_cst l')
  in
  let rec empty_def l =
    match l with
    | [] -> ""
    | (x,y) :: l' -> (def_to_string x y) ^ (empty_def l')
  in
  let Sig (a,b,c) = ctx in
  print_endline ((empty_typecst a) ^ (empty_cst b) ^ (empty_def c))

let typecst id k ctx = match ctx with
  | Sig (a,b,c) -> Sig ((id,k) :: (clean_list id a) , clean_list id b, clean_list id c)
let cst id f ctx =
  let Sig (a,b,c) = ctx in
  let error = is_family_sound f (Sig (clean_list id a, clean_list id b, clean_list id c)) in
  if error = "" then Sig (clean_list id a, (id,f) :: (clean_list id b), clean_list id c)
  else
    begin
      print_endline error;
      ctx
    end
let proof id f ctx = print_string "Not implemented yet\n"; ctx
let typecheck id delta f ctx = print_string "Not implemented yet\n"; ctx
let typeinfer id d ctx = print_string "Not implemented yet\n"; ctx
let load file ctx = print_string "Not implemented yet\n"; ctx

(* main *)

let main =
  let rec main_loop lx ctx =
  begin
    print_string "> "; flush stdout;
    match Parser.s Lexer.read lx with
    | Quit -> ()
    | Load id -> print_string ("Load " ^ id ^ ".\n"); main_loop lx ctx
    | Proof (id, f) -> print_string ("Proof" ^ id ^ " : " ^ (family_to_string f) ^ ".\n"); main_loop lx ctx
    | Typecst (id, k) -> main_loop lx (typecst id k ctx)
    | Cst (id, f) -> main_loop lx (cst id f ctx)
    | Typecheck (id, d, f) -> print_string "Typecheck.\n"; main_loop lx ctx
    | Typeinfer (id, d) -> print_string "Typeinfer.\n"; main_loop lx ctx
    | Print id -> print id ctx; main_loop lx ctx
    | Print_all -> print_all ctx; main_loop lx ctx
    | Error -> print_string "Syntax error.\n"; main_loop lx ctx
  end
  in
  let lx = Lexing.from_channel stdin
  in
  begin
    Arg.parse options arg_file usage;
    main_loop lx (Sig ([], [], []))
  end
;;

main
