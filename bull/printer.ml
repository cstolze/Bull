(* Possible extension: do pretty-printing functions whose types are Format.formatter -> t -> unit, so we can mess with the toplevel ocaml pretty-printer *)

open Utils
open Bruijn

(* for the precedences, see parser.mly *)
(* when calling aux, the precedence is (precedence-1) *)
let string_of_term is_essence id_list t =
  let rec aux t precedence =
    let parentheseme trigger text =
      if precedence < trigger then text else "(" ^ text ^ ")"
    in
    match t with
    | Sort s -> (match s with
		 | Type -> "Type"
		 | Kind -> "Kind")
    | Let (id, t1, t2) -> parentheseme 1 ("let " ^ id ^ " := "
					  ^ aux t1 0 ^ " in " ^ aux t2 0)
    | Prod (id, t1, t2) -> parentheseme 1 ("forall " ^ id ^ " : "
					   ^ aux t1 0 ^ ", " ^ aux t2 0)
    | Abs (id, t1, t2)
      -> parentheseme 1 ("fun " ^ id ^ (if is_essence
					then "" else " : " ^ aux t1 0)
			 ^ " => " ^ aux t2 0)
    | Subset (id, t1, t2) -> parentheseme 1 ("sforall " ^ id ^ " : "
					     ^ aux t1 0 ^ ", "
					     ^ aux t2 0)
    | Subabs (id, t1, t2) -> parentheseme 1 ("sfun " ^ id ^ " : "
					     ^ aux t1 0 ^ ", "
					     ^ aux t2 0)
    | App (t1, t2) -> parentheseme 5 (aux t1 4 ^ " " ^ aux t2 5)
    | Inter (t1, t2) -> parentheseme 4 (aux t1 4 ^ " & " ^ aux t2 3)
    | Union (t1, t2) -> parentheseme 3 (aux t1 3 ^ " | " ^ aux t2 2)
    | SPair (t1, t2) -> "< " ^  aux t1 0 ^ ", " ^ aux t2 0 ^ " >"
    | SPrLeft t1 -> parentheseme 6 ("proj_l " ^ aux t1 5)
    | SPrRight t1 -> parentheseme 6 ("proj_l " ^ aux t1 5)
    | SMatch (t1, t2, t3) -> "return " ^ aux t1 0 ^ " with < "
			     ^ aux t2 0 ^ ", " ^ aux t3 0 ^ " >"
    | SInLeft (t1, t2) -> parentheseme 6 ("inj_l " ^ aux t1 5
					  ^ aux t2 5)
    | SInRight (t1, t2) -> parentheseme 6 ("inj_r " ^ aux t1 5
					  ^ aux t2 5)
    | Coercion (t1, t2) -> parentheseme 6 ("coe " ^ aux t1 5 ^ aux t2 5)
    | Var _ -> assert false
    | Const id -> id
    | Omega -> "$"
    | Meta n -> "?" ^ string_of_int n
  in
  aux (fix_id id_list t) 0

(* wrappers for the print functions *)

let pretty_print_term =
  string_of_term false

let pretty_print_essence =
  string_of_term true

let pretty_print_let (t1,t2,t3,t4) id_list =
  pretty_print_term id_list t1 ^ " : " ^ pretty_print_term id_list t2
  ^ ", essence = "
  ^ pretty_print_essence id_list t3 ^ " : " ^ pretty_print_term id_list t4

let string_of_axiom id t1 t2 id_list =
  "Axiom " ^ id ^ " : " ^ pretty_print_term id_list t1
  ^ ", essence = " ^ pretty_print_term id_list t2

let string_of_let id tuple id_list =
  "Definition " ^ id ^ " = " ^ pretty_print_let tuple id_list

(* cli arguments *)

let usage = "Usage: ./main.native [-v] [FILE]\n"
let version_option = "-v"
let version_text =
  "Bull  Copyright (C) 2017  Claude Stolze, Université Côte d'Azur, INRIA\nLicense GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n"
let version_doc = "output version information and exit\n"

(* REPL text *)

let prompt = "> "
let welcome_message =
  "Welcome to Bull, an experimental LF-based proof checker with set-inspired types.\nType \"Help.\" for help.\n"
let axiom_message id = id ^ " is assumed.\n"
let let_message id = id ^ " is defined.\n"
let help_text = "List of commands:\nHelp.\t\t\t\t     show this list of commands\nLoad file.\t\t      \t     for loading a script file\nAxiom term : type.\t    \t     define a constant or an axiom\nLemma proofname : term.        \t     start an interactive proof (not implemented yet)\nDefinition name [: type] := term.    define a term\nPrint name. \t       \t  \t     print the definition of name\nPrintall. \t\t\t     print all the signature (axioms and definitions)\nCompute name.\t\t\t     normalize name and print the result\nQuit. \t\t\t\t     quit"

(* Error messages *)

let error_not_declared id = "Error: " ^ id ^ " is not a declared term."
let error_declared id = "Error: " ^ id ^ " already exists."
let syserror a = "System error: " ^ a ^ ".\n"
let failure a = "Error: " ^ a ^ ".\n"
let syntaxerror = "Syntax error.\n"
let unknownerror = "Unknown error.\n"
let sort_error t id_list =
  "Error: sort is "
  ^ pretty_print_term t id_list ^ " (should be Type or Kind)."
