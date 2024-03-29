(* Possible extension: do pretty-printing functions whose types are Format.formatter -> t -> unit, so we can mess with the toplevel ocaml pretty-printer *)

open Utils
open Bruijn
open Env

(* error localisation *)
(* hatstring a b returns "   ^^^", where the hats go from position a to position b *)
let hatstring a b =
  let rec white n =
    if n = 0 then "" else " " ^ (white (n-1))
  in
  let rec hat n =
    if n = 0 then "" else "^" ^ (hat (n-1))
  in white a ^ hat (b-a) ^ "\n"

(* extract whole lines from position a to position b, including \n in the beginning and end *)
let rec extract str a b =
  if (a+1 > String.length str) then extract str (a-1) b else
    if (b+1 > String.length str) then extract str a (b-1) else
      if (b+1 = String.length str || str.[b] = '\n') then
	if (a = 0 || str.[a] = '\n') then
	  let a = if a = 0 then a else a+1 in
	    let str2 = "\n" ^ String.sub str a (b-a+1) in
	    if str.[b] = '\n' then str2 else str2 ^ "\n"
	else
	  extract str (a-1) b
      else
	extract str a (b+1)

let error_loc (l1,l2) str =
  if (l1,l2) = dummy_loc then "" else
    let file = l1.Lexing.pos_fname (* we assume the two positions are in the same file *)
    in
    let str =
      if l1.Lexing.pos_lnum = l2.Lexing.pos_lnum then
        let str = extract str l1.Lexing.pos_cnum l2.Lexing.pos_cnum in
        let a = l1.Lexing.pos_cnum-l1.Lexing.pos_bol in
        let b = if l1 = l2 then a+1 else l2.Lexing.pos_cnum-l1.Lexing.pos_bol in
        let str2 = hatstring a b in
        str ^ str2
      else (* multiline error *)
        "\n..." ^ String.sub str l1.Lexing.pos_cnum (l2.Lexing.pos_cnum - l1.Lexing.pos_cnum) ^ "...\n"
    in
    if file = "" then str
    else "In file " ^ file ^ ", line "^string_of_int l1.Lexing.pos_lnum^", characters " ^ string_of_int (l1.Lexing.pos_cnum - l1.Lexing.pos_bol) ^ " -- " ^ string_of_int (l2.Lexing.pos_cnum - l1.Lexing.pos_bol) ^ ":\n" ^ str

(* for the precedences, see parser.mly *)
(* when calling aux, the precedence is (precedence-1) *)
let rec string_of_term is_essence id_list t =
  let rec metacontext n id_list l =
    match l with
    | [] -> ""
    | x :: l -> let ns = "$" ^ (string_of_int n) in
                ns ^ " := " ^ (string_of_term
                                 is_essence id_list x) ^
                  match l with
                  | [] -> ""
                  | _ -> "; " ^ metacontext (n+1) id_list l
  in
  let rec aux t precedence =
    let parentheseme trigger text =
      if precedence < trigger then text else "(" ^ text ^ ")"
    in
    match t with
    | Sort (l, s) -> (match s with
		 | Type -> "Type"
		 | Kind -> "Kind")
    | Let (l, id, t1, t2, t3) -> parentheseme 1 ("let " ^ id ^ (if is_essence then "" else " : "
					  ^ aux t1 0) ^ " := " ^ aux t2 0 ^ " in " ^ aux t3 0)
    | Prod (l, id, t1, t2) -> if is_const id t2 then
			        parentheseme 1 ("forall " ^ id ^ " : "
					        ^ aux t1 0 ^ ", "
					        ^ aux t2 0)
			      else parentheseme 2 (aux t1 2 ^ " -> "
						   ^ aux t2 1)
    | SProd (l, id, t1, t2) -> if is_const id t2 then
			        parentheseme 1 ("sforall " ^ id ^ " : "
					        ^ aux t1 0 ^ ", "
					        ^ aux t2 0)
			      else parentheseme 2 (aux t1 2 ^ " >> "
						   ^ aux t2 1)
    | Abs (l, id, t1, t2)
      -> parentheseme 1 ("fun " ^ id ^ (if is_essence
					then "" else " : " ^ aux t1 0)
			 ^ " => " ^ aux t2 0)
    | SAbs (l, id, t1, t2)
      -> parentheseme 1 ("sfun " ^ id ^ (if is_essence
					then "" else " : " ^ aux t1 0)
			 ^ " => " ^ aux t2 0)
    | App (l, t1, l2)
      -> parentheseme 5 (aux t1 4 ^ " "
                         ^ String.concat
                             " " (List.map (fun x -> aux x 5) @@ List.rev l2))
    | SApp (l, t1, t2)
      -> parentheseme 5 (aux t1 4 ^ " "
                         ^ aux t2 5)
    | Inter (l, t1, t2) -> parentheseme 4 (aux t1 4 ^ " & " ^ aux t2 3)
    | Union (l, t1, t2) -> parentheseme 3 (aux t1 3 ^ " | " ^ aux t2 2)
    | SPair (l, t1, t2) -> "< " ^  aux t1 0 ^ ", " ^ aux t2 0 ^ " >"
    | SPrLeft (l, t1) -> parentheseme 6 ("proj_l " ^ aux t1 5)
    | SPrRight (l, t1) -> parentheseme 6 ("proj_r " ^ aux t1 5)
    | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6) ->
       begin
         match t2 with
         | Abs(_,x,_,t2) ->
            "match " ^ aux t1 0 ^ " as " ^ x ^ " return " ^ aux t2 0 ^ " with " ^ id1 ^
              " : " ^ aux t3 0 ^ " => " ^ aux t4 0 ^ " , " ^ id2 ^ " : " ^ aux t5 0 ^ " => " ^ aux t6 0 ^ " end"
         | _ -> assert false
       end
    | SInLeft (l, t1, t2) -> parentheseme 6 ("inj_l " ^ aux t1 5
					  ^ " " ^ aux t2 5)
    | SInRight (l, t1, t2) -> parentheseme 6 ("inj_r " ^ aux t1 5
					  ^ " " ^ aux t2 5)
    | Coercion (l, t1, t2) -> parentheseme 6 ("coe " ^ aux t1 5 ^ " " ^ aux t2 5)
    | Var _ -> assert false
    | Const (l, id) -> id
    | Underscore l -> "_"
    | Meta (l,n,s) -> "?" ^ string_of_int n ^ "["
                      ^ (metacontext 0 id_list s)
                      ^ "]"
  in
  aux (fix_id id_list t) 0

(* wrappers for the print functions *)

let pretty_print_term =
  string_of_term false

let pretty_print_essence =
  string_of_term true

let pretty_print_let (t1,t2,t3,t4) id_list =
  pretty_print_term id_list t1 ^ " : " ^ pretty_print_term id_list t2
  ^ "\n\tessence = "
  ^ pretty_print_essence id_list t3 ^ " : "
  ^ pretty_print_essence id_list t4

let string_of_axiom id t1 t2 id_list =
  "Axiom " ^ id ^ " : " ^ pretty_print_term id_list t1
  ^ "\n\tessence = " ^ pretty_print_essence id_list t2

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
let help_text = "Help.\t\t\t\t\tfor a list of commands\nLoad \"file\".\t\t\t\tfor loading a script file\nAxiom term : type.\t\t\tdefine a constant or anaxiom\nDefinition name [: type] := term.\tdefine a term\nPrint name.\t\t\t\tprint the definition of name\nPrintall.\t\t\t\tprint the full environment (axioms and definitions)\nCompute term.\t\t\t\tnormalize term and print the result\nQuit.\t\t\t\t\tquit"

(* Error messages *)
let string_of_error (env,e) str =
  let id_list = to_id_list_var env in
  match e with
  | Kind_Error -> "Error: Type is not a first-class term.\n"
  | Prod_Error (l, t1) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     error_loc l str ^ "Error: the type " ^ t1 ^ " is illegal.\n"
  | App_Error (l, t1, t2, t3, t4) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term false id_list t2 ^ "\"" in
     let t3 = "\"" ^ string_of_term false id_list t3 ^ "\"" in
     let t4 = "\"" ^ string_of_term false id_list t4 ^ "\"" in
     error_loc l str ^ "Error: the term " ^ t1 ^ " of type " ^ t2 ^ " cannot be applied to the term " ^ t3 ^ " of type " ^ t4 ^ ".\n"
  | Set_Error  (l, t1) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     error_loc l str ^ "Error: the type " ^ t1 ^ " is illegal.\n"
  | Proj_Error (l, t1, t2) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term false id_list t2 ^ "\"" in
     error_loc l str ^ "Error: the term " ^ t1 ^ " has type " ^ t2 ^ " which should be an intersection.\n"
  | Match_Error (l, t1, t2, t3, t4) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term false id_list t2 ^ "\"" in
     let t3 = "\"" ^ string_of_term false id_list t3 ^ "\"" in
     let t4 = "\"" ^ string_of_term false id_list t4 ^ "\"" in
     error_loc l str ^ "Error: the term " ^ t1 ^ " has type " ^ t2 ^ " which should be the union of " ^ t3 ^ " and " ^ t4 ^ ".\n"
  | Coercion_Error (l, t1, t2, t3) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term false id_list t2 ^ "\"" in
     let t3 = "\"" ^ string_of_term false id_list t3 ^ "\"" in
     error_loc l str ^ "Error: the term " ^ t1 ^ " of type " ^ t2 ^ " cannot be coerced to type " ^ t3 ^ ".\n"
  | Const_Error (l, id) -> error_loc l str ^ "Error: unbound variable " ^ id ^ ".\n"
  | Force_Type_Error (l, t1, t2) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term false id_list t2 ^ "\"" in
     error_loc l str ^ "Error: the term " ^ t1 ^ " has type " ^ t2 ^ " which should be Type.\n"
  | Typecheck_Error (l, t1, t2, t3) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term false id_list t2 ^ "\"" in
     let t3 = "\"" ^ string_of_term false id_list t3 ^ "\"" in
     error_loc l str ^ "Error: the term " ^ t1 ^ " has type " ^ t2 ^ " while it is expected to have type " ^ t3 ^ ".\n"
  | Wrong_Type_Error (l, t1, t2) ->
     let t1 = "\"" ^ string_of_term false id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term false id_list t2 ^ "\"" in
     error_loc l str ^ "Error: found type " ^ t1 ^ " where " ^ t2 ^ " was expected.\n"
  | Essence_Error (l, t1, t2) ->
     let t1 = "\"" ^ string_of_term true id_list t1 ^ "\"" in
     let t2 = "\"" ^ string_of_term true id_list t2 ^ "\"" in
     error_loc l str ^ "Error: found essence " ^ t1 ^ " where " ^ t2 ^ " was expected.\n"

let error_not_declared id = "Error: " ^ id ^ " is not a declared term.\n"
let error_declared id = "Error: " ^ id ^ " already exists.\n"
let syserror a = "System error: " ^ a ^ ".\n"
let failure a = "Error: " ^ a ^ ".\n"
let syntaxerror str lx =
  let curr = lx.Lexing.lex_curr_p in
  let tok = Lexing.lexeme lx in
  error_loc (curr,curr) str ^
  "Syntax error: \"" ^ tok ^ "\" encountered.\n"

let error_axiom =
  "Error: invalid type.\n"

let sort_error t id_list =
  "Error: sort is "
  ^ pretty_print_term id_list t ^ " (should be Type or Kind).\n"

let let_error t t' id_list =
  "Error: type " ^ pretty_print_term id_list t'
  ^ " is not compatible with "
  ^ pretty_print_term id_list t ^ ".\n"

let error_abs id_list l str t =
  error_loc l str
  ^ "Error: this term has type " ^ pretty_print_term id_list t
  ^ " (should be a sort).\n"

let error_pts (l1,l2) str =
  error_loc (l1,l2) str
  ^ "Error: the Pure Type System cannot infer the sort of this term.\n"

let error_type_prod id_list (l1,l2) str t =
  error_loc (l1,l2) str
  ^ "Error: the returning type is " ^ pretty_print_term id_list t ^ ".\n"

let error_match id_list (l1,l2) str et1 et2 =
  error_loc (l1,l2) str
  ^ "Error: the function expect a term of type "
  ^ pretty_print_essence id_list et1
  ^ ", but is applied to a term of type "
  ^ pretty_print_essence id_list et2 ^".\n"

let error_no_prod id_list l str t =
  error_loc l str
  ^ "Error: this isn't a function, its type is "
  ^ pretty_print_term id_list t ^ ", it can't be applied.\n"

let error_sproj id_list l str t =
  error_loc l str
  ^ "Error: this term has type " ^ pretty_print_term id_list t
  ^ ", it is not an intersection.\n"

let error_set (l1,l2) str =
  error_loc (l1,l2) str
  ^ "Error: you can't use set operators on non-set terms.\n"

let error_kind = "Error: Type is not a first_class object.\n"

let error_essence (l1,l2) str =
  error_loc (l1,l2) str
  ^ "Error: the essence check failed.\n"

let error_const (l1,l2) str id =
  error_loc (l1,l2) str
  ^ "Error: " ^ id ^ " has not been declared.\n"

let error_return l str =
  error_loc l str
  ^ "Error: wrong return type.\n"

let error_with l str =
  error_loc l str
  ^ "Error: wrong argument.\n"

let error_smatch (l1,l2) str =
  error_loc (l1,l2) str
  ^ "Error: type mismatch.\n"

let error_subtype l str id_list t1 t2 =
  error_loc l str
  ^ "Error: the type " ^ pretty_print_term id_list t2 ^ " is not a subtype of " ^
    pretty_print_term id_list t1 ^ ".\n"

let error_coe1 l str id_list t =
  error_loc l str
  ^ "Error: this term has type " ^ pretty_print_term id_list t
  ^ " (should be Type or Kind).\n"

let error_coe2 l str =
  error_loc l str
  ^ "Error: this term is not coercible.\n"
