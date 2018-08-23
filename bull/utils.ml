(* TODO:
   redefine lexing/parsing
   define meta-env, substitution
   define couple term * essence

*)

type location = Lexing.position * Lexing.position
let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

(* sorts *)
type sort = Type | Kind

(* Core type *)
type term =
  | Sort of location * sort
  | Let of location * string * term * term * term (* let s : t1 := t2 in t3 *)
  | Prod of location * string * term * term (* forall s : t1, t2 *)
  | Abs of location * string * term * term (* fun s : t1 => t2 *)
  | App of location * term * term (* t1 t2 *)
  | Inter of location * term * term (* t1 & t2 *)
  | Union of location * term * term (* t1 | t2 *)
  | SPair of location * term * term (* < t1, t2 > *)
  | SPrLeft of location * term (* proj_l t1 *)
  | SPrRight of location * term (* proj_r t1 *)
  | SMatch of location * term * term * string * term * term * string * term * term (* match t1 return t2 with s1 : t3 => t4 , s2 : t5 => t6 end *)
  | SInLeft of location * term * term (* inj_l t1 t2 *)
  | SInRight of location * term * term (* inj_r t1 t2 *)
  | Coercion of location * term * term (* coe t1 t2 *)
  | Var of location * int (* bruijn index *)
  | Const of location * string (* variable name *)
  | Underscore of location (* meta-variables before analysis *)
  | Meta of location * int * (term list) (* index and substitution *)

type fullterm = { delta : term; essence : term }
type fulltype = fullterm

(* In the contexts, there are let-ins and axioms *)
type declaration =
  | DefAxiom of fulltype (* x : A *)
  | DefEssence of term * fulltype (* x {essence=t} : A *)
  | DefLet of fullterm * fulltype (* x := t : A *)

(* find the de Bruijn index associated with an identifier *)
(* TODO: refactor so utils only contain type declarations *)
let find id id_list =
  let rec aux l n =
    match l with
    | [] -> None
    | id' :: l' -> if id = id' then Some n else (aux l' (n+1))
  in aux id_list 0

(* Commands from the REPL *)
type sentence =
  | Quit
  | Load of string
  | Proof of string * term
  | Axiom of string * term
  | Definition of string * term * (term option)
  | Print of string
  | Print_all
  | Compute of string
  | Help
  | Error
