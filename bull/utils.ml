(* TODO:
   define meta-env, substitution
   do refinement
   do checking
   define "complex" lexing/parsing
   define "complex" printing

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

let nothing = Underscore dummy_loc

type fullterm = { delta : term; essence : term }
type fulltype = fullterm
let dummy_term = {delta=nothing ; essence=nothing}

(* In the contexts, there are let-ins and axioms *)
type declaration =
  | DefAxiom of string * fulltype (* x : A *)
  | DefEssence of string * term * fulltype (* x {essence=t} : A *)
  | DefLet of string * fullterm * fulltype (* x := t : A *)

(* Indices for meta-variables are integers (not de Bruijn indices) *)

(* Idea:
Two questions:
- do we know the essence? (Y/N)
- do we know the type? (Y/N)
Hence 4 main algorithms.

Meta-environment: list of 4 possible things:
- is_sort ?n (means ?n is either Type or Kind) (superseded by ?n is sort s)
- ?n is sort s
- Gamma |- ?n : T (superseded by ?n := x and by essence(?n) := x : T)
- Gamma |- essence ?n := x : T (superseded by ?n := x)
- Gamma |- ?n := x : T
*)
type metadeclaration =
  | IsSort of int
  | SubstSort of sort
  | DefMeta of declaration list * int * fulltype
  | Subst of declaration list * int * fullterm * fulltype
  | SubstEssence of declaration list * int * term * fulltype

type metaenv = int * (metadeclaration list)

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
