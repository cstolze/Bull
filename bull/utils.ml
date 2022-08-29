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
  | App of location * term * term list (* t1 t2 *)
  | SProd of location * string * term * term (* sforall s : t1, t2 *)
  | SAbs of location * string * term * term (* sfun s : t1 => t2 *)
  | SApp of location * term * term (* strong application (for the essence) of t1 and t2 *)
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

(* This is the safe way to construct an application *)
(* putting spines in spines *)
let app l t1 t2 =
  match t1 with
  | App(l, t1, l1) -> App(l, t1, t2 :: l1)
  | _ -> App (l, t1, t2 :: [])

let app' l t1 t2 =
  match t1 with
  | App(l, t1, l1) -> App(l, t1, t2 @ l1)
  | _ -> App(l, t1, t2)

let loc_term t =
  match t with
  | Sort (l, _) | Let (l,_,_,_,_) | Prod (l,_,_,_) | Abs (l,_,_,_) | App (l,_,_) | SProd (l,_,_,_) | SAbs (l,_,_,_) | SApp (l,_,_) | Inter (l,_,_)
    | Union (l,_,_) | SPair (l,_,_) | SPrLeft (l,_) | SPrRight (l,_) | SMatch (l,_,_,_,_,_,_,_,_)
    | SInLeft (l,_,_) | SInRight (l,_,_) | Coercion (l,_,_) | Var (l,_) | Const (l,_)
    | Underscore l | Meta (l,_,_) -> l

let nothing = Underscore dummy_loc

(* In the contexts, there are let-ins and axioms *)
type declaration =
  | DefAxiom of string * term (* x : A *)
  | DefLet of string * term * term (* x := t : A *)

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
  | SubstSort of int * term
  | DefMeta of declaration list * int * term
  | Subst of declaration list * int * term * term

type metaenv = int * (metadeclaration list)

(* Commands from the REPL *)
type sentence =
  | Quit
  | Load of string
  | Proof of string * term
  | Axiom of string * term
  | Definition of string * term * term
  | Print of string
  | Print_all
  | Show
  | Compute of term
  | Help
  | Error
  | Beginmeta
  | Endmeta
  | Unify of term * term
  | Add of (string * term) list * term
  | UAxiom of string * term (* for debugging *)
  | UDefinition of string * term * term (* for debugging *)

(* Error during type reconstruction *)
type errcheck =
  | Kind_Error
  | Prod_Error of location * term
  | App_Error of location * term * term * term * term
  | Set_Error of location * term
  | Proj_Error of location * term * term
  | Match_Error of location * term * term * term * term
  | Coercion_Error of location * term * term * term
  | Const_Error of location * string
  | Force_Type_Error of location * term * term
  | Typecheck_Error of location * term * term * term
  | Wrong_Type_Error of location * term * term
  | Essence_Error of location * term * term

type env_const = declaration * declaration list
type env_var = declaration list
exception Err of (env_var * errcheck)
let err x y = raise (Err (x,y))

let notnone x =
  match x with
  | None -> assert false
  | Some x -> x

let find l n =
    try
      ignore @@ List.find (fun m -> m = n) l;
      true
    with
    | Not_found -> false
