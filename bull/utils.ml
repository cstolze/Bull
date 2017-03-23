(* We need both a string identifier and the Bruijn index for the terms, as we *)
(* will print the identifier back to the user. *)
type bruijn_index =
  Bruijn of (string * int)

(* Pure lambda-terms *)
type essence =
  | EVar of bruijn_index
  | EAbs of string * essence
  | EApp of essence * essence

(* Core types *)
type kind =
  | Type
  | KProd of string * family * kind

 and family =
   | FProd of string * family * family
   | FAbs of string * family * family
   | FApp of family * delta
   | FInter of family * family
   | FUnion of family * family
   | FAtom of string
   | FOmega
   | FAny

 and delta =
   | DVar of bruijn_index
   | DStar
   | DAbs of string * family * delta
   | DApp of delta * delta
   | DInter of delta * delta
   | DPrLeft of delta
   | DPrRight of delta
   | DUnion of string * family * delta
	       * string * family * delta
	       * delta
   | DInLeft of delta
   | DInRight of delta

(* We call sigma the context in which the delta-terms are processed *)
type declaration =
  | DefType of kind
  | DefConst of family
  | DefDelta of delta * family

type sigma =
  Sigma of (string * declaration) list

(* Commands from the REPL *)
type sentence =
  | Quit
  | Load of string
  | Proof of string * family
  | Typecst of string * kind
  | Cst of string * family
  | Typecheck of string * delta * family
  | Typeinfer of string * delta
  | Print of string
  | Print_all
  | Compute of string
  | Help
  | Error

(* The proof module should be rewritten from scratch *)
type proofrule =
  | PError
  | PQuit
  | PAbort
  | PBacktrack
  | PExact of delta (* ; __ ; *)
  | PAbst1 (* dependent case *)
  | PAbst2 of string (* non-dependent case (the user has to input a variable name *)
  | PSConj
  | PSDisj of string * bfamily * bfamily
  | PProjL of bfamily
  | PProjR of bfamily
  | PInjL
  | PInjR

type path = Left | Middle | Right

(* auxiliary functions for using signature *)
(* TODO: refactor *)

let rec find id l =
  match l with
  | [] -> false
  | (x, y) :: l' -> if x = id then true else find id l'

let rec get id l =
  match l with
  | [] -> failwith "the programmer should ensure this does not happen (use the find function)"
  | (x, y) :: l' -> if x = id then y else get id l'

let find_type id ctx = let Sig (a,b,c) = ctx in find id a
let get_type id ctx = let Sig (a,b,c) = ctx in get id a
let find_cst id ctx = let Sig (a,b,c) = ctx in find id b
let get_cst id ctx = let Sig (a,b,c) = ctx in get id b (* we suppose id has already been found *)
let find_def id ctx = let Sig (a,b,c) = ctx in find id c
let get_def id ctx = let Sig (a,b,c) = ctx in get id c (* we suppose id has already been found *)
let find_all id ctx = find_type id ctx || find_cst id ctx || find_def id ctx

let typecst_to_string id t = id ^ " : " ^ (kind_to_string (bruijn_to_kind t)) ^ "\n"
let cst_to_string id t = "Constant " ^ id ^ " : " ^ (family_to_string (bruijn_to_family t)) ^ "\n"
let def_to_string id t = let (a,b) = t in
			 id ^ " = " ^ (delta_to_string (bruijn_to_delta a)) ^ " : " ^ (family_to_string (bruijn_to_family b)) ^ "\n"
