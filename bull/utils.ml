(* We need both a string identifier and the Bruijn index for the terms, as we *)
(* will print the identifier back to the user. *)
type bruijn_index =
  Bruijn of (string * int)

(* sorts *)
type sort = Type | Kind

(* Pure lambda-terms *)
type essence =
  | EVar of bruijn_index
  | EAbs of string * essence
  | EApp of essence * essence
  | EProd of essence * essence
  | ESort of sort

(* Core type *)
(* Note: the Meta variables are useless till we implement a refiner *)
type term =
  | Sort of sort
  | Prod of string * term * term
  | Abs of string * term * term
  | App of term * term
  | Inter of term * term
  | Union of term * term
  | SPair of term * term
  | SPrLeft of term
  | SPrRight of term
  | SMatch of term * term
  | SInLeft of term * term
  | SInRight of term * term
  | Var of bruijn_index
  | Omega
  | Star
  | Meta of bruijn_index

(* We call sigma the context in which the delta-terms are processed *)
type declaration =
  | DefConst of term
  | DefLet of term * term

type sigma =
  Sigma of (string * declaration) list

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

(* Error encoding *)
module Result = struct
    type ('a, 'b) t =
      | Ok of 'a
      | Error of 'b

    let bind x f =
      match x with
      | Ok a -> f a
      | Error b -> Error b
  end

(* auxiliary functions for using signature *)

let rec get id l =
  match l with
  | [] -> None
  | (x, y) :: l' -> if x = id then Some y else get id l'

let rec get_index n l =
  match l with
  | [] -> assert false (* we suppose the index is correct *)
  | x :: l' -> if n = 0 then x else get_index (n-1) l'

(* !!!!!!!!!!!!!!!!!!!!!!!!! *)
(* The proof module should be rewritten from scratch *)
type proofrule =
  | PError
  | PQuit
  | PAbort
  | PBacktrack
  | PExact of term (* ; __ ; *)
  | PAbst1 (* dependent case *)
  | PAbst2 of string (* non-dependent case (the user has to input a variable name *)
  | PSConj
  | PSDisj of string * term * term
  | PProjL of term
  | PProjR of term
  | PInjL
  | PInjR

type path = Left | Middle | Right
