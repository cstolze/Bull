(* sorts *)
type sort = Type | Kind

(* Core type *)
(* Note: the Meta variables are useless till we implement a refiner *)
type term =
  | Sort of sort
  | Let of string * term * term
  | Prod of string * term * term
  | Abs of string * term * term
  | Subset of string * term * term
  | Subabs of string * term * term
  | App of term * term
  | Inter of term * term
  | Union of term * term
  | SPair of term * term
  | SPrLeft of term
  | SPrRight of term
  | SMatch of term * term * term
  | SInLeft of term * term
  | SInRight of term * term
  | Coercion of term * term
  | Var of int (* bruijn index *)
  | Const of string (* variable name *)
  | Omega
  | Meta of int

(* In the contexts, there are let-ins and axioms *)
type declaration =
  | DefAxiom of term
  (* term * essence * type *)
  | DefLet of term * term * term


type loc =
  | Locnode of Lexing.position * Lexing.position * loc list

(* Commands from the REPL *)
type sentence =
  | Quit
  | Load of string
  | Proof of string * loc * term
  | Axiom of string * loc * term
  | Definition of string * loc * term * ((loc * term) option)
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
