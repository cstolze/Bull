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
  | PExact of delta (* ; __ ; *)
  | PAbst1 (* dependent case *)
  | PAbst2 of string (* non-dependent case (the user has to input a variable name *)
  | PSConj
  | PSDisj of string * family * family
  | PProjL of family
  | PProjR of family
  | PInjL
  | PInjR

type path = Left | Middle | Right
