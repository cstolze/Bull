open Utils
open Bruijn

let find_printer env id =
  let rec aux l =
    match l with
    | [] -> None
    | (DefAxiom(id',_), _) | (DefLet(id',_,_), _) as t :: _
         when id = id' -> Some t
    | _ :: l' -> aux l'
  in aux env

(* for the print_all function *)
let rec to_id_list_const env =
  match env with
  | [] -> []
  | (DefAxiom(id',_), _) :: env | (DefLet(id',_,_), _) :: env ->
     id' :: to_id_list_const env

let rec to_id_list_var env =
  match env with
  | [] -> []
  | (DefAxiom(id',_)) :: env | (DefLet(id',_,_)) :: env ->
     id' :: to_id_list_var env

let find_const is_essence env id =
  match find_printer env id with
  | None -> None
  | Some(x,y) ->
     match if is_essence then y else x with
     | DefAxiom(_,t) -> Some (Const(dummy_loc, id), t)
     | DefLet(_,t1,t2) -> Some (t1,t2)

let is_const_new env id =
  match find_printer env id with
  | None -> true
  | _ -> false

let add_const env t ess =
  (t,ess) :: env

(* gives the term, term essence and type of the term of index n *)
let find_var ctx n =
  match List.nth ctx n with (* no exception (if the code is bug-free) *)
  | DefAxiom (_, t) ->
     Var(dummy_loc, n),
     lift 0 (n+1) t
  | DefLet (_, t1, t2) ->
     lift 0 (n+1) t1,
     lift 0 (n+1) t2

let add_var ctx t = t :: ctx
