open Utils
open Reduction

(* returns the essence and the type of a term *)
(* TODO : ERROR HANDLING (see the parser) *)

(*
  | Type : (Type, Kind)
  | Let id,t1,t2 : ((Let id, e1, e2),T2), where t1:(e1,T1) and G, (t1, e1, T1) |- t2: (e2,T2)
  | Prod id,t1,t2 : ((Prod id, Omega, e2), PTS(s1,s2)) where t1:(e1,s1) and G, (Var 0, e1, s1) |- t2 : (e2, s2)
  | Abs id, t1, t2 : ((Abs id, Omega, e2), (Prod id, T1, T2)) where G, (Var 0, Var 0, T1) |- t2 : (e2, T2), and (Prod id, T1, T2) : (_, s)
  | Subset id, t1, t2 : ((Subset id, Omega, e2), s) where t1:(e1, s) and t2:(e2,s)
  | Subapp id, t1, t2 : ((Subapp id, Omega, e2), Subset id, T1, T2) where G, (Var 0, Var 0, T1) |- t2 : (e2, T2), and (Subset id, T1, T2) : (_, s) and e2 == Var 0
  | App t1, t2 : let t1 : (e1, T1) and t2 : (e2, T2) in: if T1 == Prod(id, T2, T3) then (e1 e2, T3), else if T1 == Subset (id, T2, T3) then (e2, T3)
  | Inter t1, t2 : ((Inter e1, e2), Type) where t1 : (e1, Type) and t2 : (e2, Type)
  | Union t1, t2 : ((Union e1, e2), Type) where t1 : (e1, Type) and t2 : (e2, Type)
  | SPair t1, t2 : (e1, (Inter T1, T2)) where t1 : (e1, T1) and t2 : (e2, T2) and e1 == e2 and (Inter T1, T2) : s
  | SPrLeft t1 : (e1, T1) where t1 : (e1, Inter (T1, T2))
  | SPrRight t2 : (e1, T2) where t1 : (e1, Inter (T1, T2))
  | SMatch t1, t2 : (e1, (Prod id1, (Union T1, T2), T3)) where t1 : (e1, Prod id1, T1, T3_1) and t2 : (e2, Prod id2, T2, T3_2) and e1 == e2 and ????? and (Union T1, T2), T3) : (_, Type)
  | SInLeft t1, t2 : (e2, Union (T2, t1)) where t1 : (_, Type) and t2 : (e2, T2)
  | SInRight t1, t2 : (e2, Union (t1, T2)) where t1 : (_, Type) and t2 : (e2, T2)
  | Coercion t1, t2 : (e2, t1) where t1 : (_, Type) and t2 : (e2, T2) and T2 < t1
  | Var n : look for n in gamma
  | Omega : (Omega, Type)
    *)


let type_of_sort s =
  match s with
  | Type -> Result.Ok (Type, Kind)
  | Kind -> assert false

(* returns the sort of Pi x : A. B, where A:s1 and b:s2 *)
let principal_type_system s1 s2 =
  match (s1, s2) with
  | (Type, Type) -> Some Type (* terms depending on terms *)
  | (Type, Kind) -> Some Kind (* types depending on terms *)
  | _ -> None (* we are doing lambdaP (aka LF) for now *)

let type_prod id (e1,t1) (e2,t2) =
  match (t1, t2) with
  | (Sort s1, Sort s2) -> (match principal_type_system s1 s2 with
    | Some s -> Result.Ok (Prod(id, e1, e2), s)
    | None -> Result.Error "TODO (type_prod)")
  | _ -> Result.Error "TODO (type_prod 2)"

let reconstruction gamma str l t =
  Result.Ok (Meta 1, Meta 2, Meta 3) (* TO FIX *)

let check_axiom gamma str l t =
  Result.Ok (Meta 1) (* TO FIX *)


(*let type_abs id (e1,t1) (e2,t2) =
  Result.Ok (Abs(id,e1,e2), Prod(id,t1,t2)) (* no *)

let rec reconstruction id_list gamma t =
  let bind f e = Result.bind (e,t) f in
  let bind2 f e1 e2 = bind (bind f e1) e2 in
  let binder_rule aux id1 t1 t2 = bind2 (aux id1) (reconstruction gamma t1) (reconstruction ((DefAxiom t1)::gamma) t2) in
  let normal_rule aux t1 t2 = bind2 aux (reconstruction gamma t1) (reconstruction gamma t2) in
  let proj_rule aux t1 = bind aux (reconstruction gamma t1)
  let 
  match t with
  | Sort s -> type_of_sort s
  | Let (id1, t1, t2) ->
    bind (fun (e,t) -> reconstruction (DefLet (t1, e, t)::gamma) t2) (reconstruction gamma t2)
  | Prod (id1, t1, t2) -> binder_rule type_prod id1 t1 t2
  | Abs (id1, t1, t2) -> binder_rule type_abs id1 t1 t2
  | Subset (id1, t1, t2) -> binder_rule type_subset id1 t1 t2
  | Subapp (id1, t1, t2) -> binder_rule type_subapp id1 t1 t2
  | App (t1, t2) -> normal_rule type_app t1 t2
  | Inter (t1, t2) -> normal_rule type_inter t1 t2
  | Union (t1, t2) -> normal_rule type_union t1 t2
  | SPair (t1, t2) -> normal_rule type_spair t1 t2
  | SPrLeft t1 -> proj_rule type_sprleft t1
  | SPrRight t1 -> proj_rule type_sprright t1
  | SMatch (t1, t2) -> normal_rule type_smatch t1 t2
  | SInLeft (t1, t2) -> normal_rule type_sinleft t1 t2
  | SInRight (t1, t2) -> normal_rule type_sinright t1 t2
  | Coercion (t1, t2) -> Result.Error ("TODO")
  | Var n -> let (_, e, t) = get_from_context gamma n in Result.Ok (e,t)
  | Const id1 -> Result.Error ("TODO (unknown variable)")
  | Omega -> Result.Ok (Omega, Type)
  | Meta n -> Result.Error ("We don't manage meta variables for now.")
 *)
