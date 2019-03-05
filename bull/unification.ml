open Utils
open Bruijn
open Reduction
open Printer

(* TODO: move the basic meta-env functions to env.ml *)

type env_meta = int * metadeclaration list

let get_meta (_,meta) n =
  let rec foo = function
    | [] -> assert false
    | IsSort m :: l ->
       if m = n then IsSort n else foo l
    | DefMeta (l1, m, t) :: l -> if m = n then DefMeta (l1, m, t) else
                                   foo l
    | SubstSort (m,s) :: l -> if m = n then SubstSort (m,s) else foo l
    | Subst (l1,m,t1,t2) :: l -> if m = n then Subst (l1, m, t1, t2)
                                 else foo l
  in
  foo meta

(* returns the type of a term *)
let get_from_meta meta l n subst =
  match get_meta meta n with
  | IsSort n -> raise (Err "should not happen? 1")
  | SubstSort (n,Sort(l,Type)) -> meta, Sort(l,Type), Sort(l,Kind)
  | SubstSort (n,_) -> raise (Err "should not happen? 2")
  | DefMeta (l1,n,t2) | Subst (l1,n,_,t2)
    -> (meta, Meta(l,n,subst), apply_substitution t2 subst)

let meta_add_sort (n,meta) l = ((n+1, IsSort n :: meta), Meta(l,n,[]))

(* enumerate a b == [a;a+1;a+2;...;b-1;b] *)
let rec enumerate min max =
  if min > max then [] else
    min :: (enumerate (min+1) max)

let meta_add (n,meta) ctx t l =
  let s = List.map (fun n -> Var(dummy_loc,n))
                   (enumerate 0 (List.length ctx - 1)) in
  ((n+1, DefMeta (ctx, n, t) :: meta), Meta(l,n,s))

let is_instanced meta n =
  match get_meta meta n with
  | SubstSort _ | Subst _ -> true
  | _ -> false

(* let unification (meta : int * Utils.metadeclaration list *)
(*                 ) (env : Utils.declaration list *)
(*                   ) (t1 : Utils.fullterm) (t2 : Utils.term) = meta *)

(* we suppose is_instanced has returned true *)
(* compute definition expansion of ?n[l] *)
let instantiate meta n l =
  match get_meta meta n with
  | SubstSort (m,s) -> s
  | Subst (l1,m,t1,t2) -> apply_substitution t1 l
  | _ -> assert false

(* replace Ctx |- ?m : T with Ctx |- ?m := t : T in the meta-environment *)
let rec solution (n,meta) m t =
  match meta with
  | [] -> []
  | IsSort a :: meta when a = m -> SubstSort (m,t) :: meta
  | DefMeta (ctx, a, t2) :: meta when a = m -> Subst(ctx, m, t, t2)
                                                 :: meta
  | x :: meta -> x :: (solution (n,meta) m t)

(* META-SAME-SAME *)
(* This is a helper function that checks if t1 and t2 are the same term *)
let rec same_term t1 t2 =
  match t1, t2 with
  | Sort(l,t1), Sort(_,t2) -> if t1 = t2 then true
                              else false
  | Prod(l,_,t1,t2), Prod(_,_,t1',t2') | Abs(l,_,t1,t2), Abs(_,_,t1',t2') | Inter(l,t1,t2), Inter(_,t1',t2') | Union(l,t1,t2), Union(_,t1',t2') | SPair(l,t1,t2), SPair(_,t1',t2') | SInLeft(l,t1,t2), SInLeft(_,t1',t2') | SInRight(l,t1,t2), SInRight(_,t1',t2') | Coercion(l,t1,t2), Coercion(_,t1',t2') ->
     if same_term t1 t1' then
       same_term t2 t2'
     else false
  | App(l, t1, l1), App(_, t1', l1') ->
     if same_term t1 t1' then
       same_list l1 l1'
     else false
  | SPrLeft(l,t1), SPrLeft(_,t1') | SPrRight(l,t1), SPrRight(_,t1') ->
     same_term t1 t1'
  | Var(l,x), Var(_,y) -> x = y
  | Meta(l,n,s1), Meta(_,m,s2) ->
     if m = n then
       same_list s1 s2
     else false
  | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6),
    SMatch (_, t1', t2', _, t3', t4', _, t5', t6') ->
     if same_term t1 t1' then
       if same_term t2 t2' then
         if same_term t3 t3' then
           if same_term t4 t4' then
             if same_term t5 t5' then
               same_term t6 t6'
             else false
           else false
         else false
       else false
     else false
  | _ -> false
and same_list s1 s2 =
  match s1, s2 with
  | [], [] -> true
  | x :: s1, y :: s2 -> if same_term x y then same_list s1 s2
                        else false
  | _ -> false

(* META-SAME *)

(* fix the de Bruijn indices in the newly formed
terms of the context *)
let fix_indices f t =
  (map_term 0 (fun k l m -> Var(l, f k m))) t

(*
 Solve ctx |- ?m : t with ctx |- ?m := ?n[tl] : t,
 where ?n is the pruned version of ?m. The l argument is a bool list
 stating which variable is kept.
*)
let create_pruned (n,meta) ctx m t l =
  let default_fix_indices k m = m in
  (* create new context, new subst list, and fix-indices function *)
  let rec foo ctx l =
    match ctx, l with
    | [], [] -> [], [], default_fix_indices
    | a :: ctx, b :: l ->
       let ctx, tl, f = foo ctx l in
       let ctx =
         if b then (* variable is kept *)
           let a = (* fix the indices in a *)
               match a with
               | DefAxiom (id, t) ->
                  DefAxiom (id, fix_indices f t)
               | DefLet (id, t1, t2) ->
                  DefLet (id, fix_indices f t1, fix_indices f t2)
           in a :: ctx
         else
           ctx
       in
       let tl = List.map (fun n -> n + 1) tl in
       let tl = if b then 0 :: tl else tl in
       (* new function for fixing indices *)
       let f k m = if b then (* variable is kept *)
                     if m < k then m (* bound variable *)
                     else if m = k then k
                     else f k (m-1) + 1
                   else (* the variable is pruned *)
                     if m < k then m (* bound variable *)
                                     (* case k = m should not happen *)
                     else f k (m-1)
       in ctx, tl, f
    | _ -> assert false
  in
  let ctx, tl, f = foo ctx l in
  let t = fix_indices f t in
  let meta = DefMeta (ctx, n, t) :: meta in
  (n+1, solution (n+1, meta) m (Meta(dummy_loc, n, List.map (fun n -> Var(dummy_loc, n)) tl)))

(* find the common terms in substitution s1 and s2 *)
let rec intersection s1 s2 =
  match s1, s2 with
  | [], [] -> []
  | x :: s1, y :: s2 ->
     same_term x y :: intersection s1 s2
  | _ -> assert false

let meta_same meta n s1 s2 =
  match get_meta meta n with
  | DefMeta (ctx, _, t) ->
     let l = intersection s1 s2 in
     create_pruned meta ctx n t l
  | _ -> failwith "should not happen meta-same"

(* HIGHER ORDER PATTERN UNIFICATION *)

(* check if the arguments are all distinct variables *)
let rec strong_pattern tl aux =
  match tl with
  | [] -> aux
  | Var (_,n) :: tl ->
     begin
       try
         ignore @@ List.find (fun m -> m = n) aux; raise (Err "HOPU impossible")
       with
       | Not_found -> strong_pattern tl (n :: aux)
     end
  | _ -> raise (Err "HOPU impossible")

let rec is_offending ctx m xi t =
  match t with
  | Sort (l,m) -> true
  | Let (l1,id,t1,t2,t3) -> assert false
  | Prod (l,id,t1,t2) | Abs (l,id,t1,t2) ->
     is_offending ctx m xi t1 &&
       is_offending (DefAxiom(id,t1) :: ctx) m (List.map (fun x -> x+1) xi) t2
  | App (l,t1,l1) ->
     List.fold_left
       (fun meta t -> is_offending ctx m xi t)
       (is_offending ctx m xi t1)
       l1
  | Inter (l,t1,t2) | Union (l,t1,t2) | SPair (l,t1,t2)
    | SInLeft (l,t1,t2) | SInRight (l,t1,t2) | Coercion (l,t1,t2) ->
     is_offending ctx m xi t1 &&
       is_offending ctx m xi t2
  | SPrLeft (l,t) | SPrRight (l,t) ->
     is_offending ctx m xi t
  | SMatch (l,t1,t2,id1,t3,t4,id2,t5,t6) ->
     is_offending ctx m xi t1 &&
       is_offending ctx m xi t2 &&
         is_offending ctx m xi t3 &&
           is_offending (DefAxiom(id1,t3)::ctx) m (List.map (fun x -> x+1) xi) t4 &&
             is_offending ctx m xi t5 &&
               is_offending (DefAxiom(id2,t5)::ctx) m (List.map (fun x -> x+1) xi) t6
  | Var (l,n) -> if n < List.length ctx then
                   begin
                    try
                      ignore @@ List.find (fun m -> m = n) xi;
                      true
                    with
                    | Not_found -> false
                   end
                 else true
  | Const (l,id) -> true
  | Underscore l -> true
  | Meta (l,n,s) -> if m = n then false
                    else
                      List.fold_left (fun x y -> x && is_offending ctx m xi y)
                        true s

let norm is_essence meta env ctx t =
  let t = apply_all_substitution meta t
  in
  strongly_normalize is_essence env ctx t

(* update the meta-environment, in order to remove all offending terms from t *)
(* raise Not_found in case of error *)
let rec prune is_essence meta env ctx m xi t =
  let t =  norm is_essence meta env ctx t in
  match t with
  | Sort (l,m) -> meta
  | Let (l1,id,t1,t2,t3) -> assert false
  | Prod (l,id,t1,t2) | Abs (l,id,t1,t2) ->
     let meta = prune is_essence meta env ctx m xi t1 in
     prune is_essence meta env (Env.add_var ctx (DefAxiom(id,t1))) m (0 :: (List.map (fun x -> x+1) xi)) t2
  | App (l,t1,l1) ->
     List.fold_left
       (fun meta t -> prune is_essence meta env ctx m xi t)
       (prune is_essence meta env ctx m xi t1)
       l1
  | Inter (l,t1,t2) | Union (l,t1,t2) | SPair (l,t1,t2)
    | SInLeft (l,t1,t2) | SInRight (l,t1,t2) | Coercion (l,t1,t2) ->
     let meta = prune is_essence meta env ctx m xi t1 in
     prune is_essence meta env ctx m xi t2
  | SPrLeft (l,t) | SPrRight (l,t) ->
     prune is_essence meta env ctx m xi t
  | SMatch (l,t1,t2,id1,t3,t4,id2,t5,t6) ->
     let meta = prune is_essence meta env ctx m xi t1 in
     let meta = prune is_essence meta env ctx m xi t2 in
     let meta = prune is_essence meta env ctx m xi t3 in
     let meta = prune is_essence meta env
                  (Env.add_var ctx (DefAxiom(id1,t3))) m (List.map (fun x -> x+1) xi) t4 in
     let meta = prune is_essence meta env ctx m xi t5 in
     prune is_essence meta env (Env.add_var ctx (DefAxiom(id2,t5))) m (List.map (fun x -> x+1) xi) t6
  | Var (l,n) -> (if n < List.length ctx then
                    ignore @@ List.find (fun m -> m = n) xi);
                 meta
  | Const (l,id) -> meta
  | Underscore l -> meta
  | Meta (l,n,s) -> if m = n then raise Not_found
                    else
                      let l = List.map (is_offending ctx m xi) s in
                      try
                        ignore @@ List.find (fun m -> m = false) l;
                        match get_meta meta n with (* we have to prune n *)
                        | DefMeta (ctx, _, t) ->
                           create_pruned meta ctx n t l
                        | _ -> failwith "should not happen prune"
                      with
                      | Not_found ->
                         meta (* nothing to do *)

let rec create_hopu ctx t xi n =
  let update x k l n =
    if n = x+k then Var (l,0)
    else Var(l,n+1) in
  match xi with
  | [] -> t
  | x :: xi ->
     let (_, tt) = Env.find_var ctx x in
     let t = map_term 0 (update x) t in (* replace x by Var 0 *)
     let ctx = map_context 0 (update x) ctx in (* same, but in the context *)
     if n <> 0 then
       Abs(dummy_loc,"x",tt, create_hopu (DefAxiom("",tt)::ctx) t (List.map (fun x -> x+1) xi) (n-1))
     else
       create_hopu (DefAxiom("",tt)::ctx) t (List.map (fun x -> x+1) xi) 0

(* dummy *)
let meta_inst is_essence meta env ctx t n s1 t1 =
  let xi = strong_pattern (List.concat [t1;s1]) [] in
  let meta = prune is_essence meta env ctx n xi t in
  let t = norm is_essence meta env ctx t in
  let res = create_hopu ctx t xi (List.length t1) in
  (n, solution meta n res)

(* MAIN UNIFICATION ALGORITHM *)

let unification is_essence meta env ctx t1 t2 =
  let norm = norm is_essence in
  let t1 = norm meta env ctx t1 in
  let t2 = norm meta env ctx t2 in
  let rec foo meta ctx t1 t2 =
    match (t1,t2) with
    (* Hack so we can suppose meta-vars are always
       head-terms of some spine *)
    | Meta(l,n,s), t -> foo meta ctx (App (l, Meta(l,n,s), [])) t
    | t, Meta(l,n,s) -> foo meta ctx t (App (l, Meta(l,n,s), []))
    (* in the foo loop, the terms are supposed to be in normal form,
       except when meta-variables are instanced. We do the corresponding
     reductions first. *)
    (* Meta-redL *)
    | App(l,Meta(l',n,s),t'), _ when is_instanced meta n ->
       foo meta ctx (norm meta env ctx @@ app' l (instantiate meta n s) t') t2
    (* Meta-redR *)
    | _, App(l,Meta(l',n,s),t') when is_instanced meta n ->
       foo meta ctx t1 (norm meta env ctx @@ app' l (instantiate meta n s) t')

    (* Unifying twice the same meta-variable. *)
    (* Meta-Same-Same and Meta-Same *)
    | App(l,Meta(l',n,s1),t1), App(ll,Meta(ll',m,s2), t2) when m = n ->
       (* Meta-Same-Same *)
       if same_list s1 s2 then
         bar meta ctx t1 t2
       else
         (* Meta-Same *)
         let meta = meta_same meta n s1 s2 in
         bar meta ctx t1 t2

    (* Unifying a meta-variable with another term *)
    | t, App(l,Meta(l',n,s1),t1) ->
       (* not implemented: Meta-DelDeps (future work) *)
       begin
         try meta_inst is_essence meta env ctx t n s1 t1 with
         | Err _ ->
            match t with
            | App(_,t,l2) -> (* first-order unification *)
               if List.length l2  = List.length t1 then
                 let meta = foo meta ctx t (App(l,Meta(l',n,s1),[])) in
                 bar meta ctx l2 t1
               else raise (Err "not unifiable")
            | _ -> raise (Err "not unifiable")
       end
    | App(l,Meta(l',n,s1),t1), t ->
       begin
         try meta_inst is_essence meta env ctx t n s1 t1 with
         | Err _ ->
            match t with (* first-order unification *)
            | App(_,t,l2) ->
               if List.length l2  = List.length t1 then
                 let meta = foo meta ctx (App(l,Meta(l',n,s1),[])) t in
                 bar meta ctx t1 l2
               else raise (Err "not unifiable")
            | _ -> raise (Err "not unifiable")
       end

    (* Structural unification *)
    | Sort(l,t1), Sort(_,t2) -> if t1 = t2 then meta
                                else raise (Err "Sort")
    | Prod(l,id,t1,t2), Prod(_,_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta (DefAxiom(id,t1) :: ctx) t2 t2' in
       meta
    | Abs(l,id,t1,t2), Abs(_,_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta (DefAxiom(id,t1) :: ctx) t2 t2' in
       meta
    | Inter(l,t1,t2), Inter(_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta ctx t2 t2' in
       meta
    | Union(l,t1,t2), Union(_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta ctx t2 t2' in
       meta
    | SPair(l,t1,t2), SPair(_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta ctx t2 t2' in
       meta
    | SPrLeft(l,t1), SPrLeft(_,t1') ->
       let meta = foo meta ctx t1 t1' in
       meta
    | SPrRight(l,t1), SPrRight(_,t1') ->
       let meta = foo meta ctx t1 t1' in
       meta
    | SInLeft(l,t1,t2), SInLeft(_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta ctx t2 t2' in
       meta
    | SInRight(l,t1,t2), SInRight(_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta ctx t2 t2' in
       meta
    | Coercion(l,t1,t2), Coercion(_,t1',t2') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta ctx t2 t2' in
       meta
    | Var(l,x), Var(_,y) -> if x = y then meta else raise (Err "Var")
    | Const(l,x), Const(_,y) -> if x = y then meta else raise (Err "Const")
    | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6),
      SMatch (_, t1', t2', _, t3', t4', _, t5', t6') ->
       let meta = foo meta ctx t1 t1' in
       let meta = foo meta ctx t2 t2' in
       let meta = foo meta ctx t3 t3' in
       let meta = foo meta (DefAxiom(id1,t3)::ctx) t4 t4' in
       let meta = foo meta ctx t5 t5' in
       let meta = foo meta (DefAxiom(id2,t5)::ctx) t6 t6' in
       meta

    | Underscore _, Underscore _ -> meta (* case where we want to unify
                                          nothing and nothing *)
    | Let (_,_,_,_,_), _ | _, Let (_,_,_,_,_) -> assert false

    (* first-order unification for applications *)
    | App(l,t1,l2), App(_,t1',l2') -> (* t1 and t1' are not meta-variables *)
       if List.length l2 = List.length l2' then
         let meta = foo meta ctx t1 t1' in
         bar meta ctx l2 l2'
       else raise (Err "not unifiable")

    (* eta-expansion if only one term is a lambda-abstraction *)
    | t, Abs(l,id,t1,t2) -> (* t's head is not an abstraction *)
       foo meta (DefAxiom(id,t1) :: ctx) (app dummy_loc t (Var(dummy_loc, 0))) t2
    | Abs(l,id,t1,t2), t -> (* t's head is not an abstraction *)
       foo meta (DefAxiom(id,t1) :: ctx) t2 (app dummy_loc t (Var(dummy_loc, 0)))

    (* other cases *)
    | _ -> raise (Err "not unifiable")

  and bar meta ctx l l' =
    match l, l' with
    | x :: l, y :: l' -> let meta = foo meta ctx x y
                         in bar meta ctx l l'
    | [], [] -> meta
    | _ -> assert false
  in
  foo meta ctx t1 t2
