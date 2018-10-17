open Utils
open Bruijn
open Reduction
open Subtyping
open Printer

let meta_add_sort (n,meta) l = ((n+1, IsSort n :: meta), {delta=Meta(l,n,[]);essence=Meta(l,n,[])})

let rec enumerate min max =
  if min > max then [] else
    min :: (enumerate (min+1) max)

let meta_add (n,meta) ctx t l =
  let s = List.map (fun n -> Var(dummy_loc,n))
                   (enumerate 0 (List.length ctx - 1)) in
  ((n+1, DefMeta (ctx, n, t) :: meta), {delta=Meta(l,n,s);essence=Meta(l,n,s)})

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
    | SubstEssence (l1, m, t1, t2) :: l
      -> if m = n then SubstEssence (l1, m, t1, t2) else foo l
  in
  foo meta

let is_instanced meta n =
  match get_meta meta n with
  | SubstSort _ | Subst _ -> true
  | _ -> false

(* let unification (meta : int * Utils.metadeclaration list *)
(*                 ) (env : Utils.declaration list *)
(*                   ) (t1 : Utils.fullterm) (t2 : Utils.term) = meta *)

(* we suppose is_instanced has returned true *)
let instantiate meta n l =
  match get_meta meta n with
  | SubstSort (m,s) -> s.delta
  | Subst (l1,m,t1,t2) -> apply_substitution t1.delta l
  | _ -> assert false

let rec solution (n,meta) m t =
  match meta with
  | [] -> []
  | IsSort a :: meta when a = m -> SubstSort (m,t) :: meta
  | DefMeta (ctx, a, t2) :: meta when a = m -> Subst(ctx, m, t, t2) :: meta
  | x :: meta -> x :: (solution (n,meta) m t)

(* TODO : 2 functions:
- unification_delta
- unification_essence

functions takes one term as input (not a fullterm)
 *)

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

(* returns true iff the free variables of t are in tl *)
let rec is_sane t tl =
  let tl' = List.map (fun n -> n+1) tl in
  match t with
  | Sort (_,t) -> true
  | Let (_,_,t1,t2,t3) -> is_sane t1 tl && is_sane t2 tl &&
                            is_sane t3 tl'
  | Prod (_,_,t1,t2) | Abs (_,_,t1,t2) -> is_sane t1 tl && is_sane t2 tl'
  | App (_,t1,l1) -> List.fold_left (fun x y -> x && is_sane y tl)
                                    (is_sane t1 tl) l1
  | Inter (_,t1,t2) | Union (_,t1,t2) | SPair (_,t1,t2)
    | SInLeft (_,t1,t2) | SInRight (_,t1,t2) | Coercion (_,t1,t2)
    -> is_sane t1 tl && is_sane t2 tl
  | SPrLeft (_,t1) | SPrRight (_,t1) -> is_sane t1 tl
  | SMatch (_,t1,t2,_,t3,t4,_,t5,t6) ->
     is_sane t1 tl && is_sane t2 tl && is_sane t3 tl && is_sane t4 tl'
     && is_sane t5 tl && is_sane t6 tl'
  | Const (_,_) -> assert false
  | Underscore _ -> assert false
  | Meta (_,_,l1) -> List.fold_left (fun x y -> x && is_sane y tl)
                                   true l1
  | Var (_,n) ->
     match tl with
     | [] -> true
     | x :: _ ->
        let min = List.fold_left (fun x y -> if x < y then x else y)
                                 x tl in
        let max = List.fold_left (fun x y -> if x > y then x else y)
                                 x tl in
        if n < min || n > max then true else
          List.mem n tl

let rec occur l n =
  match l with
  | [] -> assert false
  | m :: l -> if m = n then 0 else 1 + occur l n

(* fix the de Bruijn indices in the newly formed
terms of the context *)
(* the full environment is :
- list of global free variables (case n > max):
their indices are updated because some meta-context
variables are removed
- list of free meta-context variables:
the kept indices are stored in tl
- list of local bound variables (case n < min):
their indices do not change *)
let rec fix_intersect tl t =
  let tl' = List.map (fun n -> n+1) tl in
  match t with
  | Var (l, n) ->
     begin
       match tl with
       | [] -> Var(l, n)
       | x :: _ ->
          let min = List.fold_left (fun x y -> if x < y then x else y)
                                 x tl in
          let max = List.fold_left (fun x y -> if x > y then x else y)
                                   x tl in
          if n < min then
            Var(l, n) else
            if n > max then
              Var(l, n + min - max + List.length tl - 1)
            else
              Var(l,min + occur tl n)
     end
  | _ -> visit_term (fix_intersect tl) (fun _ -> fix_intersect tl')
                    (fun id _ -> id) t

let rec intersect ctx l1 l2 =
  match ctx, l1, l2 with
  | [], [], [] -> [], []
  | a :: ctx, x :: l1, y :: l2
    -> let ctx, tl = intersect ctx l1 l2 in
       let tl = List.map (fun n -> n + 1) tl in
       if same_term x y then
         ctx, tl
       else
         if is_sane x tl then
           match a with
           | DefAxiom (id, t) ->
              DefAxiom(id, {delta=fix_intersect tl t.delta;
                       essence=fix_intersect tl t.essence}) :: ctx, 0 :: tl
           | DefEssence (id, t1, t2) ->
              DefEssence(id, fix_intersect tl t1
                         , {delta=fix_intersect tl t2.delta;
                            essence=fix_intersect
                                      tl t2.essence}) :: ctx,
              0 :: tl
           | DefLet (id, t1, t2) ->
              DefLet(id, {delta=fix_intersect tl t1.delta;
                          essence=fix_intersect tl t1.essence},
                     {delta=fix_intersect tl t2.delta;
                      essence=fix_intersect tl t2.essence}) :: ctx,
              0 :: tl
         else
           ctx, tl
  | _ -> assert false

(* TODO *)
let meta_same (n, meta) m ctx l1 l2 =
  let ctx, tl = intersect ctx l1 l2 in
  let meta = (n+1, DefMeta (ctx, n, ???) :: meta) in
  let s = List.map (fun n -> Var(dummy_loc,n))
                   tl in
  solution meta m {delta=Meta(dummy_loc, n, s); essence=Meta(dummy_loc, n, s)}

let unification meta env t1 t2 =
  let norm t =
    let t = apply_all_substitution meta t
    in
    strongly_normalize env t
  in
  let t1 = norm t1 in
  let t2 = norm t2 in
  let rec foo meta env t1 t2 =
    match (t1,t2) with
    (* Meta-redL *)
    | Meta(l,n,s), _ when is_instanced meta n ->
       foo meta env (instantiate meta n s) t2
    | App(l,Meta(l',n,s),t'), _ when is_instanced meta n ->
       foo meta env (norm @@ App(l, instantiate meta n s, t')) t2
    (* Meta-redR *)
    | _, Meta(l,n,s) when is_instanced meta n ->
       foo meta env t1 (instantiate meta n s)
    | _, App(l,Meta(l',n,s),t') when is_instanced meta n ->
       foo meta env t1 (norm @@ App(l, instantiate meta n s, t'))
    (* Meta-Same-Same and Meta-Same *)
    | Meta(l,n,s1), Meta(l',m,s2) when m = n ->
       (* Meta-Same-Same *)
       if same_list s1 s2 then meta else
         (* Meta-Same *)
         failwith "Meta-Same 1 not implemented"
    | App(l,Meta(l',n,s1),t1), App(ll,Meta(ll',m,s2), t2) ->
       (* Meta-Same-Same *)
       if same_list s1 s2 then
         bar meta env t1 t2
       else
         (* Meta-Same *)
         failwith "Meta-Same 2 not implemented"
    | Sort(l,t1), Sort(_,t2) -> if t1 = t2 then meta
                                else raise (Err "Sort")
    | Prod(l,id,t1,t2), Prod(_,_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta (DefAxiom(id,{delta=t1;essence=nothing}) :: env) t2 t2' in
       meta
    | Abs(l,id,t1,t2), Abs(_,_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta (DefAxiom(id,{delta=t1;essence=nothing}) :: env) t2 t2' in
       meta
    | Inter(l,t1,t2), Inter(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | Union(l,t1,t2), Union(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SPair(l,t1,t2), SPair(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SPrLeft(l,t1), SPrLeft(_,t1') ->
       let meta = foo meta env t1 t1' in
       meta
    | SPrRight(l,t1), SPrRight(_,t1') ->
       let meta = foo meta env t1 t1' in
       meta
    | SInLeft(l,t1,t2), SInLeft(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SInRight(l,t1,t2), SInRight(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | Coercion(l,t1,t2), Coercion(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
  | Var(l,x), Var(_,y) -> if x = y then meta else raise (Err "Var")
  | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6),
    SMatch (_, t1', t2', _, t3', t4', _, t5', t6') ->
     let meta = foo meta env t1 t1' in
     let meta = foo meta env t2 t2' in
     let meta = foo meta env t3 t3' in
     let meta = foo meta env t4 t4' in
     let meta = foo meta env t5 t5' in
     let meta = foo meta env t6 t6' in
     meta
  | Const (_,_), _ | _, Const (_,_)
    | Underscore _, _ | _, Underscore _
    | Let (_,_,_,_,_), _ | _, Let (_,_,_,_,_) -> assert false
  | App(l,t1,l2), App(_,t1',l2') ->
     if List.length l2 = List.length l2' then
       try
         let meta = foo meta env t1 t1' in
         bar meta env l2 l2'
       with
       | _ -> failwith "Not implemented 1"
     else
       failwith "Not implemented 2"
  | Meta (l, n, s), t | t, Meta (l, n, s) ->
     failwith "Not implemented 3"
       (* TODO: find if meta has already been instantiated
        if yes, unify instantiate(meta) and t. Other case: pattern *)
  | _ -> failwith "Not implemented 4"
  and bar meta env l l' =
    match l, l' with
    | x :: l, y :: l' -> let meta = foo meta env x y
                         in bar meta env l l'
    | [], [] -> meta
    | _ -> assert false
  in
  foo meta env t1 t2

let unification meta env t1 t2 = meta
