open Utils
open Bruijn
open Reduction
open Subtyping
open Printer
open Unification

let type_of_sort s =
  match s with
  | Type -> Some (dummy_loc, Kind)
  | Kind -> None

(* returns the sort of Pi x : A. B, where A:s1 and b:s2 *)
(* pre-condition: s1 and s2 have to be sorts (or sort meta-vars) *)
let principal_type_system meta env ctx s1 s2 =
  match (s1, s2) with
  | (Sort (_,Type), t) -> (meta, t)
  | (t1, t2) ->
     let meta = unification false meta env ctx t1
                            (Sort(dummy_loc,Type))
     in (meta, t2)

(* same as principal type system, but for A | B and A & B *)
let principal_set_system meta env ctx s1 s2 =
  match (s1, s2) with
  | (Sort (_,Type), Sort(l,Type)) -> (meta, Sort(l,Type))
  | (t1, t2) ->
     let meta = unification false meta env ctx t1 (Sort(dummy_loc,Type))
     in
     let meta = unification false meta env ctx t2 (Sort(dummy_loc,Type))
     in (meta, Sort(dummy_loc,Type))

(*
  force-type takes is like reconstruct, except that
it forces the returned type to be either Type, Kind, or a meta-variable with
the property is_sort
 *)

(*
  a meta-variable environment is a list of either
  - a context, a meta-variable identifier, and a type
  - a context, and the constraint is-a-sort(meta-variable identifier)

The meta-variable environment comes with an integer being the maximum meta-var id in the list
(in case we have to add a new id)
 *)
(*
  a substitution is a list of:
  - context, meta-var id, term, type ( \Gamma \vdash id := term : type )
 *)

let rec reconstruct meta env ctx t
        : ((int * Utils.metadeclaration list) * Utils.term
           * Utils.term) =
  let unification = unification false in
  let strongly_normalize = strongly_normalize false in
  let err = err ctx in
  match t with

  | Sort (l, s) ->
     begin
       match type_of_sort s with
       | Some (l,s) -> (meta, t, Sort (l,s))
       | None -> err @@ Kind_Error
     end

  | Let (l, id, t1, t2, t3) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct_with_type
                             meta env ctx t2 t1 in
     let decl = DefLet(id, t2, t2') in
     let (meta, t3, t3') =
       reconstruct meta env (decl :: ctx) t3 in
     (meta, Let(l, id, t2', t2, t3), beta_redex t3' t2)

  | Prod (l, id, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') =
       let decl = DefAxiom(id, t1) in
       force_type meta env (decl :: ctx) t2 in
     begin
       try
         let (meta, tt) = principal_type_system meta env ctx t1' t2' in
         (meta, Prod(l,id,t1,t2), tt)
       with
       | Unif_Error -> err @@ Prod_Error(l)
     end

  | Abs (l, id, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') =
       let decl = DefAxiom(id, t1) in
       reconstruct meta env (decl :: ctx) t2 in
     let (meta,typ,_) = force_type meta env ctx (Prod (l, id, t1, t2')) in
     (meta, Abs(l, id, t1, t2), typ)

  | App (l, t1, l2) ->
     begin
       match l2 with
       | [] -> reconstruct meta env ctx t1
       | t2 :: l2 ->
          let (meta, t1, t1') = reconstruct meta env ctx (App (l,t1,l2)) in
          let t1, l2 =
            match t1 with
            | App(_, t1, l2) -> t1, l2
            | _ -> t1, []
          in
          let t1' = strongly_normalize env ctx @@ apply_all_substitution meta t1' in
          begin
            match t1' with
            | Prod (_, _, u1, u2) -> (* case 1: we know the type of t1 *)
               let (meta, t2, t2') =
                 reconstruct_with_type meta env ctx t2 u1 in
               (meta, App(l, t1, t2 :: l2),
                beta_redex u2 t2)
            | _ -> (* case 2: we do not know the type of t1 *)
               let (meta, t2, t2') = reconstruct meta env ctx t2 in
               let (meta, s) = meta_add_sort meta dummy_loc in
               let (meta, k) = meta_add meta ctx s dummy_loc in
               try
                 let meta = unification
                              meta env ctx t1' (Prod(l, "x", t2',
                                                     k)) in
                 (meta, App(l, t1, t2 :: l2), beta_redex k t2)
               with
               | Unif_Error -> err @@ App_Error(l, t1, t1', t2, t2')
          end
     end

  | Inter (l, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = force_type meta env ctx t2 in
     begin
       try
         let (meta, tt) = principal_set_system meta env ctx t1' t2' in
         (meta, Inter(l,t1,t2), tt)
       with
       | Unif_Error -> err @@ Set_Error l
     end

  | Union (l, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = force_type meta env ctx t2 in
     begin
       try
         let (meta, tt) = principal_set_system meta env ctx t1' t2' in
         (meta, Union(l,t1,t2), tt)
       with
       | Unif_Error -> err @@ Set_Error l
     end

  | SPair (l, t1, t2) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let (meta, t2, t2') = reconstruct meta env ctx t2 in
     let (meta, t', _) = force_type meta env ctx (Inter (l, t1', t2')) in
     (meta, SPair(l,t1,t2), t')
  (* TODO: rewrite the rules for SPrLeft and SPrRight so that the
     knowledge that the argument is an intersection is propagated *)
  | SPrLeft (l, t1) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let t1' = strongly_normalize env ctx @@ apply_all_substitution meta t1 in
     begin
       match t1' with
       | Inter(l,t',_) ->
          (meta, SPrLeft(l,t1), t')
       | _ ->
          let (meta, s) = meta_add_sort meta dummy_loc in
          let (meta, a) = meta_add meta ctx s dummy_loc in
          let (meta, b) = meta_add meta ctx s dummy_loc in
          try
            let meta = unification meta env ctx t1' (Inter(l,a,
                                                           b)) in
            (meta, SPrLeft(l,t1), a)
          with
          | Unif_Error -> err @@ Proj_Error(l,t1,t1')
     end
  | SPrRight (l, t1) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let t1' = strongly_normalize env ctx @@ apply_all_substitution meta t1 in
     begin
       match t1' with
       | Inter(l,_,t') ->
          (meta, SPrRight(l,t1), t')
       | _ ->
          let (meta, s) = meta_add_sort meta dummy_loc in
          let (meta, a) = meta_add meta ctx s dummy_loc in
          let (meta, b) = meta_add meta ctx s dummy_loc in
          try
            let meta = unification meta env ctx t1' (Inter(l,a,
                                                           b)) in
            (meta, SPrRight(l,t1), b)
          with
          | Unif_Error -> err @@ Proj_Error(l,t1,t1')
     end

  | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let (meta, t2, t2') =
       reconstruct_with_type meta env ctx t2 (Prod(dummy_loc, id1, t1', Sort(l,Type))) in
     let (meta, t3, t3') = reconstruct_with_type meta env ctx t3 (Sort(dummy_loc, Type)) in
     let (meta, t5, t5') = reconstruct_with_type meta env ctx t5 (Sort(dummy_loc, Type)) in
     begin
       try
         let meta = unification meta env ctx t1' (Union(dummy_loc, t3, t5)) in
         let (meta, t4, t4') =
           reconstruct_with_type meta env (DefAxiom("x", t3)
                                           :: ctx)
                                 t4 (app dummy_loc t2 (SInLeft(dummy_loc, t5, t3))) in
         let (meta, t6, t6') =
           reconstruct_with_type meta env (DefAxiom("x", t5)
                                           :: ctx) t6
                                 (app dummy_loc t2 (SInRight(dummy_loc,t3,t5)))
         in
         (meta,
          SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6),
          app dummy_loc t2 t1)
       with
       | Unif_Error -> err @@ Match_Error(l,t1,t1',t3,t5)
     end

  | SInLeft (l, t1, t2) ->
     let (meta, t1, _) = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct meta env ctx t2 in
     let (meta, tt, _) = force_type meta env ctx (Union(l,t2',t1)) in
     (meta, SInLeft(l,t1,t2), tt)

  | SInRight (l, t1, t2) ->
     let (meta, t1, _) = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct meta env ctx t2 in
     let (meta, tt, _) = force_type meta env ctx (Union(l,t1,t2')) in
     (meta, SInRight(l,t1,t2), tt)

  | Coercion (l, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct meta env ctx t2 in
     if is_subtype env ctx t1 t2' then
       (meta, Coercion(l,t1,t2), t1)
     else err @@ Coercion_Error(l,t2,t2',t1)

  | Var (l, n) -> let (t1,t1') = Env.find_var ctx n in
                  (meta, t1, t1')

  | Const (l, id) ->
     begin
     match Env.find_const false env id with
     | None -> err @@ Const_Error(l, id)
     | Some (t1,t1') -> (meta, t1, t1')
     end

  | Underscore l ->
     let (meta, s) = meta_add_sort meta l in
     let (meta, v) = meta_add meta ctx s l in
     let (meta, u) = meta_add meta ctx v l in
     (meta, u, v)

  | Meta (l, n, subst) ->
     get_from_meta meta l n subst
and force_type meta env ctx t =
  let unification = unification false in
  let (meta, t, t') = reconstruct meta env ctx t in
  let err = err ctx in
  let x =
    try
      Some (unification meta env ctx t' (Sort(dummy_loc, Type)))
    with
    | Unif_Error -> None
  in
  let y =
    try
      Some (unification meta env ctx t' (Sort(dummy_loc, Kind)))
    with
    | Unif_Error -> None
  in
  match x, y with
  | Some _, Some _ -> (meta, t, t')
  | Some meta, None -> (meta, t, t')
  | None, Some meta -> (meta, t, t')
  | None, None -> err @@ Force_Type_Error(loc_term t,t,t')
and reconstruct_with_type meta env ctx t1 ttt =
  let unification = unification false in
  let strongly_normalize = strongly_normalize false in
  let err = err ctx in
  let default () =
    let (meta, t1, t1') = reconstruct meta env ctx t1 in
    try
      unification meta env ctx t1' ttt, t1, t1'
    with
    | Unif_Error -> err @@ Typecheck_Error(loc_term t1, t1, t1', ttt)
  in
  match t1 with
  | Let(l,id,t1,t2,t3) ->
     let (meta, t1, t1') =
       force_type meta env ctx t1 in
     let (meta, t2, t2') =
       reconstruct_with_type
         meta env ctx t2 t1 in
     let decl = DefLet(id, t2, t2') in
     let (meta, t3, t3') =
       (* lift 0 1 t2 is technically correct *)
       reconstruct_with_type
         meta env (decl :: ctx) t3 (lift 0 1 ttt) in
     (meta, Let(l,id,t2',t2,t3), t3')
  | Abs(l,id,t1,t2) ->
     let ttt = strongly_normalize env ctx
              @@ apply_all_substitution meta ttt in
     begin
       match ttt with
       | Prod(_,_,u1,u2) ->
          let (meta,t1,t1') = force_type meta env ctx t1 in
          begin
            try
              let meta = unification meta env ctx t1 u1 in
              let decl = DefAxiom(id,t1) in
              let (meta, t2, t2') =
                reconstruct_with_type meta env
                                      (decl :: ctx) t2 u2 in
              (meta, Abs(l,id,t1,t2), Prod(l,id,t1,t2'))
            with
            | Unif_Error -> err @@ Wrong_Type_Error(l, t1, u1)
          end
       | _ -> default ()
     end
  | SPair(l,t1,t2) ->
     let ttt = strongly_normalize env ctx
              @@ apply_all_substitution meta ttt in
     begin
       match ttt with
       | Inter(_,u1,u2) ->
          let (meta,t1,t1') = reconstruct_with_type meta env ctx t1 u1
          in
          let (meta, t2, t2') =
            reconstruct_with_type meta env ctx t2 u2 in
          (meta, SPair(l,t1,t2), Inter(l,t1',t2'))
       | _ -> default ()
     end
  | SPrLeft (l, t1) ->
     let (meta, k) = meta_add meta ctx (Sort(dummy_loc, Type)) l in
     let (meta, t, _) = reconstruct meta env ctx
                                    (Inter(l,ttt,k)) in
     reconstruct_with_type meta env ctx t1 t
  | SPrRight (l,t1) ->
     let (meta, k) = meta_add meta ctx (Sort(dummy_loc, Type)) l in
     let (meta, t, _) = reconstruct meta env ctx
                                    (Inter(l,k,ttt)) in
     reconstruct_with_type meta env ctx t1 t
  | SInLeft (l,t1,t2) ->
     let ttt = strongly_normalize env ctx
              @@ apply_all_substitution meta ttt in
     begin
       match ttt with
       | Union(_,u1,u2) ->
          let (meta,t1,t1') = force_type meta env ctx t1
          in
          begin
            try
              let meta = unification meta env ctx t1 u2 in
              let (meta, t2, t2') =
                reconstruct_with_type meta env ctx t2 u1 in
              (meta, SInLeft(l,t1,t2), Union(l,t2',t1))
            with
            | Unif_Error -> err @@ Wrong_Type_Error(l, t1, u2)
          end
       | _ -> default ()
     end
  | SInRight (l,t1,t2) ->
     let ttt = strongly_normalize env ctx
              @@ apply_all_substitution meta ttt in
     begin
       match ttt with
       | Union(_,u1,u2) ->
          let (meta,t1,t1') = force_type meta env ctx t1
          in
          begin
            try
              let meta = unification meta env ctx t1 u1 in
              let (meta, t2, t2') =
                reconstruct_with_type meta env ctx t2 u2 in
              (meta, SInLeft(l,t1,t2), Union(l,t1,t2'))
            with
            | Unif_Error -> err @@ Wrong_Type_Error(l, t1, u1)
          end
       | _ -> default ()
     end
  | Underscore l -> let (meta, k) = meta_add meta ctx ttt l in
                    (meta, k, ttt)
  | _ -> default ()

let rec essence meta env ctx t1 =
  match t1 with
  | SPair (l,t1,t2) ->
     let (meta, t1) = essence meta env ctx t1 in
     essence_with_hint meta env ctx t2 t1
  | SPrLeft (l,t1) | SPrRight (l,t1) ->
     essence meta env ctx t1
  | SMatch (l,t1,t2,_,t3,t4,_,t5,t6) ->
     let (meta, t1) = essence meta env ctx t1 in
     let (meta, _) = essence meta env ctx t2 in
     let (meta, _) = essence meta env ctx t3 in
     let (meta, t4) = essence meta env (DefLet("x",nothing,t1) :: ctx) t4 in
     let (meta, _) = essence meta env ctx t5 in
     let (meta, t6) = essence_with_hint meta env (DefLet("x",nothing,t1) :: ctx) t6 t4 in
     meta, app l (Abs(l, "x",nothing, t6)) t1
  | SInLeft (l,t1,t2) | SInRight (l,t1,t2) | Coercion (l,t1,t2) ->
     let (meta, _) = essence meta env ctx t1 in
     essence meta env ctx t2
  | Let (l,id,t1,t2,t3) -> let (meta,t1) = essence meta env ctx t1 in
                           let (meta,t2) = essence meta env ctx t2 in
                           let (meta,t3) = essence meta env (DefLet(id,nothing,t2) :: ctx) t3 in
                           meta, Let(l,id,nothing,t2,t3)
  | Prod (l,id,t1,t2) -> let (meta,t1) = essence meta env ctx t1 in
                         let (meta,t2) = essence meta env (DefAxiom(id,nothing) :: ctx) t2 in
                         meta, Prod(l,id,t1,t2)
  | Abs (l,id,t1,t2) -> let (meta,t1) = essence meta env ctx t1 in
                        let (meta,t2) = essence meta env (DefAxiom(id,nothing) :: ctx) t2 in
                        meta, Abs(l,id,nothing,t2)
  | App (l,t1,ll) -> let (meta,t1) = essence meta env ctx t1 in
                     let rec foo meta l =
                       match l with
                       | [] -> meta, []
                       | x :: l -> let (meta, x) = essence meta env ctx x in
                                   let (meta, l) = foo meta l in
                                   meta, x :: l
                     in
                     let (meta,ll) = foo meta ll in
                     meta, App(l,t1,ll)
  | Inter (l,t1,t2) -> let (meta, t1) = essence meta env ctx t1 in
                       let (meta, t2) = essence meta env ctx t2 in
                       meta, Inter(l,t1,t2)
  | Union (l,t1,t2) -> let (meta, t1) = essence meta env ctx t1 in
                       let (meta, t2) = essence meta env ctx t2 in
                       meta, Union(l,t1,t2)
  | _ -> (meta, t1)

and essence_with_hint meta env ctx t1 t =
  let unification = unification true in
  let err = err ctx in
  let default () =
    let (meta, t1) = essence meta env ctx t1 in
    try
      let meta = unification meta env ctx t1 t in
      meta, t1
    with
    | Unif_Error -> err @@ Essence_Error(loc_term t1, t1, t)
  in
  let norm () =
    strongly_normalize true env ctx
    @@ apply_all_substitution meta t
  in
  match t1 with
  | SPair (l,t1,t2) ->
     let (meta, t1) = essence_with_hint meta env ctx t1 t in
     essence_with_hint meta env ctx t2 t1
  | SPrLeft (l,t1) | SPrRight (l,t1) ->
     essence_with_hint meta env ctx t1 t
  | SInLeft (l,t1,t2) | SInRight (l,t1,t2) | Coercion (l,t1,t2) ->
     let (meta, _) = essence meta env ctx t1 in
     essence_with_hint meta env ctx t2 t
  | Let (l,id,t1,t2,t3) ->
     let (meta,t1) = essence meta env ctx t1 in
     let (meta,t2) = essence meta env ctx t2 in
     let (meta,t3) = essence_with_hint meta env (DefLet(id,nothing,t2) :: ctx)
                                       t3 (lift 0 1 t)
     in meta, Let(l,id,nothing,t2,t3)
  | Prod (l,id,t1,t2) ->
     let t = norm () in
     begin
       match t with
       | Prod (_,_,t1',t2') ->
          let (meta,t1) = essence_with_hint meta env ctx t1 t1' in
          let (meta,t2) = essence_with_hint
                            meta env (DefAxiom(id,t1) :: ctx) t2 t2' in
          meta, Prod(l,id,t1,t2)
       | _ -> default ()
     end
  | Abs (l,id,t1,t2) ->
     let t = norm () in
     begin
       match t with
       | Abs (_,_,t1',t2') ->
          let (meta,t2) = essence_with_hint
                            meta env (DefAxiom(id,nothing) :: ctx) t2 t2' in
          meta, Abs(l,id,nothing,t2)
       | _ -> default ()
     end
  | Inter (l,t1,t2) ->
     let t = norm () in
     begin
       match t with
       | Inter (_,t1',t2') ->
          let (meta,t1) = essence_with_hint meta env ctx t1 t1' in
          let (meta,t2) = essence_with_hint meta env ctx t2 t2' in
          meta, Inter(l,t1,t2)
       | _ -> default ()
     end
  | Union (l,t1,t2) ->
     let t = norm () in
     begin
       match t with
       | Union (_,t1',t2') ->
          let (meta,t1) = essence_with_hint meta env ctx t1 t1' in
          let (meta,t2) = essence_with_hint meta env ctx t2 t2' in
          meta, Union(l,t1,t2)
       | _ -> default ()
     end
  | _ -> default ()

let clean_meta meta tl =
  let rec list_evars =
    function
    | Sort _ | Var _ | Const _ | Underscore _ -> []
    | Let  (_,_,t1,t2,t3) -> List.concat @@ List.map list_evars [t1;t2;t3]
    | Prod (_,_,t1,t2) | Abs (_,_,t1,t2) | Inter (_,t1,t2)
      | Union (_,t1,t2) | SPair (_,t1,t2) | SInLeft(_,t1,t2)
      | SInRight(_,t1,t2) | Coercion (_,t1,t2) -> List.concat @@ List.map list_evars [t1;t2]
    | App (_,t1,l) -> List.concat @@ List.map list_evars (t1 :: l)
    | SPrLeft (_, t) | SPrRight (_,t) -> list_evars t
    | SMatch (_,t1,t2,_,t3,t4,_,t5,t6) -> List.concat @@ List.map list_evars [t1;t2;t3;t4;t5;t6]
    | Meta (_,n,l) -> n :: (List.concat @@ List.map list_evars l)
  in
  let l = List.sort_uniq (fun (x : int) (y : int) -> compare x y)
          @@ List.concat @@ List.map list_evars tl in
  let foo = apply_all_substitution meta in
  let rec map =
    function
    | [] -> []
    | DefAxiom (id,t) :: ctx -> DefAxiom(id, foo t) :: map ctx
    | DefLet (id,t1,t2) :: ctx -> DefLet(id, foo t1, foo t2) :: map ctx
  in
  let rec clean =
    function
    | [] -> []
    | IsSort n :: m ->
         IsSort n :: clean m
    | SubstSort (n,t) :: m -> clean m
    | DefMeta (ctx,n,t) :: m ->
       DefMeta(map ctx, n, foo t)
       :: clean m
    | Subst _ :: m -> clean m
  in
  let rec strip =
    function
    | [] -> []
    | DefAxiom (id,t) :: ctx -> t :: strip ctx
    | DefLet (id,t1,t2) :: ctx -> t1 :: t2 :: strip ctx
  in
  let rec clean2 l =
    function
    | [] -> []
    | IsSort n :: m ->
       if find l n then
         IsSort n :: clean2 l m
       else
         clean2 l m
    | DefMeta (ctx,n,t) :: m ->
       if find l n then
         let l =
           List.append l (List.concat @@ List.map list_evars (t :: strip ctx)) in
         DefMeta (ctx,n,t) :: clean2 l m
       else
         clean2 l m
    | _ -> assert false
  in let n, meta = meta in (n,clean2 l @@ clean meta)

(* In interactive proofs, we want newly generated meta-vars
to have different names than previously generated essence meta-vars.
So call this method to synchronize meta and emeta. *)
let sync_meta_emeta (_,meta) (n,emeta) = (n,meta)

(* TODO: add the possibility for meta and emeta to already exist,
so we can do interactive proofs *)
let check_term env ctx t1 t2 =
  let (meta, t1, t2) =
    match t2 with
    | None -> reconstruct (0,[]) env ctx t1
    | Some t2 ->
       let meta, t2, _ = force_type (0,[]) env ctx t2 in
       reconstruct_with_type meta env ctx t1 t2
  in
  let t1 = apply_all_substitution meta t1 in
  let t2 = apply_all_substitution meta t2 in
  let meta = clean_meta meta [t1;t2] in
  let emeta = meta in
  let (emeta, et1) = essence emeta env ctx t1 in
  let (emeta, et2) = essence emeta env ctx t2 in
  (* TODO: unify emeta with previous emeta (in interactive proofs) *)
  let meta = sync_meta_emeta meta emeta in (* IMPORTANT *)
  let et1 = apply_all_substitution emeta et1 in
  let et2 = apply_all_substitution emeta et2 in
  (meta, emeta, t1, t2, et1, et2)

let check_axiom env ctx t =
  let (meta, t1, t2) = force_type (0,[]) env [] t in
  let t1 = apply_all_substitution meta t1 in
  let meta = clean_meta meta [t1] in
  let emeta = meta in
  let (emeta, et1) = essence emeta env ctx t1 in
  let et1 = apply_all_substitution emeta et1 in
  (meta, emeta, t1, et1)

