(*

Pour chaque delta-noeud :
- le parent (pour le backtracking ???? (à oublier)
- les enfants
- l'essence
- la règle logique utilisée (si l'utilisateur l'a rentrée)
- le contexte
- les fausses variables (utile ?????????)

Pour chaque essence-noeud :
- les enfants
- la règle de construction utilisée (si on la connait)
- le delta-noeud correspondant
- ?????? comment gérer les fausses variables ??????
  Proposition :
- faire un arbre d'essences (niveau 0 : aucune fausse variable, niveau n : n fausses variables)
- à chaque mise à jour, mettre à jour l'arbre complet
- faire un mécanisme pour que le terme associé à une fausse variable soit trouvable facilement (de manière bidirectionnelle)

 *)



open Utils
open Reduction
open Inference

(* nameless variables are holes in the AST *)

let rec update tree path input =
  match tree with
  | BDVar (x,b,i) -> input (* we suppose x = "" *)
  | BDStar -> tree (* should not happen *)
  | BDLambda (x,f,d) -> BDLambda(x, f, update d path input)
  | BDApp (d',d'') -> (match path with
		       | [] -> failwith "path error 1"
		       | Left :: path' -> BDApp(update d' path' input, d'')
		       | _ :: path' -> BDApp(d', update d'' path' input))
  | BDAnd (d', d'') -> (match path with
			| [] -> failwith "path error 1"
			| Left :: path' -> BDAnd(update d' path' input, d'')
			| _ :: path' -> BDAnd(d', update d'' path' input))
  | BDProjL d -> BDProjL(update d path input)
  | BDProjR d -> BDProjR(update d path input)
  | BDOr (x,f,d,x',f',d',d'') -> (match path with
				  | [] -> failwith "path error 1"
				  | Left :: path' -> BDOr(x, f, update d path' input, x', f', d', d'')
				  | Middle :: path' -> BDOr(x, f, d, x', f', update d' path' input, d'')
				  | Right :: path' -> BDOr(x, f, d, x', f', d', update d'' path' input))
  | BDInjL d -> BDInjL(update d path input)
  | BDInjR d -> BDInjR(update d path input)

(* check if the essence can be correct *)
let essence_trick tree =
  let rec preprocess d =
    match d with
    | BDVar (x,b,i) -> if x = "" then BDStar else d (* replace holes in the tree by `*` *)
    | BDStar -> BDStar
    | BDLambda (x,f,d') -> BDLambda(x, f, preprocess d')
    | BDApp (d',d'') -> BDApp(preprocess d', preprocess d'')
    | BDAnd (d', d'') -> BDAnd(preprocess d', preprocess d'')
    | BDProjL d' -> BDProjL(preprocess d')
    | BDProjR d' -> BDProjR(preprocess d')
    | BDOr (x,f,d',x',f',d'',d''') -> BDOr(x,f,preprocess d',x',f',preprocess d'',preprocess d''')
    | BDInjL d' -> BDInjL(preprocess d')
    | BDInjR d' -> BDInjR(preprocess d')
  in
  wellformed_delta (preprocess tree)

let rec append l x =
  match l with
  | [] -> x :: []
  | y :: l' -> y :: (append l' x)

(* give next goal *)
let goal_rotate goal =
  match goal with
  | [] -> failwith "no goal"
  | x :: l -> append l x

(*
(* give path to next hole *)
let path_rotate tree path =
  let rec foo tree path =
    match tree with
    | BDVar (x,b,i) -> if x = "" then path else failwith "FAIL"
    | BDStar -> failwith "FAIL"
    | BDLambda (x,f,d) -> foo d path
    | BDApp (d',d'') -> (match path with
			 | [] -> (try Left :: (foo d' path) with
				    _ -> Right :: (foo d'' path)
				 )
			 | Left :: path' -> (try Left :: (foo d' path) with
					       _ -> Right :: (foo d'' path)
					    )
			 | _ :: path' -> Right :: (foo d'' path)
			)
    | BDAnd (d', d'') -> (match path with
		          | [] -> (try Left :: (foo d' path) with
				     _ -> Right :: (foo d'' path)
				  )
			  | Left :: path' -> (try Left :: (foo d' path) with
						_ -> Right :: (foo d'' path)
					     )
			  | _ :: path' -> Right :: (foo d'' path)
			 )
    | BDProjL d -> foo d path
    | BDProjR d -> foo d path
    | BDOr (x,f,d,x',f',d',d'') -> (match path with
				    | [] -> (try Left :: (foo d path) with
					       _ -> (try Middle :: (foo d' path) with
						       _ -> Right :: (foo d'' path)))
				    | Left :: path' ->  (try Left :: (foo d path) with
							   _ -> (try Middle :: (foo d' path) with
								   _ -> Right :: (foo d'' path)))
				    | Middle :: path' -> (try Middle :: (foo d' path) with
							    _ -> Right :: (foo d'' path)
							 )
				    | Right :: path' -> Right :: (foo d'' path)
				   )
    | BDInjL d -> foo d path
    | BDInjR d -> foo d path
  in
  try foo tree path with
  | _ -> foo tree [] (* cyclic case *)
	 *)

let newproof goal = (BDVar("",false,0), (goal, [], []) :: [])

let proofstep p rule ctx =
  let (tree, goal') = p in
  let (goal, path, gamma, rest) =
    match goal' with
    | [] -> failwith "no goal"
    | (g, p, g') :: l -> (g, p, g', l)
  in
  let rec strip g =
    match g with
    | [] -> []
    | (a,_) :: g' -> a :: (strip g')
  in
  match rule with
  | PExact d' -> (
    let d = delta_gamma d' (strip gamma) in
    let err = Inference.familycheck goal gamma ctx in
    if err = "" then
      if Inference.wellformed_delta d ctx then
	let err = Inference.deltacheck d gamma ctx in
	if err = "" then
	  if Inference.wellformed_family goal ctx then
	    let f' = Inference.deltainfer d gamma ctx in
	    if Inference.unifiable goal f' ctx then
	      let d = update tree path d in (d, rest)
	    else
	      failwith ("Error: type-checking failed for " ^ (def_to_string "user input" (d,goal)) ^ " (its type should be " ^ (family_to_string (bruijn_to_family f')) ^ ").\n")
	  else
	    failwith ("Error: " ^ (family_to_string (bruijn_to_family goal)) ^ " is ill-formed.\n")
	else
	  failwith err
      else
	failwith ("Error: " ^ (delta_to_string (bruijn_to_delta d)) ^ " is ill-formed.\n")
    else
      failwith err
  )
  | PAbst1 -> (match goal with
	       | BSProd (x, f, g) -> (update tree path (BDLambda (x,f,BDVar("",false,0))), (g, path, (x, f) :: gamma) :: rest)
	       | _ -> failwith "Error: the goal should be like `! x : s. t`.\n"
	      )
  | PAbst2 x -> (match goal with
	       | BSFc (f, g) -> (update tree path (BDLambda (x,f,BDVar("",false,0))), (g, path, (x, f) :: gamma) :: rest)
	       | _ -> failwith "Error: the goal should be like `s -> t`.\n"
	      )
  | PSConj -> (match goal with
	       | BSAnd (f, g) -> (update tree path (BDAnd (BDVar("",false,0),BDVar("",false,0))), (f, append path Left, gamma) :: (g, append path Right , gamma) :: rest)
	       | _ -> failwith "Error: the goal should be like `! x : s. t`.\n"
	      )
  | PSDisj (id, f, f') ->
     (update tree path (BDOr(id,f,BDVar("",false,0),id,f',BDVar("",false,0),BDVar("",false,0))), (goal, append path Left, (id, f) :: gamma) :: (goal, append path Middle, (id, f') :: gamma) :: (BSOr(f,f'), append path Right, gamma) :: rest)
  | PProjL f -> (update tree path (BDProjL (BDVar("",false,0))), (BSAnd (goal, f), path, gamma) :: rest)
  | PProjR f -> (update tree path (BDProjR (BDVar("",false,0))), (BSAnd (f, goal), path, gamma) :: rest)
  | PInjL -> (match goal with
	      | BSOr (f, g) -> (update tree path (BDInjL (BDVar ("", false, 0))), (f, path, gamma) :: rest)
	      | _ -> failwith "Error: the goal should be like `s | t`.\n"
	     )
  | PInjR -> (match goal with
	      | BSOr (g, f) -> (update tree path (BDInjL (BDVar ("", false, 0))), (f, path, gamma) :: rest)
	      | _ -> failwith "Error: the goal should be like `s | t`.\n"
	     )
  | _ -> failwith "should not happen"

       (* old code
type essencetree =
  | ETVar of int
  | ETApp of essencetree * essencetree
  | ETAbstr of essencetree
  | ETOmega

(* get the essence of already-defined deltaterms *)
let rec essenceextraction delta gamma ctx =
  let rec size l =
    match l with
    | [] -> 0
    | x :: l' -> 1 + (size l')
  in
  let rec foo x l =
    match foo with
    | [] -> failwith "can't happen"
    | (y,f) :: l' -> if y = f then size gamma else 1 + (foo x l')
  in
  match delta with
  | BDVar (x,b,n) -> if b then n else foo x ctx
  | BDStar -> ETOmega
  | BDLambda (x,f,d') -> ETAbstr (essenceextraction d' ((x,f) :: gamma) ctx)
  | BDApp (d',d'') -> ETApp (essenceextraction d' gamma ctx) (essenceextraction d'' gamma ctx)
  | BDAnd (d',d'') -> essenceextraction d' gamma ctx
  | BDProjL d' -> essenceextraction d' gamma ctx
  | BDProjR d' -> essenceextraction d' gamma ctx
  | BDOr (x',f',d',x'',f'',d'',d''') ->
  | BDInjL d' -> essenceextraction d' gamma ctx
  | BDInjR d' -> essenceextraction d' gamma ctx

(* we supposed the proof is over and the graph is correct *)
let prooftobdelta p =
  let rec position id l =
    match l with
    | [] -> failwith "the programmer should ensure this does not happen (use the find function)"
    | (x, y) :: l' -> if x = id then 0 else 1+(position id l')
  in
  let PG (proof, _, _, _) = p in
  let rec foo node =
    let PN (_, childlist, gamma, formula, rule, _) = node in
    match rule with
    | None -> failwith "incomplete proof"
    | Some pf ->
       match pf with
       | POmega -> BDStar
       | PVar id -> if (find id gamma) then BDVar(id, true, position id gamma)
		    else BDVar(id, false, 0)
       | PIntro id -> (match (formula, childlist) with
		       | (BSFc(f1,_), n :: []) -> BDLambda(id, f1, foo (get n proof))
		       | _ -> failwith "incorrect proof")
       | PDependentIntro -> (match (formula, childlist) with
			     | (BSProd(id, f1, f2), n :: []) -> BDLambda(id, f1, foo (get n proof))
			     | _ -> failwith "incorrect proof")
       | PAnd -> (match childlist with
		  | n :: m :: [] -> BDAnd(foo (get n proof), foo (get m proof))
		  | _ -> failwith "incorrect proof")
       | PInjL -> (match childlist with
		     | n :: [] -> BDInjL(foo (get n proof))
		     | _ -> failwith "incorrect proof")
       | PInjR -> (match childlist with
		     | n :: [] -> BDInjR(foo (get n proof))
		     | _ -> failwith "incorrect proof")
       | PElim f -> (match childlist with
		     | n :: m :: [] -> BDApp(foo (get n proof), foo (get m proof))
		     | _ -> failwith "incorrect proof")
       | PDependentElim (f,d) -> (match childlist with
				  | n :: [] -> BDApp(foo (get n proof), d)
				  | _ -> failwith "incorrect proof")
       | PProjL f -> (match childlist with
		      | n :: [] -> BDProjL(foo (get n proof))
		      | _ -> failwith "incorrect proof")
       | PProjR f -> (match childlist with
		      | n :: [] -> BDProjR(foo (get n proof))
		      | _ -> failwith "incorrect proof")
       | POr (id, f1, f2) -> (match childlist with
			      | n :: m :: o :: [] -> BDOr (id, f1, foo (get n proof),id, f2, foo (get m proof), foo (get o proof))
			      | _ -> failwith "incorrect proof")
       | _ -> failwith "incorrect proof"
  in
  foo (get 0 proof)

  /!\
(* TODO: manage the definitions *)
let fullgamma gamma ctx =
  let Sig (a, b, c) = ctx in
  let c' = List.map (fun (x, (d, f)) -> (x, f)) c in
  List.append gamma (List.append b c')

let list_of_tactics p ctx =
  let PG(proof,essence, n, goals) = p in
  let node = get n proof in
  let PN (parent, childlist, gamma', formula, rule, e) = node in
  let gamma = fullgamma gamma' ctx in
  let EN(echildlist,erule,_) = get e essence in
  let concat a b = if a = "" || b = "" then a ^ b else a ^ ", " ^ b in
  let syntaxdirected =
    match formula with
    | BSFc (f1, f2) -> "->I"
    | BSProd (id, f1, f2) -> "->I" (* same as BSFc *)
    | BSLambda (id, f1, f2) -> failwith "incorrect formula"
    | BSApp (f1, d1) -> ""
    | BSAnd (f1, f2) -> "&I"
    | BSOr (f1, f2) -> "|Il, |Ir"
    | BSAtom id -> ""
    | BSOmega -> "omega"
    | BSAnything -> failwith "incorrect formula"
  in
  let syntaxnoabstr =
    match formula with
    | BSFc (f1, f2) -> ""
    | BSProd (id, f1, f2) -> ""
    | BSLambda (id, f1, f2) -> failwith "incorrect formula"
    | BSApp (f1, d1) -> ""
    | BSAnd (f1, f2) -> "&I"
    | BSOr (f1, f2) -> "|Il, |Ir"
    | BSAtom id -> ""
    | BSOmega -> "omega"
    | BSAnything -> failwith "incorrect formula"
  in  let rec in_gamma l f = (* we suppose all variables have different names *)
    match l with
    | [] -> false
    | (id,f') :: l' -> if unifiable f f' ctx then true else in_gamma l' f
  in
  let var = if (in_gamma gamma formula) then "var" else "" in
  let break =
    match echildlist with
    | [] -> ""
    | _ -> "break"
  in
  let switch =
    match goals with
    | [] -> ""
    | _ -> "switch"
  in
  let backtrack = if parent = n then "" else "backtrack" (* in the implementation, root is its own parent *)
  in
  match essence with
  | None -> concat syntaxdirected (concat var (concat "->E, !E, &El, &Er, |E, abort" (concat switch backtrack)))
  | Some EApp -> concat syntaxnoabstr (concat break (concat "->E, !E, &El, &Er, |E, abort" (concat switch backtrack)))
  | Some EAbstr -> concat syntaxdirected (concat "&El, &Er, |E, abort" (concat switch backtrack)))
  | Some EVar i -> concat var (concat "&El, &Er, |E, abort" (concat switch backtrack)))

let newproof formula =
  PG((0,PN (0,[],[],formula, None, 0)) :: [], (0,EN([], None, 0 :: [])) :: [], 0, [])

let prooffeasible p rule ctx =
  let PG(proof,essence, n, goals) = p in
  let node = get n proof in
  let PN (parent, childlist, gamma', formula, rule', e) = node in
  let gamma = realgamma gamma' ctx (* we don't add the definitions *)
  let EN(echildlist,erule,synclist) = get e essence in
  let maxproof = getmax proof 0 in
  let maxessence = getmax essence 0 in
  let rec position id l =
    match l with
    | [] -> failwith "the programmer should ensure this does not happen (use the find function)"
    | (x, y) :: l' -> if x = id then 0 else 1+(position id l')
  in
  let rec findposition n l =
    match l with
    | [] -> failwith "should not happen"
    | (x, y) :: l' -> if n = 0 then x else findposition (n-1) l'
  match rule with
  (* syntax directed *)
  | POmega -> (match formula with
	      | BSOmega -> ""
	      | _ -> "Error: the omega tactic should be applied to $")
  | PVar x -> /!\
(* TODO: manage definitions *)
if (find x gamma) then
		let f = get x gamma in
		if unifiable f formula then
		  match erule with
		  | None -> ""
		  | Some EVar i -> if position x gamma = i then "" else "Error: the hypothesis you should use is " ^ (findposition i gamma) /!!!!!!\
		  | Some _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n"
		else
		  "Error: cannot unify " ^ (family_to_string (bruijn_to_family f)) ^ " and " ^ (family_to_string (bruijn_to_family formula)) ^ ".\n"
	      else
		"Error: cannot find " ^ x ^ ".\n"
  | PIntro x -> (match formula with
		 | BSFc(f1, f2) -> (match erule with
				    | None -> ""
				    | Some EAbstr -> ""
				    | Some _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n")
		 | BSProd (id, f1, f2) ->  (match erule with
				    | None -> ""
				    | Some EAbstr -> ""
				    | Some _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n")
		 | _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n")
  | PDependentIntro -> (match formula with
			| BSFc(f1, f2) -> (match erule with
					   | None -> ""
					   | Some EAbstr -> ""
					   | Some _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n")
			| BSProd (id, f1, f2) ->  (match erule with
						   | None -> ""
						   | Some EAbstr -> ""
						   | Some _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n")
			| _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n")
  | PAnd -> (match formula with
	     | BSAnd(f1, f2) -> ""
	     | _ -> "Error: you can only apply the following tactics: " ^ list_of_tactics p ctx ^ ".\n")
  | PInjL ->
  | PInjR ->
  (* non syntax directed *)
  | PElim f
  | PDependentElim (f,d)
  | PProjL f
  | PProjR f
  | POr (x,f1,f2)
  (* essence *)
  | PBreak
  (* control flow *)
  | PBacktrack -> ""
  | PAbort -> ""
  | PSwitch -> ""


(* we suppose that prooffeasible p rule = "" *)
let proofstep p rule =
  let rec enqueue l x =
    match l with
    | [] -> x :: []
    | y :: l' -> y :: (enqueue l' x)
  in
  let rec replacenode l node n =
    match l with
    | [] -> []
    | (n',a) :: l' -> if n = n' then (n,node) :: l' (* no recursion *)
		      else (n',a) :: (replacenode l' node n)
  in
  let rec getmax l n =
    match l with
    | [] -> n
    | (n',_) :: l' -> let max = if n > n' then n else n' in
		      getmax l max
  in
  let hd l =
    match l with
    | [] -> -1
    | n :: _ -> n
  in
  let tl l =
    match l with
    | [] -> []
    | _ :: l' -> l'
  in
  let PG(proof,essence, n, goals) = p in
  let node = get n proof in
  let PN (parent, childlist, gamma, formula, rule', e) = node in
  let EN(echildlist,erule,synclist) = get e essence in
  let maxproof = getmax proof 0 in
  let maxessence = getmax essence 0 in
  let issync =
    match erule with
    | None -> false
    | Some _ -> true
  in
  match rule with
  (* syntax directed *)
  | POmega -> PG(replacenode proof (PN (parent, [], gamma, formula, Some rule, e)), essence, hd goals, tl goals)
  | PVar x -> PG(replacenode proof (n, PN (parent, [], gamma, formula, Some rule, e)), replacenode essence (e, EN([],Some EVar, synclist)), hd goals, tl goals)
  | PIntro x
  | PDependentIntro
  | PAnd
  | PInjL
  | PInjR
  (* non syntax directed *)
  | PElim f
  | PDependentElim (f,d)
  | PProjL f
  | PProjR f
  | POr (x,f1,f2)
  (* essence *)
  | PPop
  | PBreak
  (* control flow *)
  | PBacktrack -> failwith "this tactic should be processed by the REPL"
  | PAbort -> failwith "this tactic should be processed by the REPL"
  | PSwitch -> match (enqueue goals n) with
	       | [] -> failwith "can't happen"
	       | n' :: g -> PG(proof, essence, n', g)
			    *)
