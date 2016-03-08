open Definitions

let rec rebuild_delta derivation =
  match derivation with
  | AMark i -> DMark i
  | AFcI (t, a) ->
     (
       match (t.m, t.s) with
       | (MLambda (_, i, _), SFc (s1, s2)) ->
	  DLambda (i, s1, rebuild_delta a)
       | _ -> failwith "wrong tree"
     )
  | AFcE (_, a1, a2) ->
     DApp (rebuild_delta a1, rebuild_delta a2)
  | AAndI (_, a1, a2) ->
     DAnd (rebuild_delta a1, rebuild_delta a2)
  | AAndEL (_, a) ->
     DLeft (rebuild_delta a)
  | AAndER (_, a) ->
     DRight (rebuild_delta a)
  | ANull -> failwith "empty tree"

let replace derivation leaf =
  let rec visit (derivation : derivation) =
    match derivation with
    | ANull -> leaf
    | AMark _ -> failwith "full"
    | AFcI (t, a) -> AFcI (t, visit a)
    | AFcE (t, a1, a2) ->
       (
	 try (
	   let a1' = visit a1 in
	   AFcE (t, a1', a2)
	 )
	 with Failure "full" ->
	   let a2' = visit a2 in
	   AFcE (t, a1, a2')
       )
    | AAndI (t, a1, a2) ->
       (
	 try (
	   let a1' = visit a1 in
	   AAndI (t, a1', a2)
	 )
	 with Failure "full" ->
	   let a2' = visit a2 in
	   AAndI (t, a1, a2')
       )
    | AAndEL (t, a) -> AAndEL (t, visit a)
    | AAndER (t, a) -> AAndER (t, visit a)
  in visit derivation

let copy_pb pb =
  let pb' = {
    judg = None;
    jlist = [];
    derivation = ANull
  }
  in
  pb'.judg <- pb.judg;
  pb'.jlist <- pb.jlist;
  pb'.derivation <- pb.derivation;
  pb'

let shift pb =
  match pb.jlist with
  | [] ->
     begin
       pb.judg <- None;
       pb.jlist <- []
     end
  | t :: l ->
     begin
       pb.judg <- Some t;
       pb.jlist <- l
     end

let choose_var pb =
  (
    match pb.judg with
    | Some t ->
       (
	 match t.m with
	 | MVar x ->
	    let i = find_i x t.s t.g in
	    pb.derivation <- replace pb.derivation (AMark i);
	 | _ -> failwith "var"
       )
    | _ -> failwith "var"
  );
  shift pb

let choose_fci pb =
  match pb.judg with
  | Some t ->
     (
       match t.m, t.s with
       | MLambda (x, i, m), SFc (s1, s2) ->
	  begin
	    pb.derivation <- replace pb.derivation (AFcI (t, ANull));
	    pb.judg <- Some {g = (x, i, s1)::t.g; m = m; s = s2}
	  end
       | _ -> failwith "fci"
     )
  | _ -> failwith "fci"

let choose_fce pb a =
  match pb.judg with
  | Some t ->
     (
       match t.m with
       | MApp (m1, m2) ->
	  begin
	    pb.derivation <- replace pb.derivation (AFcE (t, ANull, ANull));
	    pb.judg <- Some {g = t.g; m = m1; s = SFc (a, t.s)};
	    pb.jlist <- {g = t.g; m = m2; s = a} :: pb.jlist
	  end
       | _ -> failwith "fce"
     )
  | _ -> failwith "fce"

let choose_andi pb =
  match pb.judg with
  | Some t ->
     (
       match t.s with
       | SAnd (s1, s2) ->
	  begin
	    pb.derivation <- replace pb.derivation (AAndI (t, ANull, ANull));
	    pb.judg <- Some {g = t.g; m = t.m; s = s1};
	    pb.jlist <- {g = t.g; m = t.m; s = s2} :: pb.jlist
	  end
       | _ -> failwith "andi"
     )
  | _ -> failwith "andi"

let choose_andel pb a =
  match pb.judg with
  | Some t ->
     begin
       pb.derivation <- replace pb.derivation (AAndEL (t, ANull));
       pb.judg <- Some {g = t.g; m = t.m; s = SAnd (t.s, a)}
     end
  | _ -> failwith "andel"

let choose_ander pb a =
  match pb.judg with
  | Some t ->
     begin
       pb.derivation <- replace pb.derivation (AAndER (t, ANull));
       pb.judg <- Some {g = t.g; m = t.m; s = SAnd (a, t.s)}
     end
  | _ -> failwith "ander"

let possibilities t bol =
  let visit_fci l =
    match t.m, t.s with
    | MLambda _, SFc _ -> "->I" :: l
    | _ -> l
  and visit_fce l =
    match t.m with
    | MApp _ -> "->E" :: l
    | _ -> l
  and visit_var l =
    match t.m with
    | MVar x ->
       (
	 try (
	   let _ = find_i x t.s t.g in
	   "var" :: l
	 )
	 with Failure "empty list" -> l
       )
    | _ -> l
  and visit_andi l =
    match t.s with
    | SAnd _ -> "&I" :: l
    | _ -> l
  in visit_fci (visit_fce (visit_var (visit_andi ("&El" :: "&Er" :: (if bol then ["backtrack"] else [])))))

let choose pb bol =
  let rec aux =
    function
    | [] -> print_string "\n\n"
    | op :: l ->
       begin
	 print_string op;
	 if l = [] then () else print_string " ; ";
	 aux l
       end
  in
  let rec choose_type () =
    print_string "\nType the intermediate type you want, or 'cancel' to come back to rules.\n\n";
    let l = read_line () in
    match l with
    | "cancel" -> failwith "annul"
    | _ ->
       try (
	 let lb = Lexing.from_string l in
	 Parser_sigma.s Lexer_sigma.read lb
       )
       with _ ->
	 begin
	   print_string "\nWhat you taped is not understandable...\n\n";
	   choose_type ()
	 end
  and loop () =
    (
      match pb.judg with
      | None -> failwith "abnormal"
      | Some t ->
	 (
	   print_string "\n";
	   print_pb pb;
	   print_string "Choose your rule :\n\n";
	   let lp = possibilities t bol in
	   aux lp;
	   let opt = read_line () in
	   if List.exists (fun o -> opt = o) lp
	   then
	     match opt with
	     | "->I" -> OFcI
	     | "var" -> OVar
	     | "backtrack" -> OBacktrack
	     | "&I" -> OAndI
	     | "->E" ->
		(
		  try OFcE (choose_type ())
		  with Failure "annul" -> loop ()
		)
	     | "&El" ->
		(
		  try OAndEL (choose_type ())
		  with Failure "annul" -> loop ()
		)
	     | "&Er" ->
		(
		  try OAndER (choose_type ())
		  with Failure "annul" -> loop ()
		)
	     | _ -> failwith "isn't happening ever"
	   else
	     begin
	       print_string "\nYou cannot choose this option yet, or you taped something wrong\n\n";
	       loop ()
	     end
	 )
    )
  in
  loop ()

let rec algorithm pb_tot =
  match pb_tot with
  | [] -> failwith "should not happen"
  | pb :: lnext ->
     match pb.judg with
     | None ->
	print_string ("\nYou succeeded, here is the delta you were looking for:\n"^(delta_to_string (rebuild_delta pb.derivation))^ "\n\n")
     | _	 ->
	let pb' = copy_pb pb in
	let opt = choose pb' (if lnext = [] then false else true) in
	match opt with
	| OFcI ->
	   begin
	     choose_fci pb';
	     algorithm (pb' :: pb_tot)
	   end
	| OFcE a ->
	   begin
	     choose_fce pb' a;
	     algorithm (pb' :: pb_tot)
	   end
	| OAndI ->
	   begin
	     choose_andi pb';
	     algorithm (pb' :: pb_tot)
	   end
	| OAndEL a ->
	   begin
	     choose_andel pb' a;
	     algorithm (pb' :: pb_tot)
	   end
	| OAndER a ->
	   begin
	     choose_ander pb' a;
	     algorithm (pb' :: pb_tot)
	   end
	| OVar ->
	   begin
	     choose_var pb';
	     algorithm (pb' :: pb_tot)
	   end
	| OBacktrack -> algorithm lnext

let main_pr lbm lbs =
  let m = Parser_m.m Lexer_m.read lbm
  and s = Parser_sigma.s Lexer_sigma.read lbs
  in
  let pb = {
    judg = Some {g = []; m = m; s = s};
    jlist =  [];
    derivation = ANull
  }
  in algorithm [pb]
