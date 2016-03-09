type sigma =
  | SFc of sigma * sigma
  | SAnd of sigma * sigma
  | SAtom of string

type m =
  | MVar of string
  | MLambda of string * string * m (* parameter * mark * function body *)
  | MApp of m * m

type bruijn =
  | BVar of string * bool * int (* varname * bound? * bruijn index *)
  | BLambda of bruijn
  | BApp of bruijn * bruijn

type delta =
  | DMark of string
  | DLambda of string * sigma * delta
  | DAnd of delta * delta
  | DApp of delta * delta
  | DRight of delta
  | DLeft of delta

	       (* useless
type bruijndelta =
  | BDMark of string * bool * int (* varname * bound? * bruijn index *)
  | BDLambda of sigma * bruijndelta
  | BDAnd of bruijndelta * bruijndelta
  | BDApp of bruijndelta * bruijndelta
  | BDRight of bruijndelta
  | BDLeft of bruijndelta
		*)

type gamma = (string * string * sigma) list (* var * mark * type *)

type judgment = {
  g : gamma;
  m : m;
  s : sigma
}

type derivation =
  | ANull
  | AMark of string
  | AFcI of (judgment * derivation)
  | AFcE of (judgment * derivation * derivation)
  | AAndI of (judgment * derivation * derivation)
  | AAndEL of (judgment * derivation)
  | AAndER of (judgment * derivation)

type pb = {
  mutable judg : judgment option;
  mutable jlist : judgment list;
  mutable derivation : derivation
}

type pb_tot = pb list

type opt =
  | OFcI
  | OFcE of sigma
  | OVar
  | OBacktrack
  | OAndI
  | OAndEL of sigma
  | OAndER of sigma
(* TODO : OChangeGoal *)

let rec to_bruijn m =
  let rec update b x n =
    match b with
    | BVar (y,false,_) -> if (y = x) then BVar(y, true, n) else b
    | BVar (_,true,_) -> b
    | BLambda b' -> BLambda (update b' x (n+1))
    | BApp (b', b'') -> BApp (update b' x n, update b'' x n)
  in
  match m with
  | MVar x -> BVar(x, false, 0)
  | MLambda (x, i, m') -> BLambda (update (to_bruijn m') x 0)
  | MApp (m', m'') -> BApp (to_bruijn m', to_bruijn m'')

			   (* useless
let rec to_bruijndelta m =
  let rec update b x n =
    match b with
    | BDMark (y,false,_) -> if (y = x) then BDMark(y, true, n) else b
    | BDMark (_,true,_) -> b
    | BDLambda (s, b') -> BDLambda (s, update b' x (n+1))
    | BDAnd (b', b'') -> BDAnd (update b' x n, update b'' x n)
    | BDApp (b', b'') -> BDApp (update b' x n, update b'' x n)
    | BDRight b' -> BDRight (update b' x n)
    | BDLeft b' -> BDLeft (update b' x n)
  in
  match m with
  | DMark x -> BDMark(x, false, 0)
  | DLambda (x, s, m') -> BDLambda (s, (update (to_bruijndelta m') x 0))
  | DAnd (m', m'') -> BDAnd (to_bruijndelta m', to_bruijndelta m'')
  | DApp (m', m'') -> BDApp (to_bruijndelta m', to_bruijndelta m'')
  | DRight m' -> BDRight (to_bruijndelta m')
  | DLeft m' -> BDLeft (to_bruijndelta m')
		*)

let alpha_conversion m n =
  let rec foo b c =
    match b, c with
    | BVar (x,false,_), BVar(y,false,_) -> x = y (* free variables *)
    | BVar (_,true, x), BVar(_,true,y) -> x = y (* bound variables *)
    | BLambda b', BLambda c' -> foo b' c'
    | BApp (b', b''), BApp (c', c'') -> foo b' c' && foo b'' c''
    | _, _ -> false
  in
  foo (to_bruijn m) (to_bruijn n)

let rec find_sigma x l =
  match l with
  | [] -> failwith "empty list"
  | (y, _, sigma) :: _ when x = y -> sigma
  | _ :: l -> find_sigma x l

let rec find_x i sigma l =
  match l with
  | [] -> failwith "empty list"
  | (x, j, sigma') :: _ when j = i && sigma = sigma' -> x
  | _ :: gam -> find_x i sigma gam

let rec find_i x sigma l =
  match l with
  | [] -> failwith "empty list"
  | (y, i, sigma') :: _ when x = y && sigma = sigma' -> i
  | _ :: l -> find_i x sigma l

let rec sigma_to_string sigma =
  match sigma with
  | SAtom x -> x
  | SFc (sigma1, sigma2) ->
     let s1 = sigma_to_string sigma1
     and s2 = sigma_to_string sigma2 in "(" ^ s1 ^ ") -> (" ^ s2 ^ ")"
  | SAnd (sigma1, sigma2) ->
     let s1 = sigma_to_string sigma1
     and s2 = sigma_to_string sigma2 in "(" ^ s1 ^ ") & (" ^ s2 ^ ")"

let rec m_to_string m =
  let rec aux m =
    match m with
    | MVar sm -> sm
    | _ -> let sm = m_to_string m in "(" ^ sm ^ ")"
  in
  match m with
  | MVar s -> s
  | MLambda (s, i, m) ->
     let t = aux m in
     "\\" ^ s ^ ":"^i^". " ^ t
  | MApp (m1, m2) ->
     let t1 = aux m1
     and t2 = aux m2 in
     t1 ^ " " ^ t2

let rec delta_to_string d =
  let rec aux delta =
    match delta with
    | DMark i -> i
    | _ -> let sd = delta_to_string delta in "(" ^ sd ^ ")"
  in
  match d with
  | DMark i -> i
  | DLambda (i, s, d) ->
     let t = aux d in
     "\\" ^ i ^ ":" ^ (sigma_to_string s) ^ ". " ^ t
  | DApp (d1, d2) ->
     let t1 = aux d1
     and t2 = aux d2 in
     t1 ^ " " ^ t2
  | DAnd (d1, d2) ->
     let t1 = aux d1
     and t2 = aux d2 in
     t1 ^ " & " ^ t2
  | DLeft d ->
     let t = aux d in
     "<= " ^ t
  | DRight d ->
     let t = aux d in
     t ^ " =>"

let judgment_to_string t =
  let rec aux_g l =
    match l with
    | [] -> "]"
    | [x, i, s] ->
       " " ^ x ^ "@" ^ i ^ " : " ^ (sigma_to_string s) ^ " ]"
    | (x, i, s) :: l ->
       " " ^ x ^ "@" ^ i ^ " : " ^ (sigma_to_string s) ^ " ;" ^ (aux_g l)
  in
  "[" ^ aux_g t.g ^ " > " ^ m_to_string t.m ^ " @ ? : " ^ sigma_to_string t.s

let print_pb pb =
  let aux1 () =
    match pb.judg with
    | Some t ->
       begin
	 print_string "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n<> goal to achieve :\n\n";
	 print_string ("   " ^ (judgment_to_string t) ^ "\n\n");
       end
    | None -> failwith "empty pb";
  and aux2 () =
    match pb.jlist with
    | [] -> ()
    | _ ->
       let rec aux l =
	 match l with
	 | [] -> ()
	 | t::l ->
	    begin
	      print_string (" - " ^ (judgment_to_string t) ^ "\n\n");
	      aux l
	    end
       in
       begin
	 print_string "<> other goal(s) :\n\n";
	 aux pb.jlist;
       end
  in
  begin
    aux1 ();
    aux2 ();
    print_string "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n"
  end
