type sigma =
	| SFc of sigma * sigma
	| SEt of sigma * sigma
	| SA

type m =
	| MVar of string
	| MLambda of string * int * m
	| MApp of m * m

type bruijn =
  | BVar of string * bool * int (* varname * bound? * bruijn index *)
  | BLambda of bruijn
  | BApp of bruijn * bruijn

type delta =
	| DMark of int
	| DLambda of int * sigma * delta
	| DEt of delta * delta
	| DApp of delta * delta
	| DDt of delta
	| DGc of delta

type gamma = (string * int * sigma) list

type trip = {
	g : gamma;
	m : m;
	s : sigma
	}

type arbuste =
	| ARien
	| AMark of int
	| AFcI of (trip * arbuste)
	| AFcE of (trip * arbuste * arbuste)
	| AEtI of (trip * arbuste * arbuste)
	| AEtEL of (trip * arbuste)
	| AEtER of (trip * arbuste)

type prems =
	| Rien
	| Qqch of trip

type pb = {
	mutable prems : prems;
	mutable deuz : trip list;
	mutable arbuste : arbuste
	}

type pb_tot = pb list

type opt =
	| OFcI
	| OFcE of sigma
	| OVar
	| OBacktrack
	| OEtI
	| OEtEL of sigma
	| OEtER of sigma

let var k = "x"^(string_of_int k)

let rec to_bruijn m =
  let rec update b x n =
    match b with
    | BVar (y,false,_) -> if (y = x) then BVar(y, true, n) else b
    | BVar (_,true,_) -> b
    | BLambda b' -> update b' x (n+1)
    | BApp (b', b'') -> BApp (update b' x (n+1), update b'' x (n+1))
  in
  match m with
  | MVar x -> BVar(x, false, 0)
  | MLambda (x, i, m') -> BLambda (update (to_bruijn m') x 0)
  | MApp (m', m'') -> BApp (to_bruijn m', to_bruijn m'')

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

let rec trouve_sigma x =
	function
	| [] -> failwith "vide wtf?"
	| (y, _, sigma) :: _ when x = y -> sigma
	| _ :: l -> trouve_sigma x l

let rec trouve_x i sigma : (string * int * sigma) list -> string =
	function
		| [] -> failwith "vide wtf?"
		| (x, j, sigma') :: _ when j = i && sigma = sigma' -> x
		| _ :: gam -> trouve_x i sigma gam

let rec trouve_i x sigma =
	function
		| [] -> failwith "vide wtf?"
		| (y, i, sigma') :: _ when x = y && sigma = sigma' -> i
		| _ :: l -> trouve_i x sigma l		 

let rec sigma_to_string sigma =
			match sigma with
				| SA -> "a"
				| SFc (sigma1, sigma2) ->
					let s1 = sigma_to_string sigma1
					and s2 = sigma_to_string sigma2 in (
						match s1, s2 with
						| "a", "a" -> "a -> a"
						| "a", _ -> "a -> (" ^ s2 ^ ")"
						| _, "a" -> "(" ^ s1 ^ ") -> a"
						| _, _ -> "(" ^ s1 ^ ") -> (" ^ s2 ^ ")"
					)
				| SEt (sigma1, sigma2) ->
					let s1 = sigma_to_string sigma1
					and s2 = sigma_to_string sigma2 in (
						match s1, s2 with
						| "a", "a" -> "a & a"
						| "a", _ -> "a & (" ^ s2 ^ ")"
						| _, "a" -> "(" ^ s1 ^ ") & a"
						| _, _ -> "(" ^ s1 ^ ") & (" ^ s2 ^ ")"
					)

let rec m_to_string =
	let rec aux m =
		match m with
			| MVar sm -> sm
			| _ -> let sm = m_to_string m in "(" ^ sm ^ ")"
	in
	function
	| MVar s -> s
	| MLambda (s, i, m) ->
		let t = aux m in
		"\\" ^ s ^ ":"^(string_of_int i)^". " ^ t
	| MApp (m1, m2) ->
		let t1 = aux m1
		and t2 = aux m2 in
		t1 ^ " " ^ t2

let rec delta_to_string : delta -> string =
	let rec aux (delta : delta) =
		match delta with
			| DMark i -> string_of_int i
			| _ -> let sd = delta_to_string delta in "(" ^ sd ^ ")"
	in
	function
	| DMark i -> string_of_int i
	| DLambda (i, s, d) ->
		let t = aux d in
		"\\" ^ (string_of_int i) ^ ":" ^ (sigma_to_string s) ^ ". " ^ t
	| DApp (d1, d2) ->
		let t1 = aux d1
		and t2 = aux d2 in
		t1 ^ " " ^ t2
	| DEt (d1, d2) ->
		let t1 = aux d1
		and t2 = aux d2 in
		t1 ^ " & " ^ t2
	| DGc d ->
		let t = aux d in
		"<= " ^ t
	| DDt d ->
		let t = aux d in
		t ^ " =>"

let trip_to_string t =
	let rec aux_g =
		function
		| [] -> "]"
		| [x, i, s] ->
			" " ^ x ^ "@" ^ (string_of_int i) ^ " : " ^ (sigma_to_string s) ^ " ]"
		| (x, i, s) :: l ->
			" " ^ x ^ "@" ^ (string_of_int i) ^ " : " ^ (sigma_to_string s) ^ " ;" ^ (aux_g l)
	in
	"[" ^ aux_g t.g ^ " > " ^ m_to_string t.m ^ " @ ? : " ^ sigma_to_string t.s

let print_pb pb =
	let aux1 () =
		match pb.prems with
			| Qqch t -> 
				begin
					print_string "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n<> goal to achieve :\n\n";
					print_string ("   " ^ (trip_to_string t) ^ "\n\n");
				end
			| Rien -> failwith "pb vide";
	and aux2 () = 
		match pb.deuz with
			| [] -> ()
			| _ ->
				let rec aux =
					function
					| [] -> ()
					| t::l ->
						begin
							print_string (" - " ^ (trip_to_string t) ^ "\n\n");
							aux l
						end
				in
				begin
					print_string "<> other goal(s) :\n\n";
					aux pb.deuz;
				end
	in
	begin
		aux1 ();
		aux2 ();
		print_string "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n"
	end
