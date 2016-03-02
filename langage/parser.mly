%{open Definitions%}

%token POUV
%token PFER
%token COUV
%token CFER
%token LOUV
%token LFER
%token PV
%token <int> INT
%token <string> VAR
%token IF
%token THEN
%token ELSE
%token AND
%token OR
%token XOR
%token NOT
%token PLUS
%token TIMES
%token MINUS
%token POW
%token PRED
%token ISZ
%token LESS
%token LET
%token EG
%token IN
%token FUN
%token AS
%token TRUE
%token FALSE
%token HD
%token MAP
%token CONS
%token FST
%token SND
%token NXP
%token EOF

%start p
%type <Definitions.parse> p

%%

l :
	| p PV l {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+4;
							m = MApp (MApp (Lists.cons k, ps1.m), ps2.m)}}
	| p LFER {let ps = $1 in {k = ps.k + 6;
							m = MApp (MApp (Lists.cons ps.k, ps.m), Lists.empty (ps.k+4))}}
;

p :
	| POUV p PFER {$2}
	
	| COUV p PV p CFER {let ps1 = $2 and ps2 = $4 in let k = max ps1.k ps2.k in {k = k+3;
							m = MApp (MApp (Pair.pair k, ps1.m), ps2.m)}}
	| FST p {let ps = $2 in {k = ps.k+3;
							m = MApp (Pair.fst ps.k, ps.m)}}
	| SND p {let ps = $2 in {k = ps.k+3;
							m = MApp (Pair.snd ps.k, ps.m)}}
	| NXP p p {let ps1 = $2 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+6;
							m = MApp (MApp (Pair.nextpair k, ps1.m), ps2.m)}}
							
	| IF p THEN p ELSE p {let ps1 = $2 and ps2 = $4 and ps3 = $6 in let k = max (max ps1.k ps2.k) ps3.k in {k = k+3;
							m = MApp (MApp (MApp (Bool.ifthenelse k, ps1.m), ps2.m), ps3.m)}}
	| p AND p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+4;
							m = MApp (MApp (Bool.et k, ps1.m), ps2.m)}}
	| p OR p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+4;
							m = MApp (MApp (Bool.ou k, ps1.m), ps2.m)}}
	| p XOR p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+4;
							m = MApp (MApp (Bool.xor k, ps1.m), ps2.m)}}
	| NOT p {let ps = $2 in {k = ps.k+3;
							m = MApp (Bool.non ps.k, ps.m)}}
	| TRUE {{k = 2; m = Bool.vrai 0}}
	| FALSE {{k = 2; m = Bool.faux 0}}
	
	| LOUV l {$2}
	| MAP p {let ps = $2 in {k = ps.k+5;
							m = MApp (Lists.map ps.k, ps.m)}}
	| HD p p {let ps1 = $2 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+4;
							m = MApp (MApp (Lists.head k, ps1.m), ps2.m)}}
	| CONS p p {let ps1 = $2 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+4;
							m = MApp (MApp (Lists.cons k, ps1.m), ps2.m)}}

	| INT {let k, m = Ent.n_to_lambda $1 in {k=k; m=m}}
	| p PLUS p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+4;
							m = MApp (MApp (Ent.plus k, ps1.m), ps2.m)}}
	| p MINUS p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+11;
							m = MApp (MApp (Ent.sub k, ps1.m), ps2.m)}}
	| p TIMES p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+3;
							m = MApp (MApp (Ent.fois k, ps1.m), ps2.m)}}
	| p POW p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+2;
							m = MApp (MApp (Ent.exp k, ps1.m), ps2.m)}}
	| PRED p {let ps = $2 in {k = ps.k+9;
							m = MApp (Ent.pred ps.k, ps.m)}}
	| ISZ p {let ps = $2 in {k = ps.k+4;
							m = MApp (Ent.iszero ps.k, ps.m)}}
	| p LESS p {let ps1 = $1 and ps2 = $3 in let k = max ps1.k ps2.k in {k = k+13;
							m = MApp (MApp (Ent.lessthan k, ps1.m), ps2.m)}}
							
	| LET VAR EG p IN p {let ps1 = $4 and ps2 = $6 in let k = max ps1.k ps2.k in{k = k+1;
							m = MApp (MLambda ($2, k, ps2.m), ps1.m)}}
	| FUN VAR AS p {let ps = $4 in {k = ps.k+1;
							m = MLambda ($2, ps.k, ps.m)}}
	| VAR {{k = 0; m = MVar $1}}
	| p p {let ps1 = $1 and ps2 = $2 in let k = max ps1.k ps2.k in {k = k;
							m = MApp (ps1.m, ps2.m)}}
;
