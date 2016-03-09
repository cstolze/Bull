%{open Definitions%}

%token OPENP
%token CLOSP
%token <string> VAR
%token AND
%token FC
%token EOF
%token INT

%right FC

%start s
%type <Definitions.sigma> s

%%

s:
	| s FC s {SFc ($1, $3)}
	| s AND s {SAnd ($1, $3)}
	| VAR {SAtom $1}
	| s INT {let a = SFc ($1, $1) in SFc (a, a)}
	| OPENP s CLOSP {$2}
;
