%{open Definitions%}

%token OPENP
%token CLOSP
%token <string> VAR
%token AND
%token FC
%token EOF

%right FC

%start s
%type <Definitions.sigma> s

%%

s:
	| s FC s {SFc ($1, $3)}
	| s AND s {SAnd ($1, $3)}
	| VAR {SAtom $1}
	| OPENP s CLOSP {$2}
;
