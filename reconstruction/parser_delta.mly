%{open Definitions%}

%token OPENP
%token CLOSP
%token LAMBDA
%token <string> VAR
%token AS
%token AL
%token AR
%token FC
%token AND
%token EOF
%token COLON

%left AS

%start d
%type <Definitions.delta> d

%%

d :
	| OPENP d CLOSP {$2}
	| l AS d {let i, s = $1 in DLambda (i, s, $3)}
	| d d {DApp ($1, $2)}
	| VAR {DMark $1}
	| d AR {DRight $1}
	| AL d {DLeft $2}
	| d AND d {DAnd ($1, $3)}
;

l :
	| LAMBDA VAR COLON s {($2, $4)}
;

s:
	| s FC s {SFc ($1, $3)}
	| s AND s {SAnd ($1, $3)}
	| VAR {SAtom}
	| OPENP s CLOSP {$2}
;
