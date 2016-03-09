%{open Definitions%}

%token OPENP
%token CLOSP
%token <string> VAR
%token LAMBDA
%token AS
%token EOF
%token COLON

%left AS

%start m
%type <Definitions.m> m

%%

m :
	| OPENP m CLOSP {$2}
	| l AS m {let v, i = $1 in MLambda (v, i, $3)}
	| m m {MApp ($1, $2)}
	| VAR {MVar $1}

l :
	| LAMBDA VAR COLON VAR {($2, $4)}
