%{open Definitions%}

%token POUVR
%token PFERM
%token <string> VAR
%token LAMBDA
%token <int> INT
%token AS
%token AP
%token EOF
%token PRES

%left AP

%start m
%type <Definitions.m> m

%%

m :
	| POUVR m PFERM {$2}
	| l AS m {let v, i = $1 in MLambda (v, i, $3)}
	| m AP m {MApp ($1, $3)}
	| VAR {MVar $1}

l :
	| LAMBDA VAR PRES INT {($2, $4)}
