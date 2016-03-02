%{open Definitions%}

%token POUVR
%token PFERM
%token LAMBDA
%token <int> INT
%token AS
%token AP
%token EG
%token ED
%token A
%token FC
%token ET
%token EOF
%token PRES

%left AP

%start d
%type <Definitions.delta> d

%%

d :
	| POUVR d PFERM {$2}
	| l AS d {let i, s = $1 in DLambda (i, s, $3)}
	| d AP d {DApp ($1, $3)}
	| INT {DMark $1}
	| d ED {DDt $1}
	| EG d {DGc $2}
	| d ET d {DEt ($1, $3)}
;

l :
	| LAMBDA INT PRES s {($2, $4)}
;

s:	
	| s FC s {SFc ($1, $3)}
	| s ET s {SEt ($1, $3)}
	| A {SA}
	| POUVR s PFERM {$2}
;
