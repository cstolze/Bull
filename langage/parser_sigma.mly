%{open Definitions%}

%token POUVR
%token PFERM
%token A
%token ET
%token FC
%token EOF
%token INT

%right FC

%start s
%type <Definitions.sigma> s

%%

s:	
	| s FC s {SFc ($1, $3)}
	| s ET s {SEt ($1, $3)}
	| A {SA}
	| s INT {let a = SFc ($1, $1) in SFc (a, a)}
	| POUVR s PFERM {$2}
;
