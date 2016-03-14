%{open Definitions%}

%start s
%type <Definitions.sentence> s

			     %%

			       s:
    | QUIT SEMICOLON
    | LOAD ID SEMICOLON
    | PROOF ID COLON family SEMICOLON
    | TYPE ID COLON kind SEMICOLON
    | CONSTANT ID COLON family SEMICOLON
    | DELTATERM ID EQUAL deltaterm [COLON family]? SEMICOLON
    | error SEMICOLON
    ;

      kind:
    | OPENP kind CLOSP
    | TYPE
    ;

      family:
    | OPENP family CLOSP
    | family ARROW family
    | family SAND family
    | family SOR family
    | ID
    | OMEGA
    ;

      deltaterm:
    | OPENP deltaterm CLOSP
    | ID
    | STAR
    | LAMBDA ID COLON family DOT deltaterm
    | deltaterm deltaterm
    | PROJLEFT deltaterm
    | PROJRIGHT deltaterm
    | INJLEFT deltaterm
    | INJRIGHT deltaterm
    | deltaterm SAND deltaterm
    | deltaterm SOR deltaterm
    ;


      proofrule:
    | OMEGA SEMICOLON
    | VAR SEMICOLON
    | INTRO SEMICOLON
    | ELIM family SEMICOLON
    | SCONJ SEMICOLON
    | PROJLEFT family SEMICOLON
    | PROJRIGHT family SEMICOLON
    | INJLEFT SEMICOLON
    | INJRIGHT SEMICOLON
    | SDISJ deltaterm COMMA family COMMA family SEMICOLON
    | error SEMICOLON
    ;
