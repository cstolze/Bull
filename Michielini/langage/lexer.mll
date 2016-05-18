{open Parser}

rule lecture = parse
	| [' ' '\n' '\t'] {lecture lexbuf}
	| '{' {COUV}
	| '}' {CFER}
	| '[' {LOUV}
	| ']' {LFER}
	| '(' {POUV}
	| ')' {PFER}
	| ';' {PV}
	| "fst" {FST}
	| "snd" {SND}
	| "nextpair" {NXP}
	| "::" {CONS}
	| "if" {IF}
	| "then" {THEN}
	| "else" {ELSE}
	| "let" {LET}
	| '=' {EG}
	| "in" {IN}
	| "fun" {FUN}
	| "->" {AS}
	| "true" {TRUE}
	| "false" {FALSE}
	| "hd" {HD}
	| "map" {MAP}
	| "and" {AND}
	| "or" {OR}
	| "xor" {XOR}
	| '+' {PLUS}
	| '-' {MINUS}
	| '*' {TIMES}
	| '^' {POW}
	| "pred" {PRED}
	| "iszero" {ISZ}
	| "<=" {LESS}
	| ['0' - '9']+ as s {INT (int_of_string s)}
	| ['a' - 'z']+ + ['a' - 'z' '0' - '9']* as s {VAR s}
	| eof {EOF}
