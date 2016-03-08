{open Parser_m}

rule read = parse
	| ['\n' ' ' '\t'] {read lexbuf}
	| '(' {OPENP}
	| ')' {CLOSP}
	| "\\" {LAMBDA}
	| "." {AS}
	| ':' {COLON}
	| ['0' - '9']+ as s {let i = int_of_string s in INT i}
	| ['a' - 'z']+ as x {VAR x}
	| eof {EOF}
