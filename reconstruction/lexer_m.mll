{open Parser_m}

rule lecture = parse
	| ['\n' '\t'] {lecture lexbuf}
	| '(' {POUVR}
	| ')' {PFERM}
	| "\\" {LAMBDA}
	| ". " {AS}
	| ' ' {AP}
	| ':' {PRES}
	| ['0' - '9']+ as s {let i = int_of_string s in INT i}
	| ['a' - 'z']+ as x {VAR x}
	| eof {EOF}
