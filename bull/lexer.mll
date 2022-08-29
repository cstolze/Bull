{open Parser}

rule read buf = parse
   | [' ' '\t'] as char { begin Buffer.add_char buf char;
				read buf lexbuf end}
   | [ '\n' ] { begin Buffer.add_char buf '\n'; Lexing.new_line lexbuf
		      ; read buf lexbuf end }
   | "(*" { begin Buffer.add_string buf "(*"; end_comment buf lexbuf; read buf lexbuf end }
   | '(' { begin Buffer.add_char buf '('; OPENP end }
   | ')' { begin Buffer.add_char buf ')'; CLOSP end }
   | '<' { begin Buffer.add_char buf '<'; LT end }
   | '>' { begin Buffer.add_char buf '>'; GT end }
   | "let" { begin Buffer.add_string buf "let"; LET end }
   | "in" { begin Buffer.add_string buf "in"; IN end }
   | "fun" { begin Buffer.add_string buf "fun"; LAMBDA end }
   | "sfun" { begin Buffer.add_string buf "sfun"; SLAMBDA end }
   | "=>" { begin Buffer.add_string buf "=>"; ENDLAMBDA end }
   | '.' { begin Buffer.add_char buf '.'; DOT end }
   | ',' { begin Buffer.add_char buf ','; COMMA end }
   | ":=" { begin Buffer.add_string buf ":="; ASSIGN end }
   | ':' { begin Buffer.add_char buf ':'; COLON end }
   | ';' { begin Buffer.add_char buf ';'; SEMICOLON end }
   | "->" { begin Buffer.add_string buf "->"; ARROW end }
   | ">>" { begin Buffer.add_string buf ">>"; SARROW end }
   | '&' { begin Buffer.add_char buf '&'; SAND end }

   | "|-" { begin Buffer.add_string buf "|-"; TURNSTILE end }

   | '|' { begin Buffer.add_char buf '|'; SOR end }
   | '_' { begin Buffer.add_char buf '_'; UNDERSCORE end }

   | '?' { begin Buffer.add_char buf '?'; QUESTION end }
   | '{' { begin Buffer.add_char buf '{'; OPENB end }
   | '}' { begin Buffer.add_char buf '}'; CLOSB end }

   | "smatch" { begin Buffer.add_string buf "smatch"; SMATCH end }
   | "as" { begin Buffer.add_string buf "as"; SMATCH end }
   | "return" { begin Buffer.add_string buf "return"; RETURN end }
   | "with" { begin Buffer.add_string buf "with"; WITH end }
   | "end" { begin Buffer.add_string buf "end"; END end }
   | "forall" { begin Buffer.add_string buf "forall"; PI end }
   | "sforall" { begin Buffer.add_string buf "sforall"; SUBSET end }
   | "coe" { begin Buffer.add_string buf "coe"; COERCION end }
   | "inj_l" { begin Buffer.add_string buf "inj_l"; INJLEFT end }
   | "inj_r" { begin Buffer.add_string buf "inj_r"; INJRIGHT end }
   | "proj_l" { begin Buffer.add_string buf "proj_l"; PROJLEFT end }
   | "proj_r" { begin Buffer.add_string buf "proj_r"; PROJRIGHT end }
   | "Quit" { begin Buffer.add_string buf "Quit"; QUIT end }
   | "Load" { begin Buffer.add_string buf "Load"; LOAD end }
   | "Lemma" { begin Buffer.add_string buf "Lemma"; LEMMA end }
   | "Type" { begin Buffer.add_string buf "Type"; TYPE end }
   | "Axiom" { begin Buffer.add_string buf "Axiom"; AXIOM end }
   | "Definition" { begin Buffer.add_string buf "Definition"; DEFINITION end }
   | "Compute" { begin Buffer.add_string buf "Compute"; COMPUTE end }
   | "Printall" { begin Buffer.add_string buf "Printall"; SIG end }
   | "Print" { begin Buffer.add_string buf "Print"; PRINT end }
   | "Help" { begin Buffer.add_string buf "Help"; HELP end }
   | "Show" { begin Buffer.add_string buf "Show"; SHOW end }

   | "Meta" { begin Buffer.add_string buf "Meta"; META end }
   | "End_meta" { begin Buffer.add_string buf "End_meta"; ENDMETA end }
   | "Add" { begin Buffer.add_string buf "Add"; ADD end }
   | "Unify" { begin Buffer.add_string buf "Unify"; UNIFY end }
   | "untyped" { begin Buffer.add_string buf "untyped"; UNTYPED end }

   | '"' [^ '"' '\n' ]* '"' as x { begin Buffer.add_string buf x; QUOTE x end }
   | ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x { begin Buffer.add_string buf x; ID x end }
   | eof {EOF}
   | _ as x { begin let x = String.make 1 x in Buffer.add_string buf x; ERR x end }
and end_comment buf = parse
   | "*)" { Buffer.add_string buf "*)" }
   | "(*" { begin Buffer.add_string buf "(*"; end_comment buf lexbuf;
		  end_comment buf lexbuf end }
   | [ '\n' ] { begin Buffer.add_char buf '\n';
		      Lexing.new_line lexbuf; end_comment buf lexbuf end }
   | _ as char { begin Buffer.add_char buf char; end_comment buf lexbuf
		 end }
