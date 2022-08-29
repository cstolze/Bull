let () = ignore (Interface.main ())

                (* BUGS
If unification fails, then id is still registered. (see bug1.bull) DONE

If there is a lexer error in a file, the parser will loop infinitely. DONE

Set errors are difficult to decipher (see bug2.bull)
Idea: use a list of locations (there should be 1 or 2 locations during an error, I don't know if there are other cases possible.
                 *)

                (*
Error messages:

The term "C (vect ?n)" has type "U (vect ?n)"
while it is expected to have type "U nat".


The following term contains unresolved implicit arguments:
  (U (vect ?n))
More precisely:
- ?n: Cannot infer this placeholder of type "nat".
                 *)
