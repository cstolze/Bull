Dependencies:
-------------
a recent version of ocaml, ocamllex, ocamlyacc, ocamlbuild

How to compile this program:
----------------------------
``` bash
$ ocamlbuild main.native
```

How to run this program:
------------------------

You can use [rlwap](http://linux.die.net/man/1/rlwrap):
``` bash
$ rlwrap ./main.native [initfile]
```

Or:
``` bash
$ ./main.native [initfile]
```

Example files can be found in the examples folder.

List of commands:
-----------------
```
Help.				     for a list of commands
Load "file".		      	     for loading a script file
Axiom term : type.	    	     define a constant or an axiom
Definition name [: type] := term.    define a term
Print name. 	       	  	     print the definition of name
Printall. 			     print the full environment (axioms and definitions)
Compute term.			     normalize term and print the result
Quit. 				     quit
```
Names are composed of any alphanumeric symbol, _ and '.
Terms and types have the same syntax.

Comments are enclosed between (* and *), à la Coq.

Syntax of terms:
----------------
```
| Type					   # sort Type
| let ID [args] [: term] := term in term   # let construct
| name					   # identifier
| forall x : term, term			   # dependent product
| term -> term	   			   # non-dependent product
| fun x : term => type			   # lambda-abstraction
| sforall x : term, term		   # relevant dependent product
| term >> term	    			   # relevant non-dependent product
| sfun x : term => term			   # relevant lambda-abstraction
| term term    	  			   # application
| term & term				   # intersection of types
| term | term				   # union of types
| <term, term>				   # strong pair
| proj_l term			  	   # left projection of a strong pair
| proj_r term			           # right projection of a strong pair
| smatch term [as id] [return term] with
  id [:t] => term, id [:t] => term	   # strong co-pair
| inj_l term term   	  		   # left injection
| inj_r term term			   # right injection
```

- Relevant lambda-abstractions only type terms equivalent to the identity function.
- Strong pair has an intersection type and both its arguments must share the same essence.
- the strong co-pair syntax is similar to the Coq `match` operator.
- The first argument of the injection is the type that is added in a union to the type of the
  second argument.

Source code:
------------

- interface.ml implements the REPL.
- main.ml launches Interface.main().
- env.ml implements the global and local environments.
- lexer.mll and parser.mly implements the lexer and the parser.
- utils.ml implements the types.
- bruijn.ml implements functions related to de Bruijn indexes.
- printer.ml implements function printers and error printers.
- reduction.ml implements the normalization algorithm.
- unification.ml implements the unification algorithm.
- reconstruction.ml implements the reconstruction algorithm.
- subtyping.ml implements the subtyping algorithm.
