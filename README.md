# run

## Standalone
### build
lake build
### run
.lake/build/bin/runner.exe 

lake exe Format -file ../batteries/Batteries/Logic.lean -include ../batteries/.lake/build/lib

lake exe Format -file ../batteries/Batteries/Data/List/Perm.lean -include ../batteries/.lake/build/lib

lake exe Format -folder ../batteries/Batteries -include ../batteries/.lake/build/lib


lake exe Format -folder ../batteries/Batteries -include ../batteries/.lake/build/lib  -include .lake/build/lib -filesPrWorker 1 -workers 16

#### hard
".lake/build/bin/Format.exe" "-file" "../batteries/Batteries/CodeAction/Misc.lean" "-include" "../batteries/.lake/build/lib" "-include" ".lake/build/lib"

".lake/build/bin/Format.exe" "-file" "../batteries/Batteries/Tactic/Case.lean" "-include" "../batteries/.lake/build/lib" "-include" ".lake/build/lib"

".lake/build/bin/Format.exe" "-file" "../batteries/Batteries/Data/RBMap/Lemmas.lean" "-include" "../batteries/.lake/build/lib" "-include" ".lake/build/lib"

".lake/build/bin/Format.exe" "-file" "../batteries/Batteries/Data/String/Lemmas.lean" "-include" "../batteries/.lake/build/lib" "-include" ".lake/build/lib"


lake exe Format -file ../batteries/Batteries/Data/Array/Match.lean -include ../batteries/.lake/build/lib

lake exe Format -file ../batteries/Batteries/Logic.lean -include ../batteries/.lake/build/lib

lake exe Format -file ../batteries/Batteries/Control/ForInStep/Basic.lean -include ../batteries/.lake/build/lib

lake exe Format -file ../batteries/Batteries/Tactic/Case.lean -include ../batteries/.lake/build/lib

lake exe Format -file ../batteries/Batteries/Data/NameSet.lean -include ../batteries/.lake/build/lib
## Files

# Overview

## PrettyFormat
Defines the types used for formatting
 - PPL

## BaseFormatter
Defines the general rules of how to format Syntax to PPL

## Annotations
Defines the specific rules used to format a function

## runner
Integration with the Lean LSP and defines the entry point for main


# simple_meta

ocamlfind ocamlc -o test -package pretty_expressive -linkpkg test.lean.ml && ./test


ocamlfind ocamlc -o test -package pretty_expressive -linkpkg bad_case.ml && ./test

eval $(opam env)