# run

## Standalone
### build
lake build
### run
.lake/build/bin/runner.exe 

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

