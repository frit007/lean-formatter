## Standalone
### Build
lake build
### Run

Format specific files
``` sh
lake exe Format -file ../batteries/Batteries/Logic.lean -include ../batteries/.lake/build/lib
```

Format an entire folder
```
lake exe Format -folder ../batteries/Batteries -include ../batteries/.lake/build/lib  -include .lake/build/lib -filesPrWorker 1 -workers 16
```
[!CAUTION]
At the moment when formatting a folder we expect the toolchain bin to be part of the users path, because it is used to interpret files in the folder. This could be this folder ".elan\toolchains\leanprover--lean4---v4.17.0-rc1\bin" depending on the version.

# Installation
Add the project as a dependency to your project
Add dependency on PrettyFormat in toml
```
[[require]]
name = "PrettyFormat"
git = "https://github.com/frit007/lean-formatter"
rev = "main"
```

# LSP formatting
To test specific changes you can use the LSP to format individual top-level commands. 
To enable this import LSP format in the file where you want to format
```
import LSPformat
```

# Writing custom formatters
If you want to format a new piece of syntax start by importing the PrettyFormat
```
-- During development use LSPformat
import LSPformat
open PrettyFormat
```

```
-- Switch to PrettyFormat when you do not need the LSP anymore
import LSPformat
open PrettyFormat
```
### Adding a new formatter
For example this would be the formatter for the `termIfThenElse` Syntax.
```
-- use #fmt during development, but #coreFmt if your formatter gets added to Coreformatters
#fmt termIfThenElse fun
| #[ifAtom, condition, thenAtom, positiveBody, elseAtom, negativeBody] => do
  let content := "" <_> condition <_> thenAtom <> nestDoc 2 ("" <$$> positiveBody) <$$> elseAtom <> nestDoc 2 ("" <$$> negativeBody)
  return ifAtom <> (content.group)
| _ => failure
```

### Configuration
We provide the following configuration options

Maximum number of characters in a line
```
set_option pf.lineLength {Nat}
```
To reduce memory usage we do not have cache every element. A larger cache distance means fewer elements get cached
```
pf.cacheDistance {Nat}
```

### debugging
We provide some debug information which can be accessed using the following flags

Output the syntax in a comment above each top level command, before being formatted
```
set_option pf.debugSyntax true
```
Output the syntax in a comment above each top level command, after being formatted (Can be useful to debug when the output only differs in whitespace)
```
set_option pf.debugSyntaxAfter true
```

debug the generated Doc (Although we recommend debugNoSolution for most usecases)
```
set_option pf.debugDoc true
```

Output the document as JSON, which can be viewed using the debugDependencies.html document. Pase the JSON in the textfield and press import
```
set_option pf.debugNoSolution true
```

Get information about failed formatting rules, this is usually caused by a formatting rule not handling all of its cases
```
set_option pf.debugErrors true
```

List syntax that do not have an associated formatting rule
```
set_option pf.debugMissingFormatters true
```