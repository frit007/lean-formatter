# installation
Add the project as a dependency to your project

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
### adding a new formatter
For example this would be the formatter for the `termIfThenElse` Syntax.
```
-- use #fmt during development, but #coreFmt if your formatter gets added to Coreformatters
#fmt termIfThenElse fun
| #[ifAtom, condition, thenAtom, positiveBody, elseAtom, negativeBody] => do
  let condition ← formatStx condition
  let positiveBody ← formatStx positiveBody
  let negativeBody ← formatStx negativeBody

  let content := " " <> condition <> " " <> thenAtom <> nestDoc 2 ("" <$$> positiveBody) <$$> elseAtom <> nestDoc 2 ("" <$$> negativeBody)
  return ifAtom <> (content.group)
| _ => failure
```