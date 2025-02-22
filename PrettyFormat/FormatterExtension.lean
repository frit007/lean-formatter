import Lean
import PrettyFormat

open PrettyFormat

@[pFormat «arith_+_»]
def formatPlus: Rule
| a => return (text " -- TODO: improve custom formatter for arith_+_ 22" <> PPL.nl)
