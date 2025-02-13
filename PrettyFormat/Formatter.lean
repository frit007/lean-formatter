import Lean
import PrettyFormat



@[pFormat «arith_+_»]
def formatPlus: PrettyFormat.FormatPPL
  | a => return (PrettyFormat.text " -- TODO: improve custom formatter for arith_+_ 22" <> PrettyFormat.PPL.nl)
