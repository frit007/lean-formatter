import Lean
import Init.Control.StateRef
open ST

-- import Init.System.IOError
-- import Init.System.FilePath
-- import Init.System.ST
-- import Init.Data.Ord
-- open System

-- def myExample : Nat := runST do
--   -- ST.run do
--   let r ← IO.mkRef 0
--   r.modify (· + 5)
--   ← r.get



structure LocalCounter (s : Type) where
  count : ST.Ref s Nat

inductive Doc (α : Type) where
| text (s : String)
| nl (s : String)
| concat (lhs rhs : α)
| choice (lhs rhs : α)

structure Cache where
  -- flatten / bridge configuration
  cost : Nat -- use actual cost factory
  layout : List String → List String -- use MeasureSet instead

structure PPL where
  d : Doc PPL
  cache : IO.Ref (List Cache)

def example3 : IO Nat := do
  let r ← IO.mkRef 0        -- create a mutable reference to 0
  r.modify (· + 5)          -- increment by 5
  let val ← r.get           -- read the value
  return val


def createDoc : IO PPL := do
  let main :PPL := {d := (Doc.text "hello :)"), cache := (← IO.mkRef [])}
  let choice :PPL := {d := (Doc.concat main main), cache := (← IO.mkRef [])}
  return choice

partial def explore (p : PPL) : IO Unit:= do
  match p.d with
  | .text (s:String) =>
    let c : Cache := {cost:= 2, layout := (fun (s) => "s"::s) }
    p.cache.modify (fun curr => c::curr)
    let after ← p.cache.get
    IO.println s!"counts : {after.length}"
    return ()
  | .nl (s : String) => return ()
  | .concat (lhs) (rhs) =>
    explore lhs
    explore rhs
    return ()
  | .choice (lhs) (rhs) =>
    explore lhs
    explore rhs
    return ()


#eval do explore (← createDoc)

def makeAndUseCounter : Nat :=
  runST (σ) do
    let r ← ST.mkRef 0
    let c : LocalCounter _ := { count := r }
    c.count.modify (· + 10)
    c.count.get


private def mkPatternRefMap (e : Expr) : Nat :=
  runST go
where
  go (σ) : ST σ (Nat) := do
  let r ← ST.mkRef 2        -- create a mutable reference to 0
  r.modify (· + 5)          -- increment by 5
  let val ← r.get           -- read the value
  return val

#eval example3
