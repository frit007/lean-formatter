import Std
open Std

-- Non-monadic version (pure recursion)
-- partial def pureSum (n : Nat) : Nat :=
--   go 0 0
--   where
--   go (i acc : Nat) : Nat :=
--     if i > n then acc else go (i + 1) (acc + i)

partial def pureSum (acc:Nat) : Nat → Nat
| 0 => acc
| n + 1 => pureSum (acc + n + 1) n
  -- go 0 0
  -- where
  -- go (i acc : Nat) : Nat :=
  --   if i > n then acc else go (i + 1) (acc + i)


-- Monadic version using StateM
def monadicSum (n : Nat) : StateM Nat Unit := do
  for i in [0:n+1] do
    modify (· + i)

def goodArraySum (n : Nat) : StateM (Array Nat) Unit := do
  for i in [0:n+1] do
    modify (fun c => c.modify 0 (· + 1))

def badArraySum (n : Nat) : StateM (Array Nat) Unit := do
  for i in [0:n+1] do
    let cache := ← get
    let updated := cache.modify (1000000) (· + 1)
    set updated

def badHashSum (n : Nat) : StateM (Std.HashMap Nat Nat) Unit := do
  for i in [0:n+1] do
    let cache := ← get
    let updated := cache.modify (0) (· + 1)
    set updated

def timeIO (action : Unit → α) : IO α := do
  let start ← IO.monoMsNow
  let result := action ()
  let stop ← IO.monoMsNow
  IO.println s!"Time: {stop - start} ms"
  return result

-- what about hashmap?

def buildMap : HashMap Nat Nat :=
  Id.run do
    let mut m := HashMap.empty
    for i in [0:10000] do
      m := m.insert i 0
    return m

def main : IO Unit := do
  let n := 100000
  let map := buildMap
  IO.println "== Pure version =="
  let res ← (timeIO <| (fun _ => pureSum 0 (n)))
  IO.println res

  IO.println "== Monadic version =="
  let res2 ← timeIO (fun _ => ((monadicSum n).run 0).run.fst)
  IO.println res2


  -- IO.println "== good array version =="
  -- let res2 ← timeIO (fun _ => ((goodArraySum n).run #[0]).run.fst)
  -- IO.println res2


  -- IO.println "== bad array version =="
  -- let res2 ← timeIO (fun _ => ((badArraySum n).run #[0]).run.fst)
  -- IO.println res2

  IO.println "== bad array version long =="
  let res2 ← timeIO (fun _ => ((badArraySum n).run (Array.range 10000000)).run.fst)
  IO.println res2

  IO.println "== good array version long =="
  let res2 ← timeIO (fun _ => ((goodArraySum n).run (Array.range 10000000)).run.fst)
  IO.println res2

  IO.println "== bad HashMap version=="
  let res2 ← timeIO (fun _ => ((badHashSum n).run (Std.HashMap.mk {})).run.fst)
  IO.println res2

  IO.println "== bad HashMap version long=="
  let res2 ← timeIO (fun _ => ((badHashSum n).run (map)).run.fst)
  IO.println res2
  -- timeIO <| (monadicSum n).run 0 >>= (fun (_, s) => IO.println s)


#eval main
#eval main
#eval main
#eval main
#eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
-- #eval main
