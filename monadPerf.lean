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


def timeIO (action : Unit → α) : IO α := do
  let start ← IO.monoMsNow
  let result := action ()
  let stop ← IO.monoMsNow
  IO.println s!"Time: {stop - start} ms"
  return result

def main : IO Unit := do
  let n := 10000000

  IO.println "== Pure version =="
  let res ← (timeIO <| (fun _ => pureSum 0 (n)))
  IO.println res

  IO.println "== Monadic version =="
  -- let a ← (monadicSum n).run 0
  -- let a :=((monadicSum n).run 0).run |>.snd
  let res2 ← timeIO (fun _ => ((monadicSum n).run 0).run)
  IO.println res2
  -- timeIO <| (monadicSum n).run 0 >>= (fun (_, s) => IO.println s)


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
-- #eval main
-- #eval main
-- #eval main
