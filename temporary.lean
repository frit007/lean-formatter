import temporary_imported

def main : IO Unit := do
    let prev ← counter.get
    let _ ← counter.set (prev + 1)
    let updated ← counter.get
    IO.println (prev)

#eval main -- 0
#eval main -- 1
#eval main -- 11 (changes every time the lines changes)
