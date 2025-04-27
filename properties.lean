axiom a : Nat
axiom b : Nat
axiom c : Nat
axiom d : Nat
axiom e : Nat

axiom h1: a = b
axiom h2: b = c + 1
axiom h3: c = d
axiom h4: e = 1 + d

theorem T : a = e :=
  calc
    a = b := h1
    b = c + 1 := h2
    c + 1 = d + 1 := congrArg Nat.succ h3
    d + 1 = 1 + d := by rw [Nat.add_comm]
    1 + d = e := Eq.symm h4

#check T
#print T
