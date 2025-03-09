-- inductive MyMonad (a : Type) where
-- | Pure : MyMonad a
-- | Bind : (MyMonad a) → MyMonad a
-- inductive MyMonad  where
-- | Pure : Nat → MyMonad
-- | Bind : (MyMonad → Nat) → (Nat → MyMonad) → MyMonad

-- class MyMonad (m : Type → Type) where
--   pure : α → m α
--   bind : m α → (α → m β) → m β

-- inductive MyState where
-- | val : Nat → MyState
-- | none : MyState

-- instance : MyMonad MyState where
-- | pure x := val x
-- | bind opt next :=
--   match opt with
--   | none => none
--   | val x => next x

-- def game : MyMonad:=
--   -- MyMonad.Pure 2
--   MyMonad.Bind (fun (x:Nat) =>
--     MyMonad.Pure x
--   )
