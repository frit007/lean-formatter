import Lean

open Lean
open Lean.Meta

abbrev Rule := String → Nat


unsafe def mkCustomAttr : IO (KeyedDeclsAttribute Rule) :=
  KeyedDeclsAttribute.init {
      builtinName := `builtin_custom,
      name := `custom,
      descr    := "some description",
      valueTypeName := `Rule
      evalKey := fun _ stx => do
      let stx ← Attribute.Builtin.getIdent stx
      let kind := stx.getId
      pure kind
  } `custom
@[init mkCustomAttr] opaque customAttr : KeyedDeclsAttribute Rule

-- split file here
-- import first_file

-- NOTE: This part has to be in a different file, otherwise the attribute will not be initialized yet (as far as I can tell it is initialized on import)
-- @[custom Lean.Parser.Term.typeSpec]
-- def formatTypeSpec : Rule
-- | a => 2

-- -- example of how it could work in a meta context
-- def metaMain (args : List String) : MetaM Unit := do
--   let env : Environment ← getEnv
--   let table := customAttr.getValues env `Lean.Parser.Term.typeSpec
--   IO.println s!"found attributes: {table.length}"
--   pure ()

-- NOTE: Again separate file is important, otherwise Lean crashes
-- #eval metaMain []

def main (args : List String) : IO Unit := do
  let env ← getEnv
  -- let env : Environment := -- getEnv some other way,
  -- let values := customAttr.getValues env `Lean.Parser.Term.typeSpec
  -- -- or maybe get the values without the environment
  -- IO.println s!"found attributes: {values.length}"
  pure ()
