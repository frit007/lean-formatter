import CoreFormatters
import LSPformat
import Lean


namespace CustomSyntax

infixr:45 " <*-> " => fun l r => l *r - r


#eval (10 <*-> 3)

/-- info:
def add (x y:Nat) : Nat := 10 <*-> 3 -/
#guard_msgs in
#format
def add (x y:Nat): Nat :=
  2

end CustomSyntax

set_option pf.debugPPL true


/-FORMAT DEBUG:

---- Generated PPL ----
ruleDoc "Lean.Parser.Command.declaration"
 (ruleDoc "Lean.Parser.Command.definition"
   ((("def")<^>("def")
    ) <> (provideDoc bridgeSpace (/-2-/ (nestDoc 4 ((ruleDoc "Lean.Parser.Command.declId"
     (("add2")<^>("add2")
      )
    ) <> (provideDoc bridgeAny (ruleDoc "Lean.Parser.Command.optDeclSig"
     ((ruleDoc "Lean.Parser.Term.explicitBinder"
       (("(") <> (((((("x")<^>("x")
        ) <> (provideDoc bridgeSpace ("y"))) <> (provideDoc bridgeSpace ((":") <> (provideDoc bridgeSpace ("Nat"))))) <> (")"))<^>(flattenDoc (/-1-/ (((("x")<^>("x")
        ) <> (provideDoc bridgeSpace ("y"))) <> (provideDoc bridgeSpace ((":") <> (provideDoc bridgeSpace ("Nat"))))) <> (")")))
        ))
      ) <> (provideDoc bridgeAny (ruleDoc "Lean.Parser.Term.typeSpec"
       (((":")<^>(":")
        ) <> (provideDoc bridgeSpace (("Nat")<^>("Nat")
        )))
      )))
    )))) <> (provideDoc bridgeAny (ruleDoc "Lean.Parser.Command.declValSimple"
     (((nestDoc 2 (((":=")<^>(":=")
      ) <> (ruleDoc "num"
       ("2")
      )))<^>(nestDoc 2 (((":=")<^>(":=")
      ) <> (ruleDoc "num"
       ("2")
      )))
      )<^>(((nestDoc 2 (((":=")<^>(":=")
      ) <> (flattenDoc (ruleDoc "num"
       ("2")
      ))))<^>(nestDoc 2 (((":=")<^>(":=")
      ) <> (flattenDoc (ruleDoc "num"
       ("2")
      ))))
      )<^>((((requireDoc bridgeSpace) <> ((":=")<^>(":=")
      )) <> (ruleDoc "num"
       ("2")
      ))<^>(((requireDoc bridgeSpace) <> ((":=")<^>(":=")
      )) <> (ruleDoc "num"
       ("2")
      ))
      )
      )
      )
    )))))
  )

-/
def add2 (x y : Nat) : Nat :=2
