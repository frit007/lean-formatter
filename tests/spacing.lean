import PFMT

open Pfmt

#eval
  let d := Doc.concat (spacing [space]) (Doc.choice (Doc.concat (spacing [space])  (Doc.text "b")) (Doc.concat (spacing [spaceNl]) (Doc.text "a")))
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
  out

#eval
  let d := Doc.concat (spacing [spaceNl]) (Doc.choice (Doc.concat (spacing [space])  (Doc.text "b")) (Doc.concat (spacing [spaceNl]) (Doc.text "a")))
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
  out

#eval
  let d := Doc.concat (spacing [space, spaceNl]) (Doc.choice (Doc.concat (spacing [space])  (Doc.text "bbbbbbbbbbbbbbbbbbbb")) (Doc.concat (spacing [spaceNl]) (Doc.text "a")))
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
  out

#eval
  let d := Doc.concat (spacing ["custom"]) (Doc.choice (Doc.concat (spacing ["custom"])  (Doc.text "bbbbbbbbbbbbbbbbbbbb")) (Doc.concat (spacing [spaceNl]) (Doc.text "a")))
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
  out
