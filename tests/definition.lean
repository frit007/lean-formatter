import LSPformat



def testList : IO Unit := do
  timeit "List Prepend" do
    let mut lst := []
    for i in [1:100000] do
      lst := i :: lst
    pure ()

def testArray : IO Unit := do
  timeit "Array Append" do
    let mut arr := #[]
    for i in [1:100000] do
      arr := arr.push i
    pure ()


#eval testList
#eval testArray
