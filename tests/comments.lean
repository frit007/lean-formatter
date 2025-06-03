import CoreFormatters
import LSPformat
import Lean


open Lean


/--
info:
def ofList (l : List Name) : NameSet := -- end Of LineComment
  l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : List Name) : NameSet := -- end Of LineComment
  l.foldl (fun s n => s.insert n) {}

/--
info:
-- bubbledComment
def ofList (l : List Name) : NameSet := l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : -- bubbledComment
  List Name
  ) : NameSet :=
  l.foldl (fun s n => s.insert n) {}


/--
info:
def ofList (l : List Name) : NameSet :=
  -- end Of LineComment
  l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : List Name) : NameSet :=
  -- end Of LineComment
  l.foldl (fun s n => s.insert n) {}


/--
info:
def ofList (l : List Name) : NameSet := l.foldl (fun s n => s.insert n) {} -- end Of LineComment
-/
#guard_msgs in
#format
def ofList (l : List Name) : NameSet :=
  l.foldl (fun s n => s.insert n) {} -- end Of LineComment

/--
info:
-- line 3
-- line 2
-- line 1
def ofList (l : List Name) : NameSet := l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l :
  -- line 1
  -- line 2
  -- line 3
  List Name) : NameSet :=
  l.foldl (fun s n => s.insert n) {}

/--
info:
-- should be moved
def ofList (l : List Name) : NameSet := l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : -- should be moved
 List Name) : NameSet :=
  l.foldl (
    fun s n => s.insert n) {}


/--
info:
def ofList (l : List Name /- should stay -/) : NameSet := l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : List Name/- should stay -/) : NameSet :=
  l.foldl ( fun s n => s.insert n) {}

/--
info:
-- fst
-- snd
def ofList (l : List Name) : NameSet := l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in -- TODO: comments somehow destroy whitespace?
#format
def ofList (l : --fst
    List --snd
    Name
  ) : NameSet :=
  l.foldl ( fun s n => s.insert n) {}

/--
info:
def ofList (l : List Name) : NameSet := /- should stay 123456 -/ l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : List Name ) : NameSet := /- should stay 123456 -/
  l.foldl ( fun s n => s.insert n) {}


/--
info:
def ofList (l : List Name) : NameSet := /- should stay 1234567 -/
  l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : List Name ) : NameSet := /- should stay 1234567 -/
  l.foldl ( fun s n => s.insert n) {}
