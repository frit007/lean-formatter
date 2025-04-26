import CoreFormatters
import LSPformat
import Lean


open Lean


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
-- bubbledComment
def ofList (l : List Name) : NameSet := l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
def ofList (l : List Name -- bubbledComment
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
