namespace PrettyFormat

/--
Why do we need so many flattens?
The issue is that flatten should be delayed until the outer bridges have found a value
-/
inductive Flatten where
| notFlattened
| flattenLeft
| flattenRight
| flattenEventually
| flattened
deriving DecidableEq, Repr

-- flattening has started, but not yet completed
@[inline] def Flatten.shouldFlattenNl (f : Flatten) : Bool :=
  f != Flatten.notFlattened

@[inline] def Flatten.isFlat (f : Flatten) : Bool :=
  f == flattened

@[inline] def Flatten.toInt : Flatten → UInt8
| notFlattened => 0
| flattenLeft => 1
| flattenRight => 2
| flattenEventually => 3
| flattened => 4

@[inline] def Flatten.startFlatten : Flatten → Flatten
| notFlattened => flattenEventually
| f => f


abbrev Bridge := UInt8

def bridgeNull :Bridge := 0
def bridgeFlex :Bridge := 1
def bridgeSpaceNl :Bridge := 2 -- flattens to a space
def bridgeHardNl :Bridge := 4 -- flattens to fail
-- If you allow a newline, you should also be compatible with HardNl
def bridgeNl :Bridge := bridgeSpaceNl ||| bridgeHardNl
def bridgeSpace :Bridge := 8
def bridgeNone :Bridge := 16
def bridgeImmediate :Bridge := 32
def bridgeAny := bridgeSpace ||| bridgeNl ||| bridgeHardNl
def bridgeEnding := bridgeAny ||| bridgeFlex

@[inline] def Bridge.subsetOf (l r: Bridge) : Bool :=
  (l &&& r) == l

@[inline] def Bridge.contains (l r: Bridge) : Bool :=
  (l &&& r) == r

@[inline] def Bridge.overlapsWith (l r: Bridge) : Bool :=
  l &&& r != 0

@[inline] def Bridge.lessThan (lhs rhs: Bridge) :=
  lhs.subsetOf rhs

@[inline] def Bridge.erase (lhs rhs: Bridge) :=
  lhs &&& (~~~ rhs)

@[inline] def Bridge.intersection (lhs rhs: Bridge) : Bridge :=
  lhs &&& rhs

@[inline] def Bridge.union (lhs rhs: Bridge) : Bridge :=
  lhs ||| rhs

@[inline] def Bridge.add (lhs rhs: Bridge) : Bridge :=
  lhs ||| rhs

@[inline] def Bridge.isEmpty (b : Bridge) : Bool :=
  b == 0

@[inline] def Bridge.smallerThan (lhs rhs: Bridge) : Bool :=
  lhs < rhs

partial def Bridge.parts : Bridge → List Bridge
| 0 => []
| x =>
  let one := (x &&& (~~~ (x - 1)))
  one :: Bridge.parts (x &&& (~~~ one))


@[inline] def Bridge.replaceIfExists (bridge old new : Bridge) :Bridge :=
  if bridge.contains old then
    (bridge.erase old) ||| new
  else
    bridge

@[inline] def Bridge.flatten (bridge : Bridge) : Bridge :=
  bridge.replaceIfExists bridgeSpaceNl (bridgeSpace)
    |>.erase bridgeHardNl

def Bridge.str (b : Bridge) : String := Id.run do
  let mut str := []
  let mut bridge : Bridge := b
  if bridgeNull == bridge then
    return "bridgeNull"
  if bridge.contains bridgeAny then
    str := str ++ ["bridgeAny"]
    bridge := bridge.erase bridgeAny
  if bridge.contains bridgeNl then
    str := str ++ ["bridgeNl"]
    bridge := bridge.erase bridgeNl
  if bridge.contains bridgeHardNl then
    str := str ++ ["bridgeHardNl"]
    bridge := bridge.erase bridgeHardNl
  if bridge.contains bridgeSpaceNl then
    str := str ++ ["bridgeSpaceNl"]
    bridge := bridge.erase bridgeSpaceNl
  if bridge.contains bridgeSpace then
    str := str ++ ["bridgeSpace"]
    bridge := bridge.erase bridgeSpace
  if bridge.contains bridgeImmediate then
    str := str ++ ["bridgeImmediate"]
    bridge := bridge.erase bridgeImmediate
  if bridge.contains bridgeNone then
    str := str ++ ["bridgeNone"]
    bridge := bridge.erase bridgeNone
  if bridge.contains bridgeFlex then
    str := str ++ ["bridgeFlex"]
    bridge := bridge.erase bridgeFlex
  if bridge != 0 then
    str := str ++ [toString bridge]
    bridge := bridge.erase bridgeNone
  if str.length == 1 then
    return String.join (str.intersperse "|||")
  else
    return s!"({String.join (str.intersperse "|||")})"


@[inline] def Bridge.provideIntersection (l r : Bridge) :=
  if l == bridgeFlex then
    r
  else if r == bridgeFlex then
    l
  else
    l.intersection r



@[inline] def Bridge.requireIntersection (l r : Bridge) :=
  if l == bridgeFlex && r.contains (bridgeAny ||| bridgeNone) then
    r
  else if r == bridgeFlex && l.contains (bridgeAny ||| bridgeNone) then
    l
  else
    l.intersection r

end PrettyFormat
