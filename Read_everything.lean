import Lean

open Lean
open Lean.Parser
open Lean.Elab

-- comments?

def a (x:Nat):=
  -- pls keep :)
  x * 2

private def mkEOI (pos : String.Pos) : Syntax :=
  let atom := mkAtom (SourceInfo.original "".toSubstring pos "".toSubstring pos) ""
  mkNode ``Command.eoi #[atom]


private partial def mkErrorMessage (c : InputContext) (pos : String.Pos) (stk : SyntaxStack) (e : Parser.Error) : Message := Id.run do
  let mut pos := pos
  let mut endPos? := none
  let mut e := e
  unless e.unexpectedTk.isMissing do
    -- calculate error parts too costly to do eagerly
    if let some r := e.unexpectedTk.getRange? then
      pos := r.start
      endPos? := some r.stop
    let unexpected := match e.unexpectedTk with
      | .ident .. => "unexpected identifier"
      | .atom _ v => s!"unexpected token '{v}'"
      | _         => "unexpected token"  -- TODO: categorize (custom?) literals as well?
    e := { e with unexpected }
    -- if there is an unexpected token, include preceding whitespace as well as the expected token could
    -- be inserted at any of these places to fix the error; see tests/lean/1971.lean
    if let some trailing := lastTrailing stk then
      if trailing.stopPos == pos then
        pos := trailing.startPos
  { fileName := c.fileName
    pos := c.fileMap.toPosition pos
    endPos := c.fileMap.toPosition <$> endPos?
    keepFullRange := true
    data := toString e }

where
  -- Error recovery might lead to there being some "junk" on the stack
  lastTrailing (s : SyntaxStack) : Option Substring :=
    s.toSubarray.findSomeRevM? (m := Id) fun stx =>
      if let .original (trailing := trailing) .. := stx.getTailInfo then pure (some trailing)
        else none

private def consumeInput (inputCtx : InputContext) (pmctx : ParserModuleContext) (pos : String.Pos) : String.Pos :=
  let s : ParserState := { cache := initCacheForInput inputCtx.input, pos := pos }
  let s := tokenFn [] |>.run inputCtx pmctx (getTokenTable pmctx.env) s
  match s.errorMsg with
  | some _ => pos + ' '
  | none   => s.pos

@[inline] def myCommandParser (rbp : Nat := 0) : Parser :=
  categoryParser `command rbp

def myTopLevelParserFn : ParserFn :=
  myCommandParser.fn

def myParseCommand (inputCtx : InputContext) (pmctx : ParserModuleContext) (mps : ModuleParserState) (messages : MessageLog) : Syntax × ModuleParserState × MessageLog := Id.run do
  let mut pos := mps.pos
  let mut recovering := mps.recovering
  let mut messages := messages
  let mut stx := Syntax.missing  -- will always be assigned below
  repeat
    if inputCtx.input.atEnd pos then
      stx := mkEOI pos
      break
    let pos' := pos
    let p := andthenFn whitespace myTopLevelParserFn
    -- let p := andthenFn whitespace topLevelCommandParserFn
    let s := p.run inputCtx pmctx (getTokenTable pmctx.env) { cache := initCacheForInput inputCtx.input, pos }
    -- IO.println s!"syntax: {stx}"
    -- save errors from sub-recoveries
    for (rpos, rstk, recovered) in s.recoveredErrors do
      messages := messages.add <| mkErrorMessage inputCtx rpos rstk recovered
    pos := s.pos
    if recovering && !s.stxStack.isEmpty && s.stxStack.back.isAntiquot then
      -- top-level antiquotation during recovery is most likely remnant from unfinished quotation, ignore
      continue
    match s.errorMsg with
    | none =>
      stx := s.stxStack.back
      recovering := false
      break
    | some errorMsg =>

      messages := messages.add <| mkErrorMessage inputCtx s.pos s.stxStack (Error.mk stx (s!"&&&&&&&&&&&&& {errorMsg}") [])
      -- advance at least one token to prevent infinite loops
      if pos == pos' then
        pos := consumeInput inputCtx pmctx pos
      /- We ignore commands where `getPos?` is none. This happens only on commands that have a prefix comprised of optional elements.
          For example, unification hints start with `optional («scoped» <|> «local»)`.
          We claim a syntactically incorrect command containing no token or identifier is irrelevant for intellisense and should be ignored. -/
      -- let ignore := s.stxStack.isEmpty || s.stxStack.back.getPos?.isNone
      unless recovering do
        messages := messages.add <| mkErrorMessage inputCtx s.pos s.stxStack errorMsg
      recovering := true
      -- if ignore then
      --   continue
      -- else
      stx := s.stxStack.back
        -- break
  return (stx, { pos, recovering }, messages)

-- Function to get the syntax of an entire file
def parseFile (filePath : System.FilePath) : IO Syntax :=
  do
    -- Read the file content
    let fileContent ← IO.FS.readFile filePath
    -- Parse the file content into syntax
    let inputCtx := Parser.mkInputContext fileContent filePath.toString
    -- let inputCtx := mkInputContext contents fname
    let (header, state, messages) ← parseHeader inputCtx
    let env ← Lean.mkEmptyEnvironment --

    match myParseCommand inputCtx { env := env, options := {} } state messages with
    | (stx, state, msgs) =>
      -- let aaa <-msgs.forM (fun msg w => IO.println msg.caption)
      -- IO.println s!"syntax: {msgs}"
      return stx

def parseFileEverything (inputCtx: InputContext) (modCtx: ParserModuleContext) (state: ModuleParserState) (msgs : MessageLog) (gas :Nat): IO (MessageLog × List Syntax) :=
  match gas with
  | 0 => return (msgs, [])
  | n +1 =>
    do
      match myParseCommand inputCtx modCtx state msgs with
      | (stx, state, msgs) =>
        -- IO.println s!"syntax: {stx}"
        if isTerminalCommand stx then
          return (msgs, [])
        else
          let (msgs2, c) ← parseFileEverything inputCtx modCtx state msgs n
          return (msgs2, stx::c)

def parseFileEverythingIntro (filePath: System.FilePath): IO (List Syntax) :=
  do
    -- Read the file content
    let fileContent ← IO.FS.readFile filePath
    -- Parse the file content into syntax
    let inputCtx := Parser.mkInputContext fileContent filePath.toString
    -- let inputCtx := mkInputContext contents fname
    let (header, state, messages) ← parseHeader inputCtx
    let env ← Lean.mkEmptyEnvironment --

    let (msgs, s) ← parseFileEverything inputCtx { env := env, options := {} } state messages 8
    msgs.forM fun msg => msg.toString >>= IO.println

    return s
    -- match Parser.parseCommand inputCtx { env := env, options := {} } state messages with
    -- | (stx, state, msgs) =>
    --   IO.println s!"syntax{stx}"
    --   return stx

-- Example usage
#eval do
  let filePath := System.FilePath.mk "./Read_everything.lean"
  let s ← parseFileEverythingIntro filePath
  IO.println s!"Parsed s:\n{s}"
