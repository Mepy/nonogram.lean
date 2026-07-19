import Std.Internal.Parsec.String
import Nonogram.LineSolver.Multi

namespace Nonogram

namespace CLI

open LineSolver.Multi

/-- A row or column selector in a runtime `line` command. -/
inductive Axis where
  | row
  | col
  deriving BEq, DecidableEq, Repr

/-- Which lines of an axis group should be processed. -/
inductive Selection where
  | indices (values : List Nat)
  | all
  deriving BEq, DecidableEq, Repr

/-- One group in a runtime `line` command. -/
inductive LineGroup where
  | axis (direction : Axis) (selection : Selection)
  | all
  | fixedPoint
  deriving BEq, DecidableEq, Repr

/-- Commands accepted by the interactive solver. -/
inductive Command where
  | newGame (seed : Option Nat)
  | exportSource
  | step
  | line (groups : List LineGroup)
  | edit (value : Cell) (row col : Nat)
  | gram
  | show
  | reveal
  | help
  | quit
  deriving BEq, DecidableEq, Repr

namespace Command

open Std.Internal Parsec
open Std.Internal.Parsec.String

private def horizontalSpace : Parser Unit := do
  discard <| many (satisfy fun char => char == ' ' || char == '\t')

private def lexeme (parser : Parser alpha) : Parser alpha := do
  let value ← parser
  horizontalSpace
  return value

private def keyword (value : String) : Parser Unit :=
  lexeme do
    discard <| pstring value
    if let some next ← peek? then
      if next.isAlphanum || next == '_' then
        fail s!"expected `{value}`"

private def natural : Parser Nat := lexeme digits

private def fixedPointGroup : Parser LineGroup := do
  keyword "**"
  return .fixedPoint

private def allGroup : Parser LineGroup := do
  keyword "*"
  return .all

private def axis : Parser Axis :=
  (keyword "row" *> pure .row) <|>
    (keyword "col" *> pure .col)

private def axisGroup : Parser LineGroup := do
  let direction ← axis
  let selection ←
    (keyword "*" *> pure Selection.all) <|>
      (do
        let values ← many natural
        return Selection.indices values.toList)
  return .axis direction selection

private def lineGroup : Parser LineGroup :=
  fixedPointGroup <|> allGroup <|> axisGroup

private def lineCommand : Parser Command := do
  keyword "line"
  return .line (← many lineGroup).toList

private def editCommand (name : String) (value : Cell) : Parser Command := do
  keyword name
  return .edit value (← natural) (← natural)

private def newGameCommand : Parser Command := do
  keyword "#new"
  let seed ←
    (do return some (← natural)) <|>
      pure none
  return .newGame seed

private def namedCommand (name : String) (command : Command) : Parser Command := do
  keyword name
  return command

private def commandParser : Parser Command := do
  ws
  let command ←
    newGameCommand <|>
      namedCommand "#export" .exportSource <|>
      namedCommand "#help" .help <|>
      namedCommand "#quit" .quit <|>
      namedCommand "#show" .show <|>
      namedCommand "#reveal" .reveal <|>
      lineCommand <|>
      editCommand "fill" .filled <|>
      editCommand "cross" .crossed <|>
      editCommand "clear" .unknown <|>
      namedCommand "gram" .gram <|>
      namedCommand "step" .step <|>
      namedCommand "show" .show <|>
      namedCommand "reveal" .reveal <|>
      namedCommand "help" .help <|>
      namedCommand "quit" .quit <|>
      namedCommand "exit" .quit
  ws
  eof
  return command

/-- Parse one CLI command using the runtime counterpart of the tactic grammar. -/
def parse (input : String) : Except String Command :=
  if input.trimAscii.isEmpty then
    .ok .step
  else
    commandParser.run input

end Command

/-- Count cells for which the board has recorded a decision. -/
def decidedCount (board : Board rows cols) : Nat :=
  (List.ofFn fun row =>
    (List.ofFn fun column => board.get row column != .unknown).count true).sum

/-- Whether every cell on a board has been decided. -/
def isComplete (board : Board rows cols) : Bool :=
  decidedCount board == rows * cols

/-- Whether a completed board records exactly this solution. -/
def matchesSolution
    (board : Board rows cols)
    (solution : Solution rows cols) : Bool :=
  (List.ofFn fun row =>
    (List.ofFn fun column =>
      board.get row column == if solution row column then .filled else .crossed).all id).all id

/-- Render a hidden solution as a fully decided board. -/
def solutionBoard (solution : Solution rows cols) : Board rows cols where
  get row column := if solution row column then .filled else .crossed

private def targetLabel : Target rows cols -> String
  | .row row => s!"row {row.val + 1}"
  | .col column => s!"col {column.val + 1}"

private def noCandidateMessage : Target rows cols -> String
  | .row row => s!"line row {row.val + 1} has no candidate"
  | .col column => s!"line col {column.val + 1} has no candidate"

private def solvedTargetMessage (solved : SolvedTarget rows cols) : String :=
  s!"line {targetLabel solved.target}: {solved.candidateCount} candidate(s)"

private def parseIndex
    (label : String)
    (bound : Nat)
    (value : Nat) : Except String (Fin bound) :=
  if _ : 0 < value then
    if hBound : value - 1 < bound then
      .ok ⟨value - 1, hBound⟩
    else
      .error s!"{label} {value} is outside the range 1..{bound}"
  else
    .error s!"{label} indices are 1-based"

/-- Apply one 1-based `fill`, `cross`, or `clear` edit. -/
def applyEdit
    (board : Board rows cols)
    (value : Cell)
    (row column : Nat) : Except String (Board rows cols) := do
  let row ← parseIndex "row" rows row
  let column ← parseIndex "column" cols column
  return board.set row column value

/-- Runtime counterpart of `gram`: require a complete board satisfying every clue. -/
def checkGram
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) : Except String Unit :=
  let unknownCount := rows * cols - decidedCount board
  if unknownCount != 0 then
    .error s!"cannot run gram: {unknownCount} cell(s) are still unknown"
  else
    let solution : Solution rows cols := fun row column => board.get row column == .filled
    if decide (solution.Satisfies puzzle) then
      .ok ()
    else
      .error "gram failed: the completed board does not satisfy the clues"

private def resolveIndices
    (direction : Axis)
    (values : List Nat) : Except String (List (Target rows cols)) :=
  match direction with
  | .row => values.mapM fun value => Target.row <$> parseIndex "row" rows value
  | .col => values.mapM fun value => Target.col <$> parseIndex "column" cols value

private def axisTargets
    (direction : Axis)
    (selection : Selection) : Except String (List (Target rows cols)) :=
  match direction, selection with
  | .row, .all => .ok (allRows rows cols)
  | .col, .all => .ok (allCols rows cols)
  | direction, .indices values => resolveIndices direction values

private def applyTargets
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (targets : List (Target rows cols)) :
    Except String (Board rows cols × List String) :=
  match solveTargets puzzle board targets with
  | .error target => .error (noCandidateMessage target)
  | .ok result => .ok (result.board, result.solved.map solvedTargetMessage)

/-- Execute runtime `line` groups with the same left-to-right board updates as the tactic. -/
def applyLineGroups
    (puzzle : Puzzle rows cols)
    (initialBoard : Board rows cols)
    (groups : List LineGroup) : Except String (Board rows cols × List String) := do
  let mut board := initialBoard
  let mut messages := []
  for group in groups do
    match group with
    | .axis direction selection =>
        let targets ← axisTargets direction selection
        let (nextBoard, nextMessages) ← applyTargets puzzle board targets
        board := nextBoard
        messages := messages ++ nextMessages
    | .all =>
        let (nextBoard, nextMessages) ← applyTargets puzzle board (allTargets rows cols)
        board := nextBoard
        messages := messages ++ nextMessages
    | .fixedPoint =>
        match solveToFixedPoint puzzle board with
        | .error target => throw (noCandidateMessage target)
        | .ok (nextBoard, passes) =>
            board := nextBoard
            messages := messages ++ [s!"line **: stabilized after {passes} pass(es)"]
  return (board, messages)

/-- One productive single-line deduction. -/
structure Step (rows cols : Nat) where
  target : Target rows cols
  candidateCount : Nat
  board : Board rows cols

/-- Find and apply the first row or column that decides at least one new cell. -/
def step
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) : Except String (Option (Step rows cols)) := do
  for target in allTargets rows cols do
    match solveTarget puzzle board target with
    | none => throw (noCandidateMessage target)
    | some (nextBoard, solved) =>
        unless boardsEqual nextBoard board do
          return some ⟨target, solved.candidateCount, nextBoard⟩
  return none

/-- The trace produced by repeatedly applying one productive line deduction. -/
def solveSteps
    (puzzle : Puzzle rows cols)
    (initialBoard : Board rows cols) : Except String (List (Step rows cols) × Board rows cols) := do
  let mut board := initialBoard
  let mut steps := []
  for _ in List.range (rows * cols + 1) do
    match ← step puzzle board with
    | none => return (steps, board)
    | some next =>
        board := next.board
        steps := steps ++ [next]
  return (steps, board)

private def randomCells : Nat -> Nat -> StdGen -> Array Bool × StdGen
  | 0, _, generator => (#[], generator)
  | count + 1, density, generator =>
      let (value, generator) := randNat generator 0 99
      let (rest, generator) := randomCells count density generator
      (rest.push (value < density), generator)

private def cellsSolution
    (cols : Nat)
    (cells : Array Bool) : Solution rows cols :=
  fun row column => cells.getD (row.val * cols + column.val) false

/-- A generated solution and the clues derived from it. -/
structure Generated (rows cols : Nat) where
  solution : Solution rows cols
  puzzle : Puzzle rows cols

/-- Generate one random solution and derive its puzzle clues. -/
def generate
    (rows cols density seed : Nat) : Generated rows cols :=
  let (cells, _) := randomCells (rows * cols) density (mkStdGen seed)
  let solution := cellsSolution (rows := rows) cols cells
  ⟨solution, solution.toPuzzle⟩

private def clueSource : Clue -> String
  | [] => "[]"
  | [block] => toString block
  | blocks => "[" ++ String.intercalate " " (blocks.map toString) ++ "]"

private def targetSource : Target rows cols -> String
  | .row row => s!"line row {row.val + 1}"
  | .col column => s!"line col {column.val + 1}"

private def axisSource : Axis -> String
  | .row => "row"
  | .col => "col"

private def lineGroupSource : LineGroup -> String
  | .axis direction .all => axisSource direction ++ " *"
  | .axis direction (.indices values) =>
      String.intercalate " " (axisSource direction :: values.map toString)
  | .all => "*"
  | .fixedPoint => "**"

/-- Render a runtime line command in the syntax accepted by `nono`. -/
def lineSource (groups : List LineGroup) : String :=
  String.intercalate " " ("line" :: groups.map lineGroupSource)

/-- Render one successful manual cell edit in tactic syntax. -/
def editSource (value : Cell) (row column : Nat) : String :=
  let command := match value with
    | .filled => "fill"
    | .crossed => "cross"
    | .unknown => "clear"
  s!"{command} {row} {column}"

/-- A stable Lean identifier for one generated puzzle. -/
def exportName (seed : Nat) : String :=
  s!"randomPuzzle_seed{seed}"

private def replayTranscript
    (puzzle : Puzzle rows cols)
    (transcript : List String) : Except String (Board rows cols) := do
  let mut board := Board.unknown
  for source in transcript do
    match ← Command.parse source with
    | .edit value row column => board ← applyEdit board value row column
    | .line groups =>
        let (nextBoard, _) ← applyLineGroups puzzle board groups
        board := nextBoard
    | _ => throw s!"cannot replay non-tactic transcript entry `{source}`"
  return board

/--
Export the current solved board as compilable Lean source. The `nono` proof
replays exactly the successful tactic commands recorded in this CLI session.
-/
def exportLeanSource
    (name : String)
    (generated : Generated rows cols)
    (board : Board rows cols)
    (transcript : List String) : Except String String := do
  checkGram generated.puzzle board
  let replayed ← replayTranscript generated.puzzle transcript
  unless boardsEqual replayed board do
    throw "cannot export: the recorded tactic transcript does not reproduce the current board"
  let rowClues := List.ofFn generated.puzzle.rowClues |>.map clueSource
  let colClues := List.ofFn generated.puzzle.colClues |>.map clueSource
  let tactics := transcript.map fun source => "  " ++ source
  return (
    "import Nonogram\n\n" ++
    "open Nonogram\n\n" ++
    s!"def {name} : Puzzle {rows} {cols} := nonogram from clues\n" ++
    "  rows: " ++ String.intercalate " " rowClues ++ "\n" ++
    "  cols: " ++ String.intercalate " " colClues ++ "\n\n" ++
    s!"theorem {name}_solvable : {name}.Solvable := nono\n" ++
    String.intercalate "\n" (tactics ++ ["  gram"]) ++ "\n")

/-- Command-line configuration. -/
structure Config where
  rows : Nat := 5
  cols : Nat := 5
  density : Nat := 50
  seed : Option Nat := none
  auto : Bool := false
  reveal : Bool := false
  help : Bool := false

namespace Config

private def parseNatOption (name value : String) : Except String Nat :=
  match value.toNat? with
  | some number => .ok number
  | none => .error s!"{name} expects a natural number, got `{value}`"

/-- Parse executable arguments. -/
def parse (args : List String) : Except String Config := do
  let rec go : List String -> Config -> Except String Config
    | [], config => .ok config
    | "--rows" :: value :: rest, config => do
        let rows ← parseNatOption "--rows" value
        go rest { config with rows }
    | "--cols" :: value :: rest, config => do
        let cols ← parseNatOption "--cols" value
        go rest { config with cols }
    | "--density" :: value :: rest, config => do
        let density ← parseNatOption "--density" value
        go rest { config with density }
    | "--seed" :: value :: rest, config => do
        let seed ← parseNatOption "--seed" value
        go rest { config with seed := some seed }
    | "--" :: rest, config => go rest config
    | "--auto" :: rest, config => go rest { config with auto := true }
    | "--reveal" :: rest, config => go rest { config with reveal := true }
    | "--help" :: rest, config => go rest { config with help := true }
    | "-h" :: rest, config => go rest { config with help := true }
    | option :: _, _ => .error s!"unknown or incomplete option `{option}`"
  let config ← go args {}
  if config.help then
    return config
  unless 0 < config.rows && config.rows <= 12 do
    throw "--rows must be in the range 1..12"
  unless 0 < config.cols && config.cols <= 12 do
    throw "--cols must be in the range 1..12"
  unless 0 < config.density && config.density < 100 do
    throw "--density must be in the range 1..99"
  return config

end Config

def usage : String :=
  "Usage: lake exe nonogram -- [options]\n\n" ++
  "Options:\n" ++
  "  --rows N       puzzle rows (default 5, maximum 12)\n" ++
  "  --cols N       puzzle columns (default 5, maximum 12)\n" ++
  "  --density N    black-cell percentage, 1..99 (default 50)\n" ++
  "  --seed N       reproducible random seed\n" ++
  "  --auto         solve one productive line at a time without prompting\n" ++
  "  --reveal       print the generated solution after solving\n" ++
  "  -h, --help     show this help"

def commandHelp : String :=
  "Commands:\n" ++
  "  #new [SEED]               start a new game; default is the next seed\n" ++
  "  #export                   export the solved transcript as Lean source\n" ++
  "  #show / #reveal           print the current board / hidden solution\n" ++
  "  #help / #quit             show this list / exit\n" ++
  "  <enter>, step             apply the next productive row or column\n" ++
  "  fill R C / cross R C      set one cell using 1-based coordinates\n" ++
  "  clear R C                 return one cell to unknown\n" ++
  "  line row 1 2 col 3       solve selected lines from left to right\n" ++
  "  line row * / line col *  solve every line on one axis\n" ++
  "  line * / line **         run one pass / run to a fixed point\n" ++
  "  gram                      check that the completed board satisfies all clues\n" ++
  "  show                      print the current board\n" ++
  "  reveal                    print the generated solution\n" ++
  "  help / quit               aliases for #help / #quit"

private def statusMessage (board : Board rows cols) : String :=
  if isComplete board then
    "Solved."
  else
    s!"{rows * cols - decidedCount board} cell(s) remain unknown."

private def printMessages (messages : List String) : IO Unit :=
  for message in messages do
    IO.println message

private def runAuto
    (generated : Generated rows cols)
    (reveal : Bool) : IO Unit := do
  let initial := Board.unknown
  IO.println (generated.puzzle.renderBoard initial)
  match solveSteps generated.puzzle initial with
  | .error message => IO.eprintln s!"error: {message}"
  | .ok (steps, board) =>
      for h : index in [:steps.length] do
        let current := steps[index]
        IO.println (s!"\nStep {index + 1}: line {targetLabel current.target}: " ++
          s!"{current.candidateCount} candidate(s)")
        IO.println (generated.puzzle.renderBoard current.board)
      IO.println s!"\n{statusMessage board}"
      if reveal then
        IO.println "\nGenerated solution:"
        IO.println (generated.puzzle.renderBoard (solutionBoard generated.solution))

private partial def repl
    (density seed : Nat)
    (generated : Generated rows cols)
    (board : Board rows cols)
    (transcript : List String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr "nono> "
  stdout.flush
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  if input.isEmpty then
    IO.println ""
    return
  match Command.parse input with
  | .error message =>
      IO.eprintln s!"error: {message}"
      repl density seed generated board transcript
  | .ok .quit => pure ()
  | .ok (.newGame requestedSeed) =>
      let nextSeed := requestedSeed.getD (seed + 1)
      let nextGenerated := generate rows cols density nextSeed
      IO.println (s!"New random {rows} x {cols} puzzle " ++
        s!"(seed {nextSeed}, density {density}%)")
      IO.println (nextGenerated.puzzle.renderBoard Board.unknown)
      repl density nextSeed nextGenerated Board.unknown []
  | .ok .exportSource =>
      let name := exportName seed
      match exportLeanSource name generated board transcript with
      | .error message => IO.eprintln s!"error: {message}"
      | .ok source => IO.println source
      repl density seed generated board transcript
  | .ok .help =>
      IO.println commandHelp
      repl density seed generated board transcript
  | .ok .show =>
      IO.println (generated.puzzle.renderBoard board)
      repl density seed generated board transcript
  | .ok .reveal =>
      IO.println (generated.puzzle.renderBoard (solutionBoard generated.solution))
      repl density seed generated board transcript
  | .ok (.edit value row column) =>
      match applyEdit board value row column with
      | .error message =>
          IO.eprintln s!"error: {message}"
          repl density seed generated board transcript
      | .ok nextBoard =>
          IO.println (generated.puzzle.renderBoard nextBoard)
          repl density seed generated nextBoard (transcript ++ [editSource value row column])
  | .ok .gram =>
      match checkGram generated.puzzle board with
      | .error message => IO.eprintln s!"error: {message}"
      | .ok () => IO.println "gram: board is complete and satisfies every clue"
      repl density seed generated board transcript
  | .ok .step =>
      match step generated.puzzle board with
      | .error message =>
          IO.eprintln s!"error: {message}"
          repl density seed generated board transcript
      | .ok none =>
          IO.println (statusMessage board)
          repl density seed generated board transcript
      | .ok (some next) =>
          IO.println s!"line {targetLabel next.target}: {next.candidateCount} candidate(s)"
          IO.println (generated.puzzle.renderBoard next.board)
          repl density seed generated next.board (transcript ++ [targetSource next.target])
  | .ok (.line groups) =>
      match applyLineGroups generated.puzzle board groups with
      | .error message =>
          IO.eprintln s!"error: {message}"
          repl density seed generated board transcript
      | .ok (nextBoard, messages) =>
          printMessages messages
          IO.println (generated.puzzle.renderBoard nextBoard)
          if isComplete nextBoard then IO.println "Solved."
          repl density seed generated nextBoard (transcript ++ [lineSource groups])

/-- Run the random-puzzle CLI. -/
def run (args : List String) : IO UInt32 := do
  let config ← match Config.parse args with
    | .ok config => pure config
    | .error message =>
        IO.eprintln s!"error: {message}\n\n{usage}"
        return 2
  if config.help then
    IO.println usage
    return 0
  let seed ← match config.seed with
    | some seed => pure seed
    | none => IO.rand 0 2147483561
  let generated := generate config.rows config.cols config.density seed
  IO.println (s!"Random {config.rows} x {config.cols} puzzle " ++
    s!"(seed {seed}, density {config.density}%)")
  if config.auto then
    runAuto generated config.reveal
  else
    IO.println (generated.puzzle.renderBoard Board.unknown)
    IO.println "\nPress Enter for one deduction, or type `#help`."
    repl config.density seed generated Board.unknown []
  return 0

end CLI

end Nonogram
