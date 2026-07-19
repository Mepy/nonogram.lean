import Lean
import Nonogram.LineSolver

open Lean Elab Term Meta

namespace Nonogram

declare_syntax_cat nonogramStep
declare_syntax_cat nonogramStepLine

/-- One row or column group in a combined `line` command. -/
syntax ident num* : nonogramStepLine

/-- Select every row or column in one group of a combined `line` command. -/
syntax ident "*" : nonogramStepLine

/-- Process every row followed by every column once. -/
syntax "*" : nonogramStepLine

/-- Repeat `*` until a complete pass leaves the board unchanged. -/
syntax "**" : nonogramStepLine

/-- Separate commands in a `nono` block; line breaks remain valid separators. -/
syntax (name := nonogramSeparator) ";" : nonogramStep

/-- `fill i j` sets `"■"` (`Cell.filled`) at row `i`, column `j`; both are 1-based. -/
syntax (name := nonogramFill) "fill" num num : nonogramStep

/-- `cross i j` sets `"×"` (`Cell.crossed`) at row `i`, column `j`; both are 1-based. -/
syntax (name := nonogramCross) "cross" num num : nonogramStep

/-- `clear i j` sets `" "` (`Cell.unknown`) at row `i`, column `j`; both are 1-based. -/
syntax (name := nonogramClear) "clear" num num : nonogramStep

/--
Process a sequence of row and column groups from left to right. For example,
`line row 1 2 col 3 row 4` lets each group use the board updated by the groups
before it. A group with no indices is a no-op. Directions are identifiers to
avoid reserving `row` and `col` as global Lean keywords.
-/
syntax (name := nonogramLineSolver) "line" nonogramStepLine* : nonogramStep

/-- Check the completed board against every clue and finish the proof. -/
syntax (name := nonogramGram) "gram" : nonogramStep

/-- Start an interactive Nonogram proof. -/
syntax (name := nono) "nono" ppLine nonogramStep* : term

namespace Tactic

@[widget_module]
private def boardWidget : Widget.Module where
  javascript := "
    import * as React from 'react';

    export default function NonogramBoard(props) {
      return React.createElement('pre', {
        style: {
          margin: '0 0 1.4em 0',
          overflowX: 'auto',
          lineHeight: 1.4,
          fontFamily: 'var(--vscode-editor-font-family, monospace)',
          fontSize: 'var(--vscode-editor-font-size)'
        }
      }, props.board);
    }
  "

/--
The concrete puzzle recovered from a goal of the form `puzzle.Solvable`.
Its value already contains every row and column clue; `nono` takes no puzzle argument.
-/
private structure Goal where
  rows : Nat
  cols : Nat
  puzzleExpr : Expr

private def getGoal (expectedType : Expr) : TermElabM Goal := do
  let expectedType ← instantiateMVars expectedType
  let fn := expectedType.getAppFn
  let args := expectedType.getAppArgs
  unless fn.isConstOf ``Puzzle.Solvable && args.size == 3 do
    throwError "`nono` can only prove a goal of the form `puzzle.Solvable`"
  let some rows ← getNatValue? args[0]!
    | throwError "`nono` needs a concrete number of rows"
  let some cols ← getNatValue? args[1]!
    | throwError "`nono` needs a concrete number of columns"
  return ⟨rows, cols, args[2]!⟩

private def getCoordinate (label : String) (bound : Nat) (stx : TSyntax `num) : TermElabM (Fin bound) := do
  let value := stx.getNat
  if value == 0 then
    throwErrorAt stx "Nonogram coordinates are 1-based; expected a positive number"
  let index := value - 1
  if h : index < bound then
    return ⟨index, h⟩
  else
    throwErrorAt stx "{label} {value} is outside the range 1..{bound}"

private unsafe def evalPuzzleUnsafe (goal : Goal) : TermElabM (Puzzle goal.rows goal.cols) := do
  let puzzleType ← inferType goal.puzzleExpr
  Meta.evalExpr (Puzzle goal.rows goal.cols) puzzleType goal.puzzleExpr

@[implemented_by evalPuzzleUnsafe]
private opaque evalPuzzle (goal : Goal) : TermElabM (Puzzle goal.rows goal.cols)

private def showBoard
    (goal : Goal)
    (puzzle : Puzzle goal.rows goal.cols)
    (board : Board goal.rows goal.cols)
    (ref : Syntax)
    (message? : Option String := none) : TermElabM Unit := do
  let boardText := puzzle.renderBoard board
  let text := message?.map (· ++ "\n\n" ++ boardText) |>.getD boardText
  let props := Json.mkObj [("board", toJson text)]
  Widget.savePanelWidgetInfo boardWidget.javascriptHash (pure props) ref

private def setMessage (cell : Cell) (row col : Nat) : String :=
  s!"set \"{toString cell}\" at ({row + 1}, {col + 1}) (both 1-based)"

private structure SolvedLine where
  index : Nat
  candidateCount : Nat

private def lineSolverReport (messages : Array String) : Option String :=
  if messages.isEmpty then none else some (String.intercalate "\n" messages.toList)

private def pushCompactLineReport
    (messages : Array String)
    (direction : String)
    (lines : Array SolvedLine) : Array String :=
  if lines.isEmpty then
    messages
  else
    let indices := lines.map fun solved => toString (solved.index + 1)
    let candidateCounts := lines.map fun solved => toString solved.candidateCount
    messages.push <| s!"line {direction} {String.intercalate ", " indices.toList}: " ++
      s!"{String.intercalate ", " candidateCounts.toList} candidate(s)"

private def allIndices (length : Nat) : Array (Fin length) :=
  (List.ofFn fun i : Fin length => i).toArray

private def solveRows
    (puzzle : Puzzle rows cols)
    (initialBoard : Board rows cols)
    (indices : Array (Fin rows)) :
    Except (Fin rows) (Board rows cols × Array SolvedLine) := do
  let mut board := initialBoard
  let mut lines := #[]
  for row in indices do
    let some result := LineSolver.solve (puzzle.rowClues row) (board.row row)
      | throw row
    board := board.replaceRow row result.line
    lines := lines.push ⟨row.val, result.candidateCount⟩
  return (board, lines)

private def solveCols
    (puzzle : Puzzle rows cols)
    (initialBoard : Board rows cols)
    (indices : Array (Fin cols)) :
    Except (Fin cols) (Board rows cols × Array SolvedLine) := do
  let mut board := initialBoard
  let mut lines := #[]
  for col in indices do
    let some result := LineSolver.solve (puzzle.colClues col) (board.col col)
      | throw col
    board := board.replaceCol col result.line
    lines := lines.push ⟨col.val, result.candidateCount⟩
  return (board, lines)

private inductive LineSolverError (rows cols : Nat) where
  | row (index : Fin rows)
  | col (index : Fin cols)

private structure SolvedAllLines (rows cols : Nat) where
  board : Board rows cols
  rows : Array SolvedLine
  cols : Array SolvedLine

private def solveAllLines
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) :
    Except (LineSolverError rows cols) (SolvedAllLines rows cols) :=
  match solveRows puzzle board (allIndices rows) with
  | .error row => .error (.row row)
  | .ok (rowBoard, rowLines) =>
      match solveCols puzzle rowBoard (allIndices cols) with
      | .error col => .error (.col col)
      | .ok (newBoard, colLines) => .ok {
          board := newBoard
          rows := rowLines
          cols := colLines
        }

private def boardsEqual (left right : Board rows cols) : Bool :=
  (List.ofFn fun row =>
    (List.ofFn fun col => left.get row col == right.get row col).all id).all id

private def solveToFixedPoint
    (puzzle : Puzzle rows cols)
    (initialBoard : Board rows cols) :
    Except (LineSolverError rows cols) (Board rows cols × Nat) :=
  loop (rows * cols + 1) initialBoard 0
where
  loop : Nat -> Board rows cols -> Nat ->
      Except (LineSolverError rows cols) (Board rows cols × Nat)
    | 0, board, passes => .ok (board, passes)
    | fuel + 1, board, passes =>
        match solveAllLines puzzle board with
        | .error error => .error error
        | .ok result =>
            if boardsEqual result.board board then
              .ok (result.board, passes + 1)
            else
              loop fuel result.board (passes + 1)

/--
Enumerate the functional `Board` in row-major order solely to quote the final solution.
The elaborator itself keeps `Board rows cols` as its only mutable puzzle state.
-/
private def cellsOfBoard (board : Board rows cols) : List Cell :=
  (List.ofFn fun r => List.ofFn fun c => board.get r c).flatten

/-- Quote a complete board as the `Fin rows -> Fin cols -> Bool` solution function. -/
private def solutionSyntax (cols : Nat) (cells : List Cell) : TermElabM (TSyntax `term) := do
  let values ← cells.toArray.mapM fun
    | .filled => `(true)
    | .crossed => `(false)
    | .unknown => throwError "internal error: incomplete board passed to `gram`"
  let colsStx : TSyntax `term := ⟨Syntax.mkNatLit cols⟩
  `(fun r c => [$values,*].getD (r.val * $colsStx + c.val) false)

private def elabNono
    (steps : Array (TSyntax `nonogramStep))
    (nonoRef : Syntax)
    (expectedType : Expr) : TermElabM Expr := do
  let goal ← getGoal expectedType
  let puzzle ← evalPuzzle goal
  -- Each edit replaces this functional board; no array-backed board state is maintained.
  let mut board : Board goal.rows goal.cols := Board.unknown
  let mut finished := false
  showBoard goal puzzle board nonoRef
  for step in steps do
    if finished && !step.raw.isOfKind ``nonogramSeparator then
      throwErrorAt step "`gram` must be the final command in a `nono` block"
    match step with
    | `(nonogramStep| ;) => pure ()
    | `(nonogramStep| fill $rowStx:num $colStx:num) =>
        let r ← getCoordinate "row" goal.rows rowStx
        let c ← getCoordinate "column" goal.cols colStx
        board := board.set r c .filled
        showBoard goal puzzle board step (some (setMessage .filled r.val c.val))
    | `(nonogramStep| cross $rowStx:num $colStx:num) =>
        let r ← getCoordinate "row" goal.rows rowStx
        let c ← getCoordinate "column" goal.cols colStx
        board := board.set r c .crossed
        showBoard goal puzzle board step (some (setMessage .crossed r.val c.val))
    | `(nonogramStep| clear $rowStx:num $colStx:num) =>
        let r ← getCoordinate "row" goal.rows rowStx
        let c ← getCoordinate "column" goal.cols colStx
        board := board.set r c .unknown
        showBoard goal puzzle board step (some (setMessage .unknown r.val c.val))
    | `(nonogramStep| line $groups:nonogramStepLine*) =>
        let mut messages := #[]
        for group in groups do
          match group with
          | `(nonogramStepLine| $direction:ident $indexStxs:num*) =>
              if direction.getId == `row then
                let rows ← indexStxs.mapM (getCoordinate "row" goal.rows)
                match solveRows puzzle board rows with
                | .error row => throwErrorAt group
                      "`line row {row.val + 1}` found no candidate; the current row contradicts its clue"
                | .ok (newBoard, lines) =>
                    board := newBoard
                    messages := pushCompactLineReport messages "row" lines
              else if direction.getId == `col then
                let cols ← indexStxs.mapM (getCoordinate "column" goal.cols)
                match solveCols puzzle board cols with
                | .error col => throwErrorAt group
                      "`line col {col.val + 1}` found no candidate; the current column contradicts its clue"
                | .ok (newBoard, lines) =>
                    board := newBoard
                    messages := pushCompactLineReport messages "col" lines
              else
                throwErrorAt direction "expected `row` or `col` after `line`"
          | `(nonogramStepLine| $direction:ident *) =>
              if direction.getId == `row then
                match solveRows puzzle board (allIndices goal.rows) with
                | .error row => throwErrorAt group
                      "`line row {row.val + 1}` found no candidate; the current row contradicts its clue"
                | .ok (newBoard, lines) =>
                    board := newBoard
                    messages := pushCompactLineReport messages "row" lines
              else if direction.getId == `col then
                match solveCols puzzle board (allIndices goal.cols) with
                | .error col => throwErrorAt group
                      "`line col {col.val + 1}` found no candidate; the current column contradicts its clue"
                | .ok (newBoard, lines) =>
                    board := newBoard
                    messages := pushCompactLineReport messages "col" lines
              else
                throwErrorAt direction "expected `row` or `col` after `line`"
          | `(nonogramStepLine| *) =>
              match solveAllLines puzzle board with
              | .error (.row row) => throwErrorAt group
                    "`line row {row.val + 1}` found no candidate; the current row contradicts its clue"
              | .error (.col col) => throwErrorAt group
                    "`line col {col.val + 1}` found no candidate; the current column contradicts its clue"
              | .ok result =>
                  board := result.board
                  messages := pushCompactLineReport messages "row" result.rows
                  messages := pushCompactLineReport messages "col" result.cols
          | `(nonogramStepLine| **) =>
              match solveToFixedPoint puzzle board with
              | .error (.row row) => throwErrorAt group
                    "`line row {row.val + 1}` found no candidate; the current row contradicts its clue"
              | .error (.col col) => throwErrorAt group
                    "`line col {col.val + 1}` found no candidate; the current column contradicts its clue"
              | .ok (newBoard, passes) =>
                  board := newBoard
                  messages := messages.push s!"line **: stabilized after {passes} pass(es)"
          | _ => throwUnsupportedSyntax
        showBoard goal puzzle board step (lineSolverReport messages)
    | `(nonogramStep| gram) =>
        let cells := cellsOfBoard board
        let unknownCount : Nat := cells.foldl (fun count cell =>
          if cell == .unknown then count + 1 else count) 0
        unless unknownCount == 0 do
          showBoard goal puzzle board step
          throwErrorAt step "cannot run `gram`: {unknownCount} cells are still unknown"
        let solution : Solution goal.rows goal.cols := fun r c => board.get r c == .filled
        unless decide (solution.Satisfies puzzle) do
          showBoard goal puzzle board step
          throwErrorAt step "`gram` failed: the completed board does not satisfy the clues"
        finished := true
    | _ => throwUnsupportedSyntax
  unless finished do
    throwError "a `nono` block must end with `gram`"
  let solution ← solutionSyntax goal.cols (cellsOfBoard board)
  let proof ← `(by
    refine ⟨$solution, ?_⟩
    native_decide)
  let result ← elabTermEnsuringType proof expectedType
  return mkSaveInfoAnnotation result

end Tactic

elab_rules : term <= expectedType
  | `(nono%$nonoTk $steps:nonogramStep*) => Tactic.elabNono steps nonoTk expectedType

end Nonogram
