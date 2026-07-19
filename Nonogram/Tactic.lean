import Lean
import Nonogram.LineSolver.Board

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

open LineSolver.BoardSolver

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

private def lineSolverReport (messages : Array String) : Option String :=
  if messages.isEmpty then none else some (String.intercalate "\n" messages.toList)

private def pushCompactLineReport
    (messages : Array String)
    (direction : String)
    (lines : List (LineSolver.BoardSolver.SolvedTarget rows cols)) : Array String :=
  if lines.isEmpty then
    messages
  else
    let indices := lines.map fun solved => toString (solved.target.index + 1)
    let candidateCounts := lines.map fun solved => toString solved.candidateCount
    messages.push <| s!"line {direction} {String.intercalate ", " indices}: " ++
      s!"{String.intercalate ", " candidateCounts} candidate(s)"

private def noCandidateMessage : Target rows cols -> String
  | .row row =>
      s!"`line row {row.val + 1}` found no candidate; the current row contradicts its clue"
  | .col col =>
      s!"`line col {col.val + 1}` found no candidate; the current column contradicts its clue"

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
                let targets := rows.toList.map Target.row
                match solveTargets puzzle board targets with
                | .error target => throwErrorAt group (noCandidateMessage target)
                | .ok result =>
                    board := result.board
                    messages := pushCompactLineReport messages "row" result.solved
              else if direction.getId == `col then
                let cols ← indexStxs.mapM (getCoordinate "column" goal.cols)
                let targets := cols.toList.map Target.col
                match solveTargets puzzle board targets with
                | .error target => throwErrorAt group (noCandidateMessage target)
                | .ok result =>
                    board := result.board
                    messages := pushCompactLineReport messages "col" result.solved
              else
                throwErrorAt direction "expected `row` or `col` after `line`"
          | `(nonogramStepLine| $direction:ident *) =>
              if direction.getId == `row then
                match solveTargets puzzle board (allRows goal.rows goal.cols) with
                | .error target => throwErrorAt group (noCandidateMessage target)
                | .ok result =>
                    board := result.board
                    messages := pushCompactLineReport messages "row" result.solved
              else if direction.getId == `col then
                match solveTargets puzzle board (allCols goal.rows goal.cols) with
                | .error target => throwErrorAt group (noCandidateMessage target)
                | .ok result =>
                    board := result.board
                    messages := pushCompactLineReport messages "col" result.solved
              else
                throwErrorAt direction "expected `row` or `col` after `line`"
          | `(nonogramStepLine| *) =>
              match solveAll puzzle board with
              | .error target => throwErrorAt group (noCandidateMessage target)
              | .ok result =>
                  board := result.board
                  messages := pushCompactLineReport messages "row"
                    (result.solved.take goal.rows)
                  messages := pushCompactLineReport messages "col"
                    (result.solved.drop goal.rows)
          | `(nonogramStepLine| **) =>
              match solveToFixedPoint puzzle board with
              | .error target => throwErrorAt group (noCandidateMessage target)
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
