import Lean
import Nonogram.Semantics

open Lean Elab Term Meta

namespace Nonogram

declare_syntax_cat nonogramStep

/-- Mark the cell at the given 1-based row and column as filled. -/
syntax (name := nonogramFill) "fill" num num : nonogramStep

/-- Mark the cell at the given 1-based row and column as crossed. -/
syntax (name := nonogramCross) "cross" num num : nonogramStep

/-- Return the cell at the given 1-based row and column to unknown. -/
syntax (name := nonogramClear) "clear" num num : nonogramStep

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
          margin: 0,
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
    (ref : Syntax) : TermElabM Unit := do
  let props := Json.mkObj [("board", toJson (puzzle.renderBoard board))]
  Widget.savePanelWidgetInfo boardWidget.javascriptHash (pure props) ref

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
    if finished then
      throwErrorAt step "`gram` must be the final command in a `nono` block"
    match step with
    | `(nonogramStep| fill $rowStx:num $colStx:num) =>
        let row ← getCoordinate "row" goal.rows rowStx
        let col ← getCoordinate "column" goal.cols colStx
        board := board.set row col .filled
        showBoard goal puzzle board step
    | `(nonogramStep| cross $rowStx:num $colStx:num) =>
        let row ← getCoordinate "row" goal.rows rowStx
        let col ← getCoordinate "column" goal.cols colStx
        board := board.set row col .crossed
        showBoard goal puzzle board step
    | `(nonogramStep| clear $rowStx:num $colStx:num) =>
        let row ← getCoordinate "row" goal.rows rowStx
        let col ← getCoordinate "column" goal.cols colStx
        board := board.set row col .unknown
        showBoard goal puzzle board step
    | `(nonogramStep| gram) =>
        let cells := cellsOfBoard board
        let unknownCount : Nat := cells.foldl (fun count cell =>
          if cell == .unknown then count + 1 else count) 0
        unless unknownCount == 0 do
          showBoard goal puzzle board step
          throwErrorAt step "cannot run `gram`: {unknownCount} cells are still unknown"
        showBoard goal puzzle board step
        let solution : Solution goal.rows goal.cols := fun r c => board.get r c == .filled
        unless decide (solution.Satisfies puzzle) do
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
