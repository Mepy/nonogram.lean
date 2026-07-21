import Lean
import Nonogram.LineSolver.Tactic
import Nonogram.WeaveSolver.Tactic

open Lean Elab Term Meta

namespace Nonogram

/-- Separate commands in a `nono` block; line breaks remain valid separators. -/
syntax (name := nonogramSeparator) ";" : nonogramStep

/-- `fill i j` sets `"■"` (`Cell.filled`) at row `i`, column `j`; both are 1-based. -/
syntax (name := nonogramFill) "fill" num num : nonogramStep

/-- `cross i j` sets `"×"` (`Cell.crossed`) at row `i`, column `j`; both are 1-based. -/
syntax (name := nonogramCross) "cross" num num : nonogramStep

/-- `clear i j` sets `" "` (`Cell.unknown`) at row `i`, column `j`; both are 1-based. -/
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

/-- Show the unchanged board on source lines between two consecutive `nono` syntax nodes. -/
private def showBoardBetween
    (goal : Goal)
    (puzzle : Puzzle goal.rows goal.cols)
    (board : Board goal.rows goal.cols)
    (before after : Syntax) : TermElabM Unit := do
  let some beforeTail := before.getTailPos? (canonicalOnly := true) | return
  let some afterPos := after.getPos? (canonicalOnly := true) | return
  let fileMap ← getFileMap
  let beforeLine := fileMap.toPosition beforeTail |>.line
  let afterLine := fileMap.toPosition afterPos |>.line
  for lineNo in [beforeLine + 1:afterLine] do
    let pos := fileMap.lineStart lineNo
    showBoard goal puzzle board (Syntax.ofRange ⟨pos, pos⟩)

private def setMessage (cell : Cell) (row col : Nat) : String :=
  s!"set \"{toString cell}\" at ({row + 1}, {col + 1}) (both 1-based)"

/-- Prevent Lean's term-goal fallback from rendering `⊢ puzzle.Solvable` inside a `nono` block. -/
private def hideDefaultTermGoal (expectedType : Expr) (ref : Syntax) : TermElabM Unit := do
  let placeholder ← mkSorry expectedType (synthetic := true)
  addTermInfo' ref placeholder (expectedType? := expectedType)

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
    (nonoStx : Syntax)
    (expectedType : Expr) : TermElabM Expr := do
  let goal ← getGoal expectedType
  let puzzle ← evalPuzzle goal
  hideDefaultTermGoal expectedType nonoStx
  -- Each edit replaces this functional board; no array-backed board state is maintained.
  let mut board : Board goal.rows goal.cols := Board.unknown
  let mut finished := false
  let mut previousRef := nonoRef
  showBoard goal puzzle board nonoRef
  for step in steps do
    if finished && !step.raw.isOfKind ``nonogramSeparator then
      throwErrorAt step "`gram` must be the final command in a `nono` block"
    showBoardBetween goal puzzle board previousRef step
    unless step.raw.isOfKind ``nonogramSeparator do
      showBoard goal puzzle board step
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
        let (newBoard, report) ← LineSolver.Tactic.elabLine puzzle board groups
        board := newBoard
        showBoard goal puzzle board step report
    | `(nonogramStep| weave $coordinates:nonogramWeaveCoordinate*) =>
        let (newBoard, report) ← WeaveSolver.Tactic.elabWeave puzzle board coordinates
        board := newBoard
        showBoard goal puzzle board step report
    | `(nonogramStep| gram) =>
        let cells := cellsOfBoard board
        let unknownCount : Nat := cells.foldl (fun count cell =>
          if cell == .unknown then count + 1 else count) 0
        unless unknownCount == 0 do
          throwErrorAt step "cannot run `gram`: {unknownCount} cells are still unknown"
        let solution : Solution goal.rows goal.cols := fun r c => board.get r c == .filled
        unless decide (solution.Satisfies puzzle) do
          throwErrorAt step "`gram` failed: the completed board does not satisfy the clues"
        finished := true
    | _ => throwUnsupportedSyntax
    previousRef := step
  unless finished do
    throwError "a `nono` block must end with `gram`"
  let solution ← solutionSyntax goal.cols (cellsOfBoard board)
  let proof ← `(by
    refine ⟨$solution, ?_⟩
    native_decide)
  -- The generated proof is an implementation detail. Hiding its tactic info keeps
  -- Lean's default goal view from obscuring the board state shown by `nono`.
  let result ← withEnableInfoTree false <| elabTermEnsuringType proof expectedType
  return mkSaveInfoAnnotation result

end Tactic

elab_rules : term <= expectedType
  | `(nono%$nonoTk $steps:nonogramStep*) =>
      let nonoStx := Syntax.node .none (Name.mkSimple "nonogramState")
        (#[nonoTk] ++ steps.map fun step => step.raw)
      Tactic.elabNono steps nonoTk nonoStx expectedType

end Nonogram
