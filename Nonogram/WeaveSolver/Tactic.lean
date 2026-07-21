import Lean
import Nonogram.Tactic.Basic
import Nonogram.WeaveSolver

open Lean Elab Term

namespace Nonogram

declare_syntax_cat nonogramWeaveCoordinate

/-- One 1-based `(row, column)` coordinate passed to `weave`. -/
syntax num num : nonogramWeaveCoordinate

/--
Enumerate assignments to the selected cells and use line-solver contradictions
to discard them. The board is updated when exactly one assignment survives.
-/
syntax (name := nonogramWeaveSolver) "weave" nonogramWeaveCoordinate* : nonogramStep

namespace WeaveSolver.Tactic

private def report (result : Result rows cols) : String :=
  let disposition :=
    if result.resolved then "applied the unique candidate"
    else "board unchanged"
  s!"weave: {result.candidateCount} of {result.attemptedCount} candidate(s) survived; " ++
    disposition

/-- Elaborate and execute one `weave` command. -/
def elabWeave
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinateStxs : Array (TSyntax `nonogramWeaveCoordinate)) :
    TermElabM (Board rows cols × Option String) := do
  let coordinates ← coordinateStxs.mapM fun coordinateStx => do
    match coordinateStx with
    | `(nonogramWeaveCoordinate| $rowStx:num $colStx:num) =>
        let row ← Nonogram.Tactic.getCoordinate "row" rows rowStx
        let col ← Nonogram.Tactic.getCoordinate "column" cols colStx
        pure { row, col }
    | _ => throwUnsupportedSyntax
  match solve puzzle board coordinates.toList with
  | .error _ =>
      throwError "`weave` rejected every candidate; the current board contradicts the clues"
  | .ok result => return (result.board, some (report result))

end WeaveSolver.Tactic

end Nonogram
