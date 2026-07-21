import Nonogram.LineSolver.Multi
import Nonogram.WeaveSolver

namespace Nonogram

/-- A sound operation used to justify a `nono` outcome. -/
inductive SolverStep (rows cols : Nat) where
  | targets (targets : List (LineSolver.Multi.Target rows cols))
  | fixedPoint
  | weave (coordinates : List (WeaveSolver.Coordinate rows cols))
  | clear (row : Fin rows) (col : Fin cols)

namespace SolverStep

open LineSolver.Multi


/-- Execute one sound operation without tactic reporting. -/
def apply
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (step : SolverStep rows cols) : Except Unit (Board rows cols) :=
  match step with
  | .targets targetList =>
      (solveTargets puzzle board targetList).mapError (fun _ => ()) |>.map (fun r => r.board)
  | SolverStep.fixedPoint =>
      (solveToFixedPoint puzzle board).mapError (fun _ => ()) |>.map Prod.fst
  | SolverStep.weave coordinates =>
      (WeaveSolver.solve puzzle board coordinates).map (fun r => r.board)
  | SolverStep.clear row col => .ok (board.set row col .unknown)

/-- Execute a sound transcript from left to right. -/
def run
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) :
    List (SolverStep rows cols) -> Except Unit (Board rows cols)
  | [] => .ok board
  | step :: steps => do
      let board ← apply puzzle board step
      run puzzle board steps

end SolverStep

end Nonogram
