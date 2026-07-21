import Nonogram.WeaveSolver.Spec
import Nonogram.WeaveSolver.Naive
import Nonogram.WeaveSolver.Soundness.Naive

namespace Nonogram

namespace WeaveSolver

/-- Analyze selected cells with the default exhaustive implementation. -/
def solve
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Except Unit (Result rows cols) :=
  Naive.solve puzzle board coordinates

/-- The default weave implementation meets the behavioral specification. -/
theorem solve_exact
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Spec.ExactOutcome puzzle board coordinates (solve puzzle board coordinates) := by
  exact Naive.solve_exact puzzle board coordinates

/-- Every compatible complete puzzle solution survives a successful weave. -/
theorem solve_sound
    {puzzle : Puzzle rows cols}
    {oldBoard : Board rows cols}
    {coordinates : List (Coordinate rows cols)}
    {result : Result rows cols}
    (hSolve : solve puzzle oldBoard coordinates = .ok result)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    result.board.Compatible solution := by
  exact Naive.solve_sound hSolve hSatisfies hCompatible

end WeaveSolver

end Nonogram
