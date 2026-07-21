import Nonogram.LineSolver.Multi

namespace Nonogram

namespace WeaveSolver

open LineSolver.Multi

/-- One cell selected for case analysis by the weave solver. -/
structure Coordinate (rows cols : Nat) where
  row : Fin rows
  col : Fin cols
  deriving BEq, DecidableEq

/-- The successful result of a weave search. -/
structure Result (rows cols : Nat) where
  board : Board rows cols
  candidateCount : Nat
  attemptedCount : Nat
  resolved : Bool

private def enumerate
    (board : Board rows cols) :
    List (Coordinate rows cols) -> List (Board rows cols)
  | [] => [board]
  | coordinate :: coordinates =>
      match board.get coordinate.row coordinate.col with
      | .unknown =>
          enumerate (board.set coordinate.row coordinate.col .filled) coordinates ++
          enumerate (board.set coordinate.row coordinate.col .crossed) coordinates
      | .filled | .crossed => enumerate board coordinates

/--
Enumerate the selected cells, reject assignments on which the line solver finds
a contradiction, and apply the sole surviving assignment when there is one.
Duplicate coordinates are ignored. An error means every assignment contradicted
at least one row or column.
-/
def solve
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Except Unit (Result rows cols) :=
  let assignments := enumerate board coordinates.eraseDups
  let candidates := assignments.filterMap fun candidate =>
    match solveToFixedPoint puzzle candidate with
    | .error _ => none
    | .ok (solved, _) => some solved
  match candidates with
  | [] => .error ()
  | [candidate] => .ok ⟨candidate, 1, assignments.length, true⟩
  | _ => .ok ⟨board, candidates.length, assignments.length, false⟩

end WeaveSolver

end Nonogram
