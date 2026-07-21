import Nonogram

open Nonogram

namespace Nonogram.WeaveSolver.Tests

def ambiguous : Puzzle 2 2 := nonogram from clues
  rows: 1 1
  cols: 1 1

private def topLeft : Coordinate 2 2 :=
  { row := 0, col := 0 }

/-- Repeated coordinates do not create duplicate branches. -/
example :
    (match solve ambiguous Board.unknown [topLeft, topLeft] with
    | .ok result =>
        result.attemptedCount == 2 &&
        result.candidateCount == 2 &&
        !result.resolved &&
        result.board.get 0 0 == .unknown
    | .error _ => false) = true := by
  native_decide

def contradictory : Puzzle 1 1 := nonogram from clues
  rows: 1
  cols: []

/-- Every assignment is rejected when the puzzle itself is contradictory. -/
example :
    (match solve contradictory Board.unknown [{ row := 0, col := 0 }] with
    | .error _ => true
    | .ok _ => false) = true := by
  native_decide

def xPuzzle : Puzzle 3 3 := nonogram from solution
  #.#
  .#.
  #.#

/-- The tactic parser accepts any number of `(row, column)` pairs. -/
example : xPuzzle.Solvable := nono
  weave 1 1 1 2
  gram

end Nonogram.WeaveSolver.Tests
