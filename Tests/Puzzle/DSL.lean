import Nonogram.Puzzle.DSL

/-! Tests for literal and programmatic puzzle construction. -/

open Nonogram

def stripePuzzle : Puzzle 3 3 := nonogram {
  rows: [[1], [3], -],
  columns: [[1], [1], [1]]
}

example : List.ofFn stripePuzzle.rowClues = [[1], [3], []] := by
  native_decide

example : List.ofFn stripePuzzle.colClues = [[1], [1], [1]] := by
  native_decide

example :
    (List.ofFn stripePuzzle.rowClues).all (Clue.isWellFormed 3) &&
      (List.ofFn stripePuzzle.colClues).all (Clue.isWellFormed 3) := by
  native_decide

example : Puzzle 2 2 :=
  Puzzle.ofClueLists [[1], []] [[1], []]

/-- error: row clue 1 contains a zero-length block; block lengths must be positive -/
#guard_msgs in
def zeroBlock := nonogram {
  rows: [[0]],
  columns: [[]]
}

/-- error: row clue 1 requires at least 2 cells, but the puzzle has 1 -/
#guard_msgs in
def oversizedRow := nonogram {
  rows: [[2]],
  columns: [[]]
}

/-- error: column clue 1 requires at least 2 cells, but the puzzle has 1 -/
#guard_msgs in
def oversizedColumn := nonogram {
  rows: [[]],
  columns: [[2]]
}
