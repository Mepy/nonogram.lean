import Nonogram

open Nonogram

/-- A small cross-shaped 5 x 5 puzzle. -/
def crossPuzzle : Puzzle 5 5 := nonogram {
  rows: [[1], [1], [5], [1], [1]],
  columns: [[1], [1], [5], [1], [1]]
}

def crossSolution : Solution 5 5 :=
  fun r c => r.val == 2 || c.val == 2

def crossBoard : Board 5 5 where
  get r c := if crossSolution r c then .filled else .crossed

def main : IO Unit := do
  IO.println "5 x 5 cross Nonogram"
  IO.println (crossPuzzle.renderBoard crossBoard)
