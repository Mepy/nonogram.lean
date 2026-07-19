import Nonogram

open Nonogram

/-- A small cross-shaped 5 x 5 puzzle. -/
def crossPuzzle : Puzzle 5 5 where
  rowClues i := if i.val = 2 then [5] else [1]
  colClues i := if i.val = 2 then [5] else [1]

def crossSolution : Solution 5 5 :=
  fun r c => r.val == 2 || c.val == 2

def crossBoard : Board 5 5 where
  get r c := if crossSolution r c then .filled else .crossed

def main : IO Unit := do
  IO.println "5 x 5 cross Nonogram"
  IO.println (crossPuzzle.renderBoard crossBoard)
