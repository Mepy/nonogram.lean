import Nonogram

open Nonogram

/-- A 3 x 3 puzzle whose solution is an X. -/
def xPuzzle : Puzzle 3 3 where
  rowClues i := if i.val = 1 then [1] else [1, 1]
  colClues i := if i.val = 1 then [1] else [1, 1]

example : xPuzzle.Solvable := nono
  fill 1 1
  cross 1 2
  fill 1 3
  cross 2 1
  fill 2 2
  clear 2 2
  fill 2 2
  cross 2 3
  fill 3 1
  cross 3 2
  fill 3 3
  gram
