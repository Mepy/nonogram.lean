import Nonogram

open Nonogram

def randomPuzzle_seed734130137 : Puzzle 5 5 := nonogram from clues
  rows: 4 4 4 3 1
  cols: [1 1] 4 4 [3 1] [1 1]

example : randomPuzzle_seed734130137.Solvable :=
  nono
  line row 1 2 3
  line col 2 3 4
  line row 4 5

  line col 5
  line row 1 2 3
  gram
