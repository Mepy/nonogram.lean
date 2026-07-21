import Nonogram

open Nonogram

def exportedCross : Puzzle 5 5 := nonogram from clues
  rows: 1 1 5 1 1
  cols: 1 1 5 1 1

theorem exportedCross_solvable : exportedCross.Outcome := nono
  line row 3
  line col 1
  line col 2
  line col 3
  line row 1
  line row 2
  line row 4
  line row 5
  gram
