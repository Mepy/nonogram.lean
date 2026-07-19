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

example : xPuzzle.Solvable := nono
  line
  line row
  line col
  line *
  gram

example : xPuzzle.Solvable := nono
  line row *
  line col *
  gram

example : xPuzzle.Solvable := nono
  line **
  gram

example : xPuzzle.Solvable := nono
  line row 1 * row 2
  gram

example : xPuzzle.Solvable := nono line row 1 3 line col 2 row 2 gram

/-- Row 3 initially has the three candidates `■■■××`, `×■■■×`, and `××■■■`. -/
def overlapPuzzle : Puzzle 3 5 where
  rowClues i := if i.val = 2 then [3] else []
  colClues i := if i.val = 0 || i.val = 4 then [] else [1]

private def blankFive : Line 5 Cell := fun _ => .unknown

example : (LineSolver.solve [3] blankFive).map (·.candidateCount) = some 3 := by
  native_decide

example :
    (LineSolver.solve [3] blankFive).map (fun result => result.line.toList) =
      some [.unknown, .unknown, .filled, .unknown, .unknown] := by
  native_decide

example : overlapPuzzle.Solvable := nono
  line row 3 1 2
  line col 1 2 3 4 5
  gram
