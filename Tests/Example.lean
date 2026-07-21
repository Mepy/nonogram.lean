import Nonogram

open Nonogram

/-- A 3 x 3 puzzle whose solution is an X. -/
def xPuzzle : Puzzle 3 3 where
  rowClues i := if i.val = 1 then [1] else [1, 1]
  colClues i := if i.val = 1 then [1] else [1, 1]

example : xPuzzle.Outcome := nono
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

example : xPuzzle.Outcome := nono
  line
  line row
  line col
  line *
  gram

example : xPuzzle.Outcome := nono
  line row *
  line col *
  gram

example : xPuzzle.Outcome := nono
  line **
  gram

example : xPuzzle.Outcome := nono
  line row 1 * row 2
  gram

example : xPuzzle.Outcome := nono line row 1 3 line col 2 row 2 gram

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

example : overlapPuzzle.Outcome := nono
  line row 3 1 2
  line col 1 2 3 4 5
  gram


def bear : Puzzle 30 30 := nonogram from clues
  rows: [3 3] [5 7 5] [2 12 2] [2 12 2] 18 17 18 [4 6 6] [4 6 6] [3 1 2 5] [5 3 7] [4 3 6] [4 1 1 1 5] [3 5 5] [3 7] [2 2 5] [10 6] [4 6] [4 7] [4 6] [4 7] [7 3 3 2] [9 6 2 2] [2 9 6 3 3] [1 7 14] [1 7 13] [2 8 10] [11 10] [6 13] 10
  cols: 4 [2 2] [2 2] [3 3] 8 [3 6 10] [5 8 11] [2 11 12] [2 5 5 12] [6 1 5 6] [5 1 1 3 6] [7 1 1 2 3] [8 2 1 1 2 2] [8 4 1 2 2] [8 2 1 1 3 3] [8 1 1 8] [9 1 1 8] [6 1 2 7] [6 1 2 7] [7 5 7] [14 6] [2 13 5] [2 15 6] 28 [3 5 13] [7 2] [5 2] [4 3] 7 4

example : bear.Outcome :=
  nono
  line col 6 7 8 9 17 21 22 23 24 25
  line row *
  line **
  fill 14 12 fill 14 16
  line **
  gram


def amb2 : Puzzle 2 2 := nonogram from solution
  ×■
  ■×

example : amb2.Outcome :=
  nono
  fill 1 1
  line **
  gram

def amb3_Sub : Puzzle 3 3 := nonogram from solution
  ×××
  ×■×
  ××■

example : amb3_Sub.Outcome :=
  nono
  line **
  fill 2 2
  line **
  gram

def amb3_Ann : Puzzle 3 3 := nonogram from clues
  rows: 1 1 1
  cols: 1 1 1

def uniqueButLineStalled : Puzzle 5 5 := nonogram from solution
  ■■××■
  ××■×■
  ××■×■
  ××■××
  ■■×××

example : uniqueButLineStalled.Outcome :=
  nono
  line **

  weave 5 1
  gram
