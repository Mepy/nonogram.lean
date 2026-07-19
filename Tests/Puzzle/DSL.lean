import Nonogram.Puzzle.DSL

/-! Tests for literal and programmatic puzzle construction. -/

open Nonogram

def stripePuzzle : Puzzle 3 3 := nonogram from clues
  rows: 1 3 []
  cols: 1 1 1

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

def emptyClueAliases : Puzzle 3 1 := nonogram from clues
  rows: [] - 0
  cols: 0

example : List.ofFn emptyClueAliases.rowClues = [[], [], []] := by
  native_decide

example : List.ofFn emptyClueAliases.colClues = [[]] := by
  native_decide

def xPuzzleFromClues : Puzzle 3 3 := nonogram from clues
  rows: [1 1] 1 [1 1]
  cols: [1 1] 1 [1 1]

example : List.ofFn xPuzzleFromClues.rowClues = [[1, 1], [1], [1, 1]] := by
  native_decide

example : List.ofFn xPuzzleFromClues.colClues = [[1, 1], [1], [1, 1]] := by
  native_decide

def diagonalSolution : Solution 2 2 :=
  fun row column => row == column

example : List.ofFn diagonalSolution.toPuzzle.rowClues = [[1], [1]] := by
  native_decide

example : List.ofFn diagonalSolution.toPuzzle.colClues = [[1], [1]] := by
  native_decide

example : diagonalSolution.Satisfies diagonalSolution.toPuzzle :=
  diagonalSolution.satisfies_toPuzzle

def asciiPuzzleFromSolution : Puzzle 3 3 := nonogram from solution
  #_#
  _#_
  #_#

example : List.ofFn asciiPuzzleFromSolution.rowClues = [[1, 1], [1], [1, 1]] := by
  native_decide

example : List.ofFn asciiPuzzleFromSolution.colClues = [[1, 1], [1], [1, 1]] := by
  native_decide

def renderedPuzzleFromSolution : Puzzle 3 3 := nonogram from solution
  ■×■
  ×■×
  ■×■

example : List.ofFn renderedPuzzleFromSolution.rowClues = [[1, 1], [1], [1, 1]] := by
  native_decide

example : List.ofFn renderedPuzzleFromSolution.colClues = [[1, 1], [1], [1, 1]] := by
  native_decide

/-- error: row clue 1 contains a zero-length block; block lengths must be positive -/
#guard_msgs in
def zeroBlock := nonogram from clues
  rows: [0]
  cols: []

/-- error: row clue 1 requires at least 2 cells, but the puzzle has 1 -/
#guard_msgs in
def oversizedRow := nonogram from clues
  rows: 2
  cols: []

/-- error: column clue 1 requires at least 2 cells, but the puzzle has 1 -/
#guard_msgs in
def oversizedColumn := nonogram from clues
  rows: []
  cols: [2]

/-- error: solution row 2 has width 2, expected 3 -/
#guard_msgs in
def raggedSolution := nonogram from solution
  ###
  ##
