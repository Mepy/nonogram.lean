import Nonogram.CLI

open Nonogram
open Nonogram.CLI

example :
    (match Command.parse "" with
    | .ok command => command == .step
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "line row 1 3 col 2 * **" with
    | .ok command => command == .line [
        .axis .row (.indices [1, 3]),
        .axis .col (.indices [2]),
        .all,
        .fixedPoint]
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "line row *" with
    | .ok command => command == .line [.axis .row .all]
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "fill 2 3" with
    | .ok command => command == .edit .filled 2 3
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "gram" with
    | .ok command => command == .gram
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "#new" with
    | .ok command => command == .newGame none
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "#new 1729" with
    | .ok command => command == .newGame (some 1729)
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "#export" with
    | .ok command => command == .exportSource
    | .error _ => false) = true := by
  native_decide

example :
    (match Command.parse "line row 1 trailing" with
    | .ok _ => false
    | .error _ => true) = true := by
  native_decide

example :
    (match Config.parse ["--", "--rows", "4", "--cols", "6", "--seed", "42", "--auto"] with
    | .ok config =>
        config.rows == 4 && config.cols == 6 && config.seed == some 42 && config.auto
    | .error _ => false) = true := by
  native_decide

example :
    (match Config.parse ["--rows", "13"] with
    | .ok _ => false
    | .error _ => true) = true := by
  native_decide

def testSolution : Solution 5 5 :=
  fun row column => row.val == 2 || column.val == 2

def testPuzzle : Puzzle 5 5 := testSolution.toPuzzle

def testGenerated : Generated 5 5 where
  solution := testSolution
  puzzle := testPuzzle

def testTranscript : List String := [
  "line row 3",
  "line col 1",
  "line col 2",
  "line col 3",
  "line row 1",
  "line row 2",
  "line row 4",
  "line row 5"]

def expectedExport : String := include_str "CLI" / "Exported.lean"

example :
    (match exportLeanSource "exportedCross" testGenerated
        (solutionBoard testSolution) testTranscript with
    | .ok source => source == expectedExport
    | .error _ => false) = true := by
  native_decide

example :
    (match exportLeanSource "unfinished" testGenerated Board.unknown [] with
    | .ok _ => false
    | .error _ => true) = true := by
  native_decide

example : exportName 42 = "randomPuzzle_seed42" := by
  native_decide

example :
    (match applyEdit (rows := 5) (cols := 5) Board.unknown .filled 2 3 with
    | .ok board => board.get ⟨1, by decide⟩ ⟨2, by decide⟩ == .filled
    | .error _ => false) = true := by
  native_decide

example :
    (match checkGram testPuzzle (solutionBoard testSolution) with
    | .ok () => true
    | .error _ => false) = true := by
  native_decide

example :
    (match solveSteps testPuzzle Board.unknown with
    | .ok (_, board) => isComplete board && matchesSolution board testSolution
    | .error _ => false) = true := by
  native_decide

example :
    let first := generate 3 3 50 42
    let second := generate 3 3 50 42
    matchesSolution (solutionBoard first.solution) second.solution = true := by
  native_decide
