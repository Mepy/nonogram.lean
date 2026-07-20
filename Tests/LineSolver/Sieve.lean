import Nonogram.LineSolver.Sieve

open Nonogram
open Nonogram.LineSolver.Sieve

def ambiguousSolution : Solution 2 2 :=
  fun row column => row == column

def ambiguousGenerated : CLI.Generated 2 2 where
  solution := ambiguousSolution
  puzzle := ambiguousSolution.toPuzzle

example : countSolutionsUpTo ambiguousGenerated.puzzle 2 = 2 := by
  native_decide

example :
    (match analyze 7 ambiguousGenerated true with
    | .ok (some result) =>
        result.unknownCount == 4 && result.classification == some .multiple
    | _ => false) = true := by
  native_decide

example :
    puzzleSource ambiguousGenerated.puzzle =
      "nonogram from clues\n  rows: 1 1\n  cols: 1 1" := by
  native_decide

example :
    (match analyze 0 (CLI.generate 5 5 50 0) true with
    | .ok (some result) =>
        result.unknownCount == 8 && result.classification == some .unique
    | _ => false) = true := by
  native_decide
