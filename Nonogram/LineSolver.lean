import Nonogram.Semantics

namespace Nonogram

namespace LineSolver

/-- The result of intersecting every candidate for one line. -/
structure Result (length : Nat) where
  candidateCount : Nat
  line : Line length Cell

private def assignments : (length : Nat) -> List (List Bool)
  | 0 => [[]]
  | length + 1 =>
      (assignments length).flatMap fun tail =>
        [false :: tail, true :: tail]

private def ofList (cells : List Bool) : Line length Bool :=
  fun i => cells.getD i.val false

private def compatibleCell (known : Cell) (candidate : Bool) : Bool :=
  match known with
  | .unknown => true
  | .filled => candidate
  | .crossed => !candidate

private def compatible (known : Line length Cell) (candidate : Line length Bool) : Bool :=
  (List.ofFn fun i => compatibleCell (known i) (candidate i)).all id

/--
Enumerate every Boolean line that satisfies `clue` and agrees with the cells
already known in `line`.
-/
def candidates (clue : Clue) (line : Line length Cell) : List (Line length Bool) :=
  (assignments length).map ofList |>.filter fun candidate =>
    Line.satisfies clue candidate && compatible line candidate

private def intersect (candidates : List (Line length Bool)) : Line length Cell :=
  fun i =>
    if candidates.all fun candidate => candidate i then
      .filled
    else if candidates.all fun candidate => !candidate i then
      .crossed
    else
      .unknown

/--
Intersect all candidates for a line. A cell is decided exactly when every
candidate gives it the same value. `none` means that no candidate remains.
-/
def solve (clue : Clue) (line : Line length Cell) : Option (Result length) :=
  let candidates := candidates clue line
  if candidates.isEmpty then
    none
  else
    some {
      candidateCount := candidates.length
      line := intersect candidates
    }

end LineSolver

end Nonogram
