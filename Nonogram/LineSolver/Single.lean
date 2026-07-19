import Nonogram.LineSolver.Spec

namespace Nonogram

namespace LineSolver

namespace Internal

/-- Enumerate Boolean lists of a given length. Exposed for verification only. -/
def assignments : (length : Nat) -> List (List Bool)
  | 0 => [[]]
  | length + 1 =>
      (assignments length).map (false :: ·) ++
        (assignments length).map (true :: ·)

/-- Interpret a Boolean list as a finite line. Exposed for verification only. -/
def ofList (cells : List Bool) : Line length Bool :=
  fun i => cells.getD i.val false

/-- Check compatibility at one cell. Exposed for verification only. -/
def compatibleCell (known : Cell) (candidate : Bool) : Bool :=
  match known with
  | .unknown => true
  | .filled => candidate
  | .crossed => !candidate

/-- Check compatibility between a known line and a candidate. -/
def compatible (known : Line length Cell) (candidate : Line length Bool) : Bool :=
  (List.ofFn fun i => compatibleCell (known i) (candidate i)).all id

/-- Intersect a list of Boolean candidates. Exposed for verification only. -/
def intersect (candidates : List (Line length Bool)) : Line length Cell :=
  fun i =>
    if candidates.all fun candidate => candidate i then
      .filled
    else if candidates.all fun candidate => !candidate i then
      .crossed
    else
      .unknown

end Internal

/--
Enumerate every Boolean line that satisfies `clue` and agrees with the cells
already known in `line`.
-/
def candidates (clue : Clue) (line : Line length Cell) : List (Line length Bool) :=
  (Internal.assignments length).map Internal.ofList |>.filter fun candidate =>
    Line.satisfies clue candidate && Internal.compatible line candidate

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
      line := Internal.intersect candidates
    }

end LineSolver

end Nonogram
