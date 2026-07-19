import Nonogram.LineSolver.Single.Internal

namespace Nonogram

namespace LineSolver.Single.Naive

/--
Enumerate every Boolean line that satisfies `clue` and agrees with the cells
already known in `line`.
-/
def candidates
    (clue : Clue)
    (line : Line length Cell) : List (Line length Bool) :=
  (LineSolver.Single.Internal.assignments length).map
      LineSolver.Single.Internal.ofList |>.filter fun candidate =>
    Line.satisfies clue candidate &&
      LineSolver.Single.Internal.compatible line candidate

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
      line := LineSolver.Single.Internal.intersect candidates
    }

end LineSolver.Single.Naive

end Nonogram
