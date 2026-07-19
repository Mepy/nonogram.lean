import Nonogram.LineSolver.Single.Naive
import Nonogram.LineSolver.Single.Placement

namespace Nonogram
namespace LineSolver

/-- Generate clue-directed candidates compatible with the known line. -/
def candidates (clue : Clue) (line : Line length Cell) : List (Line length Bool) :=
  Single.Placement.candidates clue line

/-- Analyze one line with the default clue-directed implementation. -/
def solve (clue : Clue) (line : Line length Cell) : Option (Result length) :=
  Single.Placement.solve clue line

end LineSolver
end Nonogram
