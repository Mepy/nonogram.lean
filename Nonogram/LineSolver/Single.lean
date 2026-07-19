import Nonogram.LineSolver.Single.Naive
import Nonogram.LineSolver.Single.Placement
import Nonogram.LineSolver.Single.Pruned

namespace Nonogram
namespace LineSolver

/-- Generate candidates with compatibility pruning during clue placement. -/
def candidates (clue : Clue) (line : Line length Cell) : List (Line length Bool) :=
  Single.Pruned.candidates clue line

/-- Analyze one line with the default compatibility-pruned implementation. -/
def solve (clue : Clue) (line : Line length Cell) : Option (Result length) :=
  Single.Pruned.solve clue line

end LineSolver
end Nonogram
