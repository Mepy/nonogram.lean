import Nonogram.LineSolver.Spec

namespace Nonogram
namespace LineSolver.Single.Internal

/-- Enumerate Boolean lists of a given length. Retained for the reference solver. -/
def assignments : (length : Nat) -> List (List Bool)
  | 0 => [[]]
  | length + 1 =>
      (assignments length).map (false :: ·) ++
        (assignments length).map (true :: ·)

/-- Interpret a Boolean list as a finite line. -/
def ofList (cells : List Bool) : Line length Bool :=
  fun i => cells.getD i.val false

/-- Check compatibility at one cell. -/
def compatibleCell (known : Cell) (candidate : Bool) : Bool :=
  match known with
  | .unknown => true
  | .filled => candidate
  | .crossed => !candidate

/-- Check compatibility between a known line and a candidate. -/
def compatible (known : Line length Cell) (candidate : Line length Bool) : Bool :=
  (List.ofFn fun i => compatibleCell (known i) (candidate i)).all id

/-- Intersect a list of Boolean candidates cell by cell. -/
def intersect (candidates : List (Line length Bool)) : Line length Cell :=
  fun i =>
    if candidates.all fun candidate => candidate i then
      .filled
    else if candidates.all fun candidate => !candidate i then
      .crossed
    else
      .unknown

end LineSolver.Single.Internal
end Nonogram
