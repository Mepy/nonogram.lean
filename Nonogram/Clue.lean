import Nonogram.Basic

namespace Nonogram

/-- The lengths of the black runs in one line, from left to right. -/
abbrev Clue := List Nat

namespace Clue

/-- The least line length needed by a clue, including separators. -/
def requiredLength : Clue -> Nat
  | [] => 0
  | first :: rest =>
      first + rest.foldl (fun total block => total + 1 + block) 0

/-- A clue contains only positive runs and fits in a line of this length. -/
def WellFormed (lineLength : Nat) (clue : Clue) : Prop :=
  And
    (forall block, List.Mem block clue -> 0 < block)
    (requiredLength clue <= lineLength)

/-- Executable counterpart of `WellFormed`. -/
def isWellFormed (lineLength : Nat) (clue : Clue) : Bool :=
  clue.all (fun block => decide (0 < block)) &&
    decide (requiredLength clue <= lineLength)

/-- Render a clue as space-separated run lengths; an empty clue is left blank. -/
def render (clue : Clue) : String :=
  if clue.isEmpty then
    ""
  else
    String.intercalate " " (clue.map toString)

end Clue

namespace Line

private def blackRunsAux : List Bool -> Nat -> List Nat -> List Nat
  | [], current, completed =>
      let completed := if current = 0 then completed else current :: completed
      completed.reverse
  | true :: rest, current, completed =>
      blackRunsAux rest (current + 1) completed
  | false :: rest, current, completed =>
      if current = 0 then
        blackRunsAux rest 0 completed
      else
        blackRunsAux rest 0 (current :: completed)

/-- Compute the lengths of all maximal black runs in a Boolean list. -/
def blackRuns (cells : List Bool) : List Nat :=
  blackRunsAux cells 0 []

/-- Compute the black runs of a finite line. -/
def runs (line : Line length Bool) : List Nat :=
  blackRuns line.toList

/-- A Boolean line satisfies a clue when its black runs equal the clue. -/
def Satisfies (clue : Clue) (line : Line length Bool) : Prop :=
  line.runs = clue

/-- Executable counterpart of `Satisfies`. -/
def satisfies (clue : Clue) (line : Line length Bool) : Bool :=
  line.runs == clue

end Line

end Nonogram
