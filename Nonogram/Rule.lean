import Nonogram.Semantics

namespace Nonogram

/-- A deduction rule may update a board or decline to apply. -/
abbrev Rule (rows cols : Nat) :=
  Puzzle rows cols -> Board rows cols -> Option (Board rows cols)

namespace Rule

/-- A sound rule preserves every solution compatible with the old board. -/
def Sound (rule : Rule rows cols) : Prop :=
  forall puzzle oldBoard newBoard,
    rule puzzle oldBoard = some newBoard ->
    forall solution,
      solution.Satisfies puzzle ->
      oldBoard.Compatible solution ->
      newBoard.Compatible solution

/-- A monotone rule never forgets or changes known information. -/
def Monotone (rule : Rule rows cols) : Prop :=
  forall puzzle oldBoard newBoard,
    rule puzzle oldBoard = some newBoard ->
    newBoard.Refines oldBoard

end Rule

end Nonogram
