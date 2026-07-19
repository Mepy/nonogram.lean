import Nonogram.Semantics

namespace Nonogram

namespace Spec

/-- A complete solution still possible under the puzzle clues and current board. -/
def Candidate
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (solution : Solution rows cols) : Prop :=
  And (solution.Satisfies puzzle) (board.Compatible solution)

/-- The current board admits at least one complete puzzle solution. -/
def Consistent
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) : Prop :=
  exists solution : Solution rows cols, Candidate puzzle board solution

/-- Every globally possible solution fills this cell. -/
def ForcedFilled
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (row : Fin rows)
    (col : Fin cols) : Prop :=
  forall solution, Candidate puzzle board solution -> solution row col = true

/-- Every globally possible solution crosses this cell. -/
def ForcedCrossed
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (row : Fin rows)
    (col : Fin cols) : Prop :=
  forall solution, Candidate puzzle board solution -> solution row col = false

end Spec

end Nonogram
