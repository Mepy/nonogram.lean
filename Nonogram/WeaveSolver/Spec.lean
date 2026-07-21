import Nonogram.LineSolver.Multi

namespace Nonogram

namespace WeaveSolver

open LineSolver.Multi

/-- One cell selected for case analysis by the weave solver. -/
structure Coordinate (rows cols : Nat) where
  row : Fin rows
  col : Fin cols
  deriving BEq, DecidableEq

/-- The successful observable result of a weave search. -/
structure Result (rows cols : Nat) where
  board : Board rows cols
  candidateCount : Nat
  attemptedCount : Nat
  resolved : Bool

namespace Spec

/--
Reference enumeration of the filled/crossed assumptions represented by a
coordinate sequence. Known cells do not branch.
-/
def assignmentBoardsRaw
    (board : Board rows cols) :
    List (Coordinate rows cols) -> List (Board rows cols)
  | [] => [board]
  | coordinate :: coordinates =>
      match board.get coordinate.row coordinate.col with
      | .unknown =>
          assignmentBoardsRaw
              (board.set coordinate.row coordinate.col .filled) coordinates ++
            assignmentBoardsRaw
              (board.set coordinate.row coordinate.col .crossed) coordinates
      | .filled | .crossed => assignmentBoardsRaw board coordinates

/-- The exact assumption boards denoted by the selected coordinates. -/
def assignmentBoards
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) : List (Board rows cols) :=
  assignmentBoardsRaw board coordinates.eraseDups

/--
The surviving line-propagation candidates. A branch survives exactly when
full-board line propagation reaches a fixed point instead of a contradiction.
-/
def candidates
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) : List (Board rows cols) :=
  (assignmentBoards board coordinates).filterMap fun candidate =>
    match solveToFixedPoint puzzle candidate with
    | .error _ => none
    | .ok (solved, _) => some solved

/-- A successful result exactly summarizes the reference branch search. -/
def ExactResult
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols))
    (result : Result rows cols) : Prop :=
  let assignments := assignmentBoards board coordinates
  let survivors := candidates puzzle board coordinates
  survivors ≠ [] ∧
    result.attemptedCount = assignments.length ∧
    result.candidateCount = survivors.length ∧
    match survivors with
    | [candidate] => result.resolved = true ∧ result.board = candidate
    | _ => result.resolved = false ∧ result.board = board

/--
The complete behavioral specification of a weave solver. An error means every
assignment was rejected. Success reports exact counts, applies the propagated
board of a sole survivor, and otherwise leaves the input board unchanged.
-/
def ExactOutcome
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Except Unit (Result rows cols) -> Prop
  | .error _ => candidates puzzle board coordinates = []
  | .ok result => ExactResult puzzle board coordinates result

end Spec

end WeaveSolver

end Nonogram
