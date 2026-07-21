import Nonogram.WeaveSolver.Spec

namespace Nonogram

namespace WeaveSolver.Naive

open LineSolver.Multi

/-- Exhaustively branch on every selected unknown cell. -/
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

/-- Exhaustive assumption boards, with duplicate coordinates ignored. -/
def assignmentBoards
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) : List (Board rows cols) :=
  assignmentBoardsRaw board coordinates.eraseDups

/-- Run full-board line propagation on every exhaustive assumption board. -/
def candidates
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) : List (Board rows cols) :=
  (assignmentBoards board coordinates).filterMap fun candidate =>
    match solveToFixedPoint puzzle candidate with
    | .error _ => none
    | .ok (solved, _) => some solved

/--
Exhaustively enumerate all assignments before testing each one with full-board
line propagation.
-/
def solve
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Except Unit (Result rows cols) :=
  let assignments := assignmentBoards board coordinates
  let survivors := candidates puzzle board coordinates
  match survivors with
  | [] => .error ()
  | [candidate] => .ok ⟨candidate, 1, assignments.length, true⟩
  | _ => .ok ⟨board, survivors.length, assignments.length, false⟩

end WeaveSolver.Naive

end Nonogram
