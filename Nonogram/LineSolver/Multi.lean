import Nonogram.LineSolver.Single

namespace Nonogram

namespace LineSolver.Multi

/-- One row or column selected for line solving. -/
inductive Target (rows cols : Nat) where
  | row (index : Fin rows)
  | col (index : Fin cols)

namespace Target

/-- The zero-based row or column index of a target. -/
def index : Target rows cols -> Nat
  | .row index | .col index => index.val

end Target

/-- A successfully solved target and its number of remaining candidates. -/
structure SolvedTarget (rows cols : Nat) where
  target : Target rows cols
  candidateCount : Nat

/-- The result of solving a sequence of row and column targets. -/
structure Result (rows cols : Nat) where
  board : Board rows cols
  solved : List (SolvedTarget rows cols)

/-- Solve one selected row or column and replace it in the board. -/
def solveTarget
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (target : Target rows cols) :
    Option (Board rows cols × SolvedTarget rows cols) :=
  match target with
  | .row row =>
      match LineSolver.solve (puzzle.rowClues row) (board.row row) with
      | none => none
      | some result => some (
          board.replaceRow row result.line,
          ⟨target, result.candidateCount⟩)
  | .col col =>
      match LineSolver.solve (puzzle.colClues col) (board.col col) with
      | none => none
      | some result => some (
          board.replaceCol col result.line,
          ⟨target, result.candidateCount⟩)

/--
Solve targets from left to right. An error identifies the first target whose
current line has no candidate.
-/
def solveTargets
    (puzzle : Puzzle rows cols) :
    Board rows cols -> List (Target rows cols) ->
      Except (Target rows cols) (Result rows cols)
  | board, [] => .ok ⟨board, []⟩
  | board, target :: targets =>
      match solveTarget puzzle board target with
      | none => .error target
      | some (nextBoard, solvedTarget) =>
          match solveTargets puzzle nextBoard targets with
          | .error failed => .error failed
          | .ok result => .ok ⟨result.board, solvedTarget :: result.solved⟩

/-- Every row target in increasing order. -/
def allRows (rows cols : Nat) : List (Target rows cols) :=
  List.ofFn fun row : Fin rows => Target.row row

/-- Every column target in increasing order. -/
def allCols (rows cols : Nat) : List (Target rows cols) :=
  List.ofFn fun col : Fin cols => Target.col col

/-- Every row followed by every column. -/
def allTargets (rows cols : Nat) : List (Target rows cols) :=
  allRows rows cols ++ allCols rows cols

/-- Solve every row and then every column once. -/
def solveAll
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) :
    Except (Target rows cols) (Result rows cols) :=
  solveTargets puzzle board (allTargets rows cols)

/-- Decidable extensional equality for functional boards. -/
def boardsEqual (left right : Board rows cols) : Bool :=
  (List.ofFn fun row =>
    (List.ofFn fun col => left.get row col == right.get row col).all id).all id

/-- Repeat full passes up to `fuel`, stopping early at a fixed point. -/
def solveToFixedPointWithFuel
    (puzzle : Puzzle rows cols) :
    Nat -> Board rows cols -> Nat ->
      Except (Target rows cols) (Board rows cols × Nat)
  | 0, board, passes => .ok (board, passes)
  | fuel + 1, board, passes =>
      match solveAll puzzle board with
      | .error target => .error target
      | .ok result =>
          if boardsEqual result.board board then
            .ok (result.board, passes + 1)
          else
            solveToFixedPointWithFuel puzzle fuel result.board (passes + 1)

/-- Repeat full passes until stable, with enough fuel for every cell decision. -/
def solveToFixedPoint
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) :
    Except (Target rows cols) (Board rows cols × Nat) :=
  solveToFixedPointWithFuel puzzle (rows * cols + 1) board 0

end LineSolver.Multi

end Nonogram
