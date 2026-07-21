import Nonogram.WeaveSolver.Naive
import Nonogram.LineSolver.Soundness.Multi

namespace Nonogram

namespace WeaveSolver.Naive

private theorem assignmentBoardsRaw_eq_spec
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    assignmentBoardsRaw board coordinates =
      Spec.assignmentBoardsRaw board coordinates := by
  induction coordinates generalizing board with
  | nil => rfl
  | cons coordinate coordinates ih =>
      cases hCell : board.get coordinate.row coordinate.col <;>
        simp [assignmentBoardsRaw, Spec.assignmentBoardsRaw, hCell, ih]

/-- The naive branch generator agrees with the reference assignment semantics. -/
theorem assignmentBoards_eq_spec
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    assignmentBoards board coordinates = Spec.assignmentBoards board coordinates := by
  exact assignmentBoardsRaw_eq_spec board coordinates.eraseDups

/-- The naive survivor list agrees with the reference propagation semantics. -/
theorem candidates_eq_spec
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    candidates puzzle board coordinates = Spec.candidates puzzle board coordinates := by
  rw [candidates, Spec.candidates, assignmentBoards_eq_spec]

/-- The exhaustive weave implementation meets the behavioral specification. -/
theorem solve_exact
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Spec.ExactOutcome puzzle board coordinates (solve puzzle board coordinates) := by
  simp only [solve]
  rw [assignmentBoards_eq_spec, candidates_eq_spec]
  cases hCandidates : Spec.candidates puzzle board coordinates with
  | nil => simp [Spec.ExactOutcome, hCandidates]
  | cons candidate rest =>
      cases rest with
      | nil => simp [Spec.ExactOutcome, Spec.ExactResult, hCandidates]
      | cons next tail => simp [Spec.ExactOutcome, Spec.ExactResult, hCandidates]

private def solutionCell (value : Bool) : Cell :=
  if value then .filled else .crossed

private def solutionAssignment
    (solution : Solution rows cols) :
    Board rows cols -> List (Coordinate rows cols) -> Board rows cols
  | board, [] => board
  | board, coordinate :: coordinates =>
      match board.get coordinate.row coordinate.col with
      | .unknown =>
          solutionAssignment solution
            (board.set coordinate.row coordinate.col
              (solutionCell (solution coordinate.row coordinate.col)))
            coordinates
      | .filled | .crossed => solutionAssignment solution board coordinates

private theorem set_solutionCell_compatible
    {board : Board rows cols}
    {solution : Solution rows cols}
    (hCompatible : board.Compatible solution)
    (row : Fin rows)
    (col : Fin cols) :
    (board.set row col (solutionCell (solution row col))).Compatible solution where
  cell currentRow currentCol := by
    simp only [Board.set]
    split
    next hTarget =>
      rcases hTarget with ⟨rfl, rfl⟩
      cases hValue : solution currentRow currentCol <;>
        simp [solutionCell, Cell.Compatible]
    next _ => exact hCompatible.cell currentRow currentCol

private theorem solutionAssignment_compatible
    (solution : Solution rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols))
    (hCompatible : board.Compatible solution) :
    (solutionAssignment solution board coordinates).Compatible solution := by
  induction coordinates generalizing board with
  | nil => exact hCompatible
  | cons coordinate coordinates ih =>
      cases hCell : board.get coordinate.row coordinate.col with
      | unknown =>
          simp only [solutionAssignment, hCell]
          exact ih _ (set_solutionCell_compatible hCompatible coordinate.row coordinate.col)
      | filled =>
          simp only [solutionAssignment, hCell]
          exact ih board hCompatible
      | crossed =>
          simp only [solutionAssignment, hCell]
          exact ih board hCompatible

private theorem solutionAssignment_mem_raw
    (solution : Solution rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    solutionAssignment solution board coordinates ∈
      assignmentBoardsRaw board coordinates := by
  induction coordinates generalizing board with
  | nil => simp [solutionAssignment, assignmentBoardsRaw]
  | cons coordinate coordinates ih =>
      cases hCell : board.get coordinate.row coordinate.col with
      | unknown =>
          cases hValue : solution coordinate.row coordinate.col <;>
            simp [solutionAssignment, assignmentBoardsRaw, solutionCell,
              hCell, hValue, ih]
      | filled => simp [solutionAssignment, assignmentBoardsRaw, hCell, ih]
      | crossed => simp [solutionAssignment, assignmentBoardsRaw, hCell, ih]

private theorem exists_compatible_candidate
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols))
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : board.Compatible solution) :
    exists candidate,
      candidate ∈ candidates puzzle board coordinates ∧
        candidate.Compatible solution := by
  let normalized := coordinates.eraseDups
  let assigned := solutionAssignment solution board normalized
  have hAssignedMem : assigned ∈ assignmentBoards board coordinates := by
    exact solutionAssignment_mem_raw solution board normalized
  have hAssignedCompatible : assigned.Compatible solution :=
    solutionAssignment_compatible solution board normalized hCompatible
  obtain ⟨candidate, passes, hFixedPoint, hCandidateCompatible⟩ :=
    LineSolver.Multi.solveToFixedPoint_exists_sound
      puzzle assigned hSatisfies hAssignedCompatible
  refine ⟨candidate, ?_, hCandidateCompatible⟩
  apply List.mem_filterMap.mpr
  refine ⟨assigned, hAssignedMem, ?_⟩
  simp [Spec.propagate, hFixedPoint]

/--
Every complete puzzle solution compatible with the input board remains
compatible with the board returned by a successful exhaustive weave solve.
-/
theorem solve_sound
    {puzzle : Puzzle rows cols}
    {oldBoard : Board rows cols}
    {coordinates : List (Coordinate rows cols)}
    {result : Result rows cols}
    (hSolve : solve puzzle oldBoard coordinates = .ok result)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    result.board.Compatible solution := by
  obtain ⟨compatibleCandidate, hCandidateMem, hCandidateCompatible⟩ :=
    exists_compatible_candidate puzzle oldBoard coordinates hSatisfies hCompatible
  simp only [solve] at hSolve
  cases hCandidates : candidates puzzle oldBoard coordinates with
  | nil =>
      rw [hCandidates] at hCandidateMem
      simp at hCandidateMem
  | cons candidate rest =>
      cases rest with
      | nil =>
          have hCandidate : compatibleCandidate = candidate := by
            simpa [hCandidates] using hCandidateMem
          subst compatibleCandidate
          simp [hCandidates] at hSolve
          rw [← congrArg Result.board hSolve]
          exact hCandidateCompatible
      | cons next tail =>
          simp [hCandidates] at hSolve
          rw [← congrArg Result.board hSolve]
          exact hCompatible

end WeaveSolver.Naive

end Nonogram
