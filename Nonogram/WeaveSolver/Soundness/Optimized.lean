import Nonogram.WeaveSolver.Optimized
import Nonogram.WeaveSolver.Soundness.Naive

namespace Nonogram

namespace WeaveSolver.Optimized

private theorem merge_ofCandidates
    (left right : List (Board rows cols)) :
    Summary.merge (Summary.ofCandidates left) (Summary.ofCandidates right) =
      Summary.ofCandidates (left ++ right) := by
  cases left with
  | nil => rfl
  | cons leftHead leftTail =>
      cases leftTail with
      | nil =>
          cases right with
          | nil => rfl
          | cons rightHead rightTail =>
              cases rightTail <;> simp [Summary.merge, Summary.ofCandidates]
      | cons leftSecond leftRest =>
          cases right with
          | nil => simp [Summary.merge, Summary.ofCandidates]
          | cons rightHead rightTail =>
              cases rightTail <;>
                simp [Summary.merge, Summary.ofCandidates, List.length_append,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem assignmentCountRaw_eq_spec
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    assignmentCountRaw board coordinates =
      (Spec.assignmentBoardsRaw board coordinates).length := by
  induction coordinates generalizing board with
  | nil => rfl
  | cons coordinate coordinates ih =>
      cases hCell : board.get coordinate.row coordinate.col <;>
        simp [assignmentCountRaw, Spec.assignmentBoardsRaw, hCell, ih]

/-- The streaming assignment counter equals the specification's enumeration size. -/
theorem assignmentCount_eq_spec
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    assignmentCount board coordinates =
      (Spec.assignmentBoards board coordinates).length := by
  exact assignmentCountRaw_eq_spec board coordinates.eraseDups

private theorem searchRaw_eq_spec
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    searchRaw puzzle board coordinates =
      Summary.ofCandidates
        ((Spec.assignmentBoardsRaw board coordinates).filterMap
          (Spec.propagate puzzle)) := by
  induction coordinates generalizing board with
  | nil =>
      cases hPropagate : Spec.propagate puzzle board <;>
        simp [searchRaw, Spec.assignmentBoardsRaw, hPropagate,
          Summary.ofCandidates]
  | cons coordinate coordinates ih =>
      cases hCell : board.get coordinate.row coordinate.col with
      | unknown =>
          simp only [searchRaw, Spec.assignmentBoardsRaw, hCell,
            List.filterMap_append, ih]
          exact merge_ofCandidates _ _
      | filled => simp [searchRaw, Spec.assignmentBoardsRaw, hCell, ih]
      | crossed => simp [searchRaw, Spec.assignmentBoardsRaw, hCell, ih]

/-- The streaming DFS summary exactly represents the specification's survivors. -/
theorem search_eq_spec
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    search puzzle board coordinates =
      Summary.ofCandidates (Spec.candidates puzzle board coordinates) := by
  exact searchRaw_eq_spec puzzle board coordinates.eraseDups

/-- The streaming DFS implementation meets the weave behavioral specification. -/
theorem solve_exact
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Spec.ExactOutcome puzzle board coordinates (solve puzzle board coordinates) := by
  simp only [solve]
  rw [assignmentCount_eq_spec, search_eq_spec]
  cases hCandidates : Spec.candidates puzzle board coordinates with
  | nil => simp [Summary.ofCandidates, Spec.ExactOutcome, hCandidates]
  | cons candidate rest =>
      cases rest with
      | nil => simp [Summary.ofCandidates, Spec.ExactOutcome,
          Spec.ExactResult, hCandidates]
      | cons next tail => simp [Summary.ofCandidates, Spec.ExactOutcome,
          Spec.ExactResult, hCandidates]

/--
Every compatible complete puzzle solution survives a successful streaming
solve.
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
  have hExact := solve_exact puzzle oldBoard coordinates
  have hNaiveExact := Naive.solve_exact puzzle oldBoard coordinates
  cases hNaive : Naive.solve puzzle oldBoard coordinates with
  | error error =>
      rw [hNaive] at hNaiveExact
      rw [hSolve] at hExact
      simp only [Spec.ExactOutcome] at hNaiveExact hExact
      exact (hExact.1 hNaiveExact).elim
  | ok naiveResult =>
      have hNaiveSound := Naive.solve_sound hNaive hSatisfies hCompatible
      rw [hNaive] at hNaiveExact
      rw [hSolve] at hExact
      cases hCandidates : Spec.candidates puzzle oldBoard coordinates with
      | nil => simp [Spec.ExactOutcome, Spec.ExactResult, hCandidates] at hExact
      | cons candidate rest =>
          cases rest with
          | nil =>
              simp [Spec.ExactOutcome, Spec.ExactResult, hCandidates] at hExact
              simp [Spec.ExactOutcome, Spec.ExactResult, hCandidates] at hNaiveExact
              rw [hExact.2.2.2, ← hNaiveExact.2.2.2]
              exact hNaiveSound
          | cons next tail =>
              simp [Spec.ExactOutcome, Spec.ExactResult, hCandidates] at hExact
              simp [Spec.ExactOutcome, Spec.ExactResult, hCandidates] at hNaiveExact
              rw [hExact.2.2.2]
              exact hCompatible

/--
The streaming weave solve succeeds whenever a compatible complete solution
exists, and its result preserves that solution.
-/
theorem solve_exists_sound
    (puzzle : Puzzle rows cols)
    (oldBoard : Board rows cols)
    (coordinates : List (Coordinate rows cols))
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    exists result,
      solve puzzle oldBoard coordinates = .ok result ∧
        result.board.Compatible solution := by
  obtain ⟨naiveResult, hNaive, _⟩ :=
    Naive.solve_exists_sound puzzle oldBoard coordinates hSatisfies hCompatible
  have hNaiveExact := Naive.solve_exact puzzle oldBoard coordinates
  rw [hNaive] at hNaiveExact
  cases hOptimized : solve puzzle oldBoard coordinates with
  | error error =>
      have hOptimizedExact := solve_exact puzzle oldBoard coordinates
      rw [hOptimized] at hOptimizedExact
      simp only [Spec.ExactOutcome] at hNaiveExact hOptimizedExact
      exact (hNaiveExact.1 hOptimizedExact).elim
  | ok result =>
      exact ⟨result, rfl,
        solve_sound hOptimized hSatisfies hCompatible⟩

end WeaveSolver.Optimized

end Nonogram
