import Nonogram.SolverStep
import Nonogram.LineSolver.Soundness.Multi
import Nonogram.LineSolver.Soundness.FixedPoint
import Nonogram.WeaveSolver

namespace Nonogram

namespace SolverStep

open LineSolver.Multi

/-- Executable extensional equality for finite boards, used by generated proofs. -/
def boardDecidableEq : DecidableEq (Board rows cols) := fun left right =>
  if h : boardsEqual left right = true then
    isTrue (by
      cases left with
      | mk leftGet =>
          cases right with
          | mk rightGet =>
              congr
              funext row col
              exact (boardsEqual_eq_true_iff _ _).mp h row col)
  else
    isFalse (fun hEqual => by
      apply h
      subst right
      exact (boardsEqual_eq_true_iff _ _).mpr (fun _ _ => rfl))

instance : DecidableEq (Board rows cols) := boardDecidableEq

instance [DecidableEq error] [DecidableEq value] :
    DecidableEq (Except error value)
  | .error left, .error right =>
      match decEq left right with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (fun hEqual => h (Except.error.inj hEqual))
  | .ok left, .ok right =>
      match decEq left right with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (fun hEqual => h (Except.ok.inj hEqual))
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)

private theorem clear_compatible
    {board : Board rows cols}
    {solution : Solution rows cols}
    (hCompatible : board.Compatible solution)
    (row : Fin rows)
    (col : Fin cols) :
    (board.set row col .unknown).Compatible solution where
  cell currentRow currentCol := by
    simp only [Board.set]
    split
    next _ => simp [Cell.Compatible]
    next _ => exact hCompatible.cell currentRow currentCol

/-- Every sound transcript step preserves a compatible complete solution. -/
theorem run_exists_sound
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (steps : List (SolverStep rows cols))
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : board.Compatible solution) :
    exists finalBoard,
      run puzzle board steps = .ok finalBoard ∧
        finalBoard.Compatible solution := by
  induction steps generalizing board with
  | nil => exact ⟨board, rfl, hCompatible⟩
  | cons step steps ih =>
      cases step with
      | targets targets =>
          obtain ⟨result, hRun, hFinal⟩ :=
            solveTargets_exists_sound puzzle board targets hSatisfies hCompatible
          obtain ⟨finalBoard, hRest, hFinalCompatible⟩ :=
            ih result.board hFinal
          refine ⟨finalBoard, ?_, hFinalCompatible⟩
          have hApply : apply puzzle board (.targets targets) = .ok result.board := by
            simp [apply, hRun] <;> rfl
          rw [run, hApply]
          exact hRest
      | fixedPoint =>
          obtain ⟨nextBoard, passes, hRun, hNext⟩ :=
            solveToFixedPoint_exists_sound puzzle board hSatisfies hCompatible
          obtain ⟨finalBoard, hRest, hFinalCompatible⟩ :=
            ih nextBoard hNext
          refine ⟨finalBoard, ?_, hFinalCompatible⟩
          have hApply : apply puzzle board .fixedPoint = .ok nextBoard := by
            simp [apply, hRun] <;> rfl
          rw [run, hApply]
          exact hRest
      | weave coordinates =>
          obtain ⟨result, hRun, hNext⟩ :=
            WeaveSolver.solve_exists_sound puzzle board coordinates
              hSatisfies hCompatible
          obtain ⟨finalBoard, hRest, hFinalCompatible⟩ :=
            ih result.board hNext
          refine ⟨finalBoard, ?_, hFinalCompatible⟩
          have hApply : apply puzzle board (.weave coordinates) = .ok result.board := by
            simp [apply, hRun] <;> rfl
          rw [run, hApply]
          exact hRest
      | clear row col =>
          obtain ⟨finalBoard, hRest, hFinalCompatible⟩ :=
            ih (board.set row col .unknown)
              (clear_compatible hCompatible row col)
          refine ⟨finalBoard, ?_, hFinalCompatible⟩
          have hApply : apply puzzle board (.clear row col) =
              .ok (board.set row col .unknown) := by
            rfl
          rw [run, hApply]
          exact hRest

/-- A sound transcript reporting an error proves that the puzzle is unsolvable. -/
theorem run_error_unsolvable
    {puzzle : Puzzle rows cols}
    {steps : List (SolverStep rows cols)}
    (hRun : run puzzle Board.unknown steps = .error ()) :
    puzzle.Unsolvable := by
  intro hSolvable
  rcases hSolvable with ⟨solution, hSatisfies⟩
  obtain ⟨finalBoard, hSuccess, _⟩ :=
    run_exists_sound puzzle Board.unknown steps hSatisfies
      ⟨fun r c => by simp [Board.unknown, Cell.Compatible]⟩
  rw [hRun] at hSuccess
  cases hSuccess

private theorem ofSolution_compatible_solution
    (solution : Solution rows cols) :
    (Board.ofSolution solution).Compatible solution where
  cell row col := by
    cases h : solution row col <;>
      simp [Board.ofSolution, h, Cell.Compatible]

private theorem ofSolution_compatible_iff
    {solution other : Solution rows cols}
    (hCompatible : (Board.ofSolution solution).Compatible other) :
    other = solution := by
  funext row col
  have hCell := hCompatible.cell row col
  cases h : solution row col <;>
    simpa [Board.ofSolution, h, Cell.Compatible] using hCell

/-- A complete sound transcript proves uniqueness from its decided solution. -/
theorem run_unique
    {puzzle : Puzzle rows cols}
    {steps : List (SolverStep rows cols)}
    {solution : Solution rows cols}
    (hRun : run puzzle Board.unknown steps =
      .ok (Board.ofSolution solution))
    (hSatisfies : solution.Satisfies puzzle) :
    puzzle.UniquelySolvable := by
  refine ⟨solution, hSatisfies, ?_⟩
  intro other hOther
  obtain ⟨finalBoard, hSuccess, hCompatible⟩ :=
    run_exists_sound puzzle Board.unknown steps hOther
      ⟨fun r c => by simp [Board.unknown, Cell.Compatible]⟩
  rw [hRun] at hSuccess
  cases hSuccess
  exact ofSolution_compatible_iff hCompatible

end SolverStep

end Nonogram
