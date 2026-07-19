import Nonogram.LineSolver.Single
import Nonogram.LineSolver.Soundness.Single.Naive
import Nonogram.LineSolver.Soundness.Single.Placement

namespace Nonogram
namespace LineSolver

/-!
Correctness of the default single-line solver. Implementation-specific
enumeration proofs live under `Soundness.Single`.
-/

open Single.Internal

/-- The default clue-directed implementation meets the declarative specification. -/
theorem solve_exact (clue : Clue) (line : Line length Cell) :
    Spec.ExactOutcome clue line (solve clue line) := by
  exact Single.Placement.solve_exact clue line

private theorem intersect_compatible_of_mem
    {candidate : Line length Bool}
    {candidates : List (Line length Bool)}
    (hMem : candidate ∈ candidates) :
    (intersect candidates).Compatible candidate := by
  intro i
  simp only [intersect]
  split
  next hFilled =>
    simp only [Cell.Compatible]
    exact List.all_eq_true.mp hFilled candidate hMem
  next _ =>
    split
    next hCrossed =>
      simp only [Cell.Compatible]
      have hNot := List.all_eq_true.mp hCrossed candidate hMem
      simpa using hNot
    next _ =>
      simp only [Cell.Compatible]

private theorem intersect_refines
    {known : Line length Cell}
    {candidates : List (Line length Bool)}
    (hNonempty : candidates ≠ [])
    (hCompatible : forall candidate, candidate ∈ candidates -> known.Compatible candidate) :
    (intersect candidates).Refines known := by
  intro i
  cases hKnown : known i with
  | unknown =>
      simp [Cell.Refines]
  | filled =>
      have hAllFilled : candidates.all (fun candidate => candidate i) = true :=
        List.all_eq_true.mpr fun candidate hMem => by
          have hCell := hCompatible candidate hMem i
          simpa [hKnown, Cell.Compatible] using hCell
      simp [intersect, hAllFilled, Cell.Refines]
  | crossed =>
      have hAllCrossed : candidates.all (fun candidate => !candidate i) = true :=
        List.all_eq_true.mpr fun candidate hMem => by
          have hCell := hCompatible candidate hMem i
          simp [hKnown, Cell.Compatible] at hCell
          simp [hCell]
      have hNotAllFilled : candidates.all (fun candidate => candidate i) ≠ true := by
        intro hAllFilled
        have ⟨candidate, hMem⟩ := List.exists_mem_of_ne_nil candidates hNonempty
        have hFilled := List.all_eq_true.mp hAllFilled candidate hMem
        have hCrossed := List.all_eq_true.mp hAllCrossed candidate hMem
        simp [hFilled] at hCrossed
      simp [intersect, hNotAllFilled, hAllCrossed, Cell.Refines]

/-- Every compatible solution remains compatible after a successful solve. -/
theorem solve_sound
    {clue : Clue}
    {line : Line length Cell}
    {result : Result length}
    (hSolve : solve clue line = some result)
    {candidate : Line length Bool}
    (hSatisfies : Line.Satisfies clue candidate)
    (hCompatible : line.Compatible candidate) :
    result.line.Compatible candidate := by
  let lineCandidates := candidates clue line
  change (if lineCandidates.isEmpty then none else some {
    candidateCount := lineCandidates.length
    line := intersect lineCandidates
  }) = some result at hSolve
  split at hSolve
  next _ => simp at hSolve
  next _ =>
    simp only [Option.some.injEq] at hSolve
    subst result
    exact intersect_compatible_of_mem <|
      Single.Placement.mem_candidates_iff_candidate.mpr
        ⟨hSatisfies, hCompatible⟩

/-- A successful solve preserves all information already known in the line. -/
theorem solve_refines
    {clue : Clue}
    {line : Line length Cell}
    {result : Result length}
    (hSolve : solve clue line = some result) :
    result.line.Refines line := by
  let lineCandidates := candidates clue line
  change (if lineCandidates.isEmpty then none else some {
    candidateCount := lineCandidates.length
    line := intersect lineCandidates
  }) = some result at hSolve
  split at hSolve
  next _ => simp at hSolve
  next hNonempty =>
    simp only [Option.some.injEq] at hSolve
    subst result
    apply intersect_refines
    · simpa using hNonempty
    · intro candidate hMem
      exact (Single.Placement.mem_candidates_iff_candidate.mp hMem).2

end LineSolver
end Nonogram
