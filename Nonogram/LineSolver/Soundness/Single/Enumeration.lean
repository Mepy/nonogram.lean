import Nonogram.LineSolver.Single.Internal

namespace Nonogram
namespace LineSolver.Single.Soundness

open LineSolver.Single.Internal

private theorem canBe_iff_exists_mem
    {clue : Clue}
    {line : Line length Cell}
    {items : List (Line length Bool)}
    (hEnumerates : Spec.Enumerates clue line items)
    {index : Fin length}
    {value : Bool} :
    Spec.CanBe clue line index value ↔
      exists candidate, candidate ∈ items ∧ candidate index = value := by
  constructor
  · rintro ⟨candidate, hCandidate, hValue⟩
    exact ⟨candidate, (hEnumerates.2 candidate).mpr hCandidate, hValue⟩
  · rintro ⟨candidate, hMem, hValue⟩
    exact ⟨candidate, (hEnumerates.2 candidate).mp hMem, hValue⟩

private theorem exists_false_of_not_all_true
    {items : List (Line length Bool)}
    {index : Fin length}
    (hNotAll : items.all (fun candidate => candidate index) ≠ true) :
    exists candidate, candidate ∈ items ∧ candidate index = false := by
  apply Classical.byContradiction
  intro hNoFalse
  apply hNotAll
  apply List.all_eq_true.mpr
  intro candidate hMem
  cases hValue : candidate index with
  | false => exact (hNoFalse ⟨candidate, hMem, hValue⟩).elim
  | true => rfl

private theorem exists_true_of_not_all_false
    {items : List (Line length Bool)}
    {index : Fin length}
    (hNotAll : items.all (fun candidate => !candidate index) ≠ true) :
    exists candidate, candidate ∈ items ∧ candidate index = true := by
  apply Classical.byContradiction
  intro hNoTrue
  apply hNotAll
  apply List.all_eq_true.mpr
  intro candidate hMem
  cases hValue : candidate index with
  | false => rfl
  | true => exact (hNoTrue ⟨candidate, hMem, hValue⟩).elim

private theorem intersect_exactLine
    {clue : Clue}
    {line : Line length Cell}
    {items : List (Line length Bool)}
    (hEnumerates : Spec.Enumerates clue line items)
    (hNonempty : items ≠ []) :
    Spec.ExactLine clue line (intersect items) := by
  intro index
  simp only [intersect]
  split
  next hAllFilled =>
    simp only [Spec.ExactCell]
    constructor
    · have ⟨candidate, hMem⟩ := List.exists_mem_of_ne_nil _ hNonempty
      apply (canBe_iff_exists_mem hEnumerates).mpr
      exact ⟨candidate, hMem, List.all_eq_true.mp hAllFilled candidate hMem⟩
    · intro hCanBeFalse
      obtain ⟨candidate, hMem, hFalse⟩ :=
        (canBe_iff_exists_mem hEnumerates).mp hCanBeFalse
      have hTrue := List.all_eq_true.mp hAllFilled candidate hMem
      simp [hFalse] at hTrue
  next hNotAllFilled =>
    split
    next hAllCrossed =>
      simp only [Spec.ExactCell]
      constructor
      · have ⟨candidate, hMem⟩ := List.exists_mem_of_ne_nil _ hNonempty
        apply (canBe_iff_exists_mem hEnumerates).mpr
        have hFalse := List.all_eq_true.mp hAllCrossed candidate hMem
        simp at hFalse
        exact ⟨candidate, hMem, hFalse⟩
      · intro hCanBeTrue
        obtain ⟨candidate, hMem, hTrue⟩ :=
          (canBe_iff_exists_mem hEnumerates).mp hCanBeTrue
        have hFalse := List.all_eq_true.mp hAllCrossed candidate hMem
        simp [hTrue] at hFalse
    next hNotAllCrossed =>
      simp only [Spec.ExactCell]
      constructor
      · apply (canBe_iff_exists_mem hEnumerates).mpr
        exact exists_false_of_not_all_true hNotAllFilled
      · apply (canBe_iff_exists_mem hEnumerates).mpr
        exact exists_true_of_not_all_false hNotAllCrossed

/-- Intersecting any exact candidate enumeration meets the line-solver spec. -/
theorem exactOutcome_of_enumerates
    {clue : Clue}
    {line : Line length Cell}
    (items : List (Line length Bool))
    (hEnumerates : Spec.Enumerates clue line items) :
    Spec.ExactOutcome clue line <|
      if items.isEmpty then
        none
      else
        some {
          candidateCount := items.length
          line := intersect items
        } := by
  split
  next hEmpty =>
    simp only [Spec.ExactOutcome, Spec.HasCandidateCount]
    exact ⟨items, hEnumerates, by simpa using hEmpty⟩
  next hNonempty =>
    simp only [Spec.ExactOutcome, Spec.ExactResult]
    refine ⟨⟨items, hEnumerates, rfl⟩, ?_, ?_⟩
    · apply List.length_pos_iff.mpr
      simpa using hNonempty
    · apply intersect_exactLine hEnumerates
      simpa using hNonempty

end LineSolver.Single.Soundness
end Nonogram
