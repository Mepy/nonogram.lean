import Nonogram.LineSolver

namespace Nonogram

namespace LineSolver

/-!
Soundness and refinement proofs for `solve`, which handles one row or column
as an independent line. Board-level row/column replacement and repeated line
solving are outside this module's scope.
-/

open Internal

private theorem mem_assignments_of_length
    (cells : List Bool)
    (hLength : cells.length = length) :
    cells ∈ assignments length := by
  induction length generalizing cells with
  | zero =>
      cases cells with
      | nil => simp [assignments]
      | cons head tail => simp at hLength
  | succ length ih =>
      cases cells with
      | nil => simp at hLength
      | cons head tail =>
          simp only [List.length_cons, Nat.succ.injEq] at hLength
          subst hLength
          cases head <;> simp [assignments, ih tail rfl]

private theorem ofList_ofFn (line : Line length Bool) :
    ofList (List.ofFn line) = line := by
  funext i
  simp [ofList, List.getD]

private theorem compatibleCell_eq_true_iff (known : Cell) (candidate : Bool) :
    compatibleCell known candidate = true ↔ Cell.Compatible known candidate := by
  cases known <;> cases candidate <;> simp [compatibleCell, Cell.Compatible]

private theorem compatible_eq_true_iff
    (known : Line length Cell)
    (candidate : Line length Bool) :
    compatible known candidate = true ↔ known.Compatible candidate := by
  simp only [compatible, List.all_eq_true, id_eq, List.mem_ofFn, Line.Compatible]
  constructor
  · intro h i
    exact (compatibleCell_eq_true_iff _ _).mp (h _ ⟨i, rfl⟩)
  · intro h cell ⟨i, hi⟩
    rw [← hi]
    exact (compatibleCell_eq_true_iff _ _).mpr (h i)

private theorem mem_candidates
    {clue : Clue}
    {line : Line length Cell}
    {candidate : Line length Bool}
    (hSatisfies : Line.Satisfies clue candidate)
    (hCompatible : line.Compatible candidate) :
    candidate ∈ candidates clue line := by
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_map.mpr
    refine ⟨List.ofFn candidate, ?_, ?_⟩
    · exact mem_assignments_of_length _ List.length_ofFn
    · exact ofList_ofFn candidate
  · simp only [Bool.and_eq_true]
    constructor
    · simpa [Line.satisfies, Line.Satisfies] using hSatisfies
    · exact (compatible_eq_true_iff _ _).mpr hCompatible

private theorem compatible_of_mem_candidates
    {clue : Clue}
    {line : Line length Cell}
    {candidate : Line length Bool}
    (hMem : candidate ∈ candidates clue line) :
    line.Compatible candidate := by
  have hFilter := (List.mem_filter.mp hMem).2
  rw [Bool.and_eq_true] at hFilter
  exact (compatible_eq_true_iff _ _).mp hFilter.2

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

/--
Every satisfying Boolean line compatible with the input remains compatible
after one successful call to the single-line solver.
-/
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
    exact intersect_compatible_of_mem (mem_candidates hSatisfies hCompatible)

/--
One successful call to the single-line solver never forgets or changes
information already present in that line.
-/
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
      exact compatible_of_mem_candidates hMem

end LineSolver

end Nonogram
