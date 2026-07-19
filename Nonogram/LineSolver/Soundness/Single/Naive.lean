import Nonogram.LineSolver.Single.Naive
import Nonogram.LineSolver.Soundness.Single.Enumeration

namespace Nonogram

namespace LineSolver.Single.Naive

/-!
Correctness of the exhaustive single-line implementation: candidate
enumeration and exact output. The default solver's soundness and refinement
theorems live in the parent `Soundness.Single` module.
-/

open LineSolver.Single.Internal

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

private theorem length_of_mem_assignments
    {cells : List Bool}
    (hMem : cells ∈ assignments length) :
    cells.length = length := by
  induction length generalizing cells with
  | zero =>
      simp [assignments] at hMem
      subst cells
      rfl
  | succ length ih =>
      simp only [assignments, List.mem_append, List.mem_map] at hMem
      rcases hMem with ⟨tail, hTail, rfl⟩ | ⟨tail, hTail, rfl⟩ <;>
        simp [ih hTail]

private theorem ofList_injective_of_lengths
    {left right : List Bool}
    (hLeftLength : left.length = length)
    (hRightLength : right.length = length)
    (hEqual : ofList left = (ofList right : Line length Bool)) :
    left = right := by
  apply List.ext_get (hLeftLength.trans hRightLength.symm)
  intro index hIndexLeft hIndexRight
  have hIndex : index < length := hLeftLength ▸ hIndexLeft
  have hAtIndex := congrFun hEqual ⟨index, hIndex⟩
  simpa [ofList, List.getD, hIndexLeft, hIndexRight] using hAtIndex

private theorem assignments_nodup (length : Nat) :
    (assignments length).Nodup := by
  induction length with
  | zero => simp [assignments]
  | succ length ih =>
      simp only [assignments, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact ih.map (false :: ·) fun left right hNe hEqual =>
          hNe (List.cons.inj hEqual).2
      · exact ih.map (true :: ·) fun left right hNe hEqual =>
          hNe (List.cons.inj hEqual).2
      · intro left hLeft right hRight
        obtain ⟨leftTail, _, rfl⟩ := List.mem_map.mp hLeft
        obtain ⟨rightTail, _, rfl⟩ := List.mem_map.mp hRight
        intro hEqual
        exact Bool.noConfusion (List.cons.inj hEqual).1

private theorem map_ofList_nodup
    (items : List (List Bool))
    (hNodup : items.Nodup)
    (hLength : forall cells, cells ∈ items -> cells.length = length) :
    (items.map ofList : List (Line length Bool)).Nodup := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at hNodup
      simp only [List.map]
      rw [List.nodup_cons]
      constructor
      · intro hMapped
        obtain ⟨other, hOther, hEqual⟩ := List.mem_map.mp hMapped
        have hHeadEqual : head = other := ofList_injective_of_lengths
          (hLength head List.mem_cons_self)
          (hLength other (List.mem_cons_of_mem head hOther))
          hEqual.symm
        apply hNodup.1
        rw [hHeadEqual]
        exact hOther
      · apply ih hNodup.2
        intro cells hCells
        exact hLength cells (List.mem_cons_of_mem head hCells)

private theorem mapped_assignments_nodup (length : Nat) :
    ((assignments length).map ofList : List (Line length Bool)).Nodup :=
  map_ofList_nodup _ (assignments_nodup length) fun _ hCells =>
    length_of_mem_assignments hCells

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

/-- The executable candidate list contains exactly the semantic candidates. -/
theorem mem_candidates_iff_candidate
    {clue : Clue}
    {line : Line length Cell}
    {candidate : Line length Bool} :
    candidate ∈ candidates clue line ↔ Spec.Candidate clue line candidate := by
  constructor
  · intro hMem
    have hFilter := (List.mem_filter.mp hMem).2
    rw [Bool.and_eq_true] at hFilter
    constructor
    · simpa [Line.satisfies, Line.Satisfies] using hFilter.1
    · exact (compatible_eq_true_iff _ _).mp hFilter.2
  · intro hCandidate
    exact mem_candidates hCandidate.1 hCandidate.2

/-- The executable candidate list has no duplicates. -/
theorem candidates_nodup (clue : Clue) (line : Line length Cell) :
    (candidates clue line).Nodup := by
  unfold candidates
  exact (mapped_assignments_nodup length).filter _

/-- The executable list is a finite enumeration of the declarative candidate set. -/
theorem candidates_enumerate (clue : Clue) (line : Line length Cell) :
    Spec.Enumerates clue line (candidates clue line) := by
  exact ⟨candidates_nodup clue line,
    fun _ => mem_candidates_iff_candidate⟩

/-- The exhaustive single-line implementation meets the declarative specification. -/
theorem solve_exact (clue : Clue) (line : Line length Cell) :
    Spec.ExactOutcome clue line (solve clue line) := by
  let items := candidates clue line
  change Spec.ExactOutcome clue line <|
    if items.isEmpty then none else some {
      candidateCount := items.length
      line := intersect items
    }
  exact LineSolver.Single.Soundness.exactOutcome_of_enumerates items
    (candidates_enumerate clue line)

end LineSolver.Single.Naive

end Nonogram
