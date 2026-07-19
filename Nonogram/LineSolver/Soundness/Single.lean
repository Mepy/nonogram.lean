import Nonogram.LineSolver.Single

namespace Nonogram

namespace LineSolver

/-!
Correctness of the exhaustive single-line implementation: candidate
enumeration, exact output, soundness, and refinement. Board-level replacement
and repeated line solving are outside this module's scope.
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

private theorem compatible_of_mem_candidates
    {clue : Clue}
    {line : Line length Cell}
    {candidate : Line length Bool}
    (hMem : candidate ∈ candidates clue line) :
    line.Compatible candidate := by
  have hFilter := (List.mem_filter.mp hMem).2
  rw [Bool.and_eq_true] at hFilter
  exact (compatible_eq_true_iff _ _).mp hFilter.2

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
  exact ⟨candidates_nodup clue line, fun _ => mem_candidates_iff_candidate⟩

private theorem canBe_iff_exists_mem
    {clue : Clue}
    {line : Line length Cell}
    {index : Fin length}
    {value : Bool} :
    Spec.CanBe clue line index value ↔
      exists candidate, candidate ∈ candidates clue line ∧ candidate index = value := by
  constructor
  · rintro ⟨candidate, hCandidate, hValue⟩
    exact ⟨candidate, mem_candidates_iff_candidate.mpr hCandidate, hValue⟩
  · rintro ⟨candidate, hMem, hValue⟩
    exact ⟨candidate, mem_candidates_iff_candidate.mp hMem, hValue⟩

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
    (hNonempty : candidates clue line ≠ []) :
    Spec.ExactLine clue line (intersect (candidates clue line)) := by
  intro index
  simp only [intersect]
  split
  next hAllFilled =>
    simp only [Spec.ExactCell]
    constructor
    · have ⟨candidate, hMem⟩ := List.exists_mem_of_ne_nil _ hNonempty
      apply canBe_iff_exists_mem.mpr
      exact ⟨candidate, hMem, List.all_eq_true.mp hAllFilled candidate hMem⟩
    · intro hCanBeFalse
      obtain ⟨candidate, hMem, hFalse⟩ := canBe_iff_exists_mem.mp hCanBeFalse
      have hTrue := List.all_eq_true.mp hAllFilled candidate hMem
      simp [hFalse] at hTrue
  next hNotAllFilled =>
    split
    next hAllCrossed =>
      simp only [Spec.ExactCell]
      constructor
      · have ⟨candidate, hMem⟩ := List.exists_mem_of_ne_nil _ hNonempty
        apply canBe_iff_exists_mem.mpr
        have hFalse := List.all_eq_true.mp hAllCrossed candidate hMem
        simp at hFalse
        exact ⟨candidate, hMem, hFalse⟩
      · intro hCanBeTrue
        obtain ⟨candidate, hMem, hTrue⟩ := canBe_iff_exists_mem.mp hCanBeTrue
        have hFalse := List.all_eq_true.mp hAllCrossed candidate hMem
        simp [hTrue] at hFalse
    next hNotAllCrossed =>
      simp only [Spec.ExactCell]
      constructor
      · apply canBe_iff_exists_mem.mpr
        exact exists_false_of_not_all_true hNotAllFilled
      · apply canBe_iff_exists_mem.mpr
        exact exists_true_of_not_all_false hNotAllCrossed

/-- The exhaustive single-line implementation meets the declarative specification. -/
theorem solve_exact (clue : Clue) (line : Line length Cell) :
    Spec.ExactOutcome clue line (solve clue line) := by
  let items := candidates clue line
  change Spec.ExactOutcome clue line <|
    if items.isEmpty then none else some {
      candidateCount := items.length
      line := intersect items
    }
  split
  next hEmpty =>
    simp only [Spec.ExactOutcome, Spec.HasCandidateCount]
    refine ⟨items, ?_, ?_⟩
    · exact candidates_enumerate clue line
    · simpa using hEmpty
  next hNonempty =>
    simp only [Spec.ExactOutcome, Spec.ExactResult]
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨items, candidates_enumerate clue line, rfl⟩
    · apply List.length_pos_iff.mpr
      simpa using hNonempty
    · apply intersect_exactLine
      simpa using hNonempty

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
