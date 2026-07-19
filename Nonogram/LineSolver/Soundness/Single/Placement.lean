import Nonogram.LineSolver.Single.Placement
import Nonogram.LineSolver.Soundness.Single.Enumeration

namespace Nonogram
namespace LineSolver.Single.Placement

open LineSolver.Single.Internal Placement.Internal

/-- Raw clue-directed placements are exactly the satisfying Boolean lists. -/
theorem mem_rawPlacements_iff
    {cells : List Bool} :
    cells ∈ rawPlacements length clue ↔
      cells.length = length ∧ Line.blackRuns cells = clue := by
  induction clue generalizing length cells with
  | nil =>
      simp only [rawPlacements, List.mem_singleton]
      constructor
      · intro hCells
        subst cells
        exact ⟨by simp [white], by simp [white]⟩
      · rintro ⟨hLength, hRuns⟩
        rw [Line.eq_replicate_false_of_blackRuns_eq_nil hRuns, hLength]
        rfl
  | cons block rest ih =>
      by_cases hBlock : block = 0
      · subst block
        simp only [rawPlacements, ↓reduceIte, List.not_mem_nil, false_iff]
        rintro ⟨_, hRuns⟩
        obtain ⟨_, _, hPositive, _⟩ := Line.exists_first_run hRuns
        omega
      · cases rest with
        | nil =>
            simp only [rawPlacements, hBlock, ↓reduceIte]
            by_cases hFits : block <= length
            · simp only [hFits, ↓reduceIte, List.mem_map, List.mem_range]
              constructor
              · rintro ⟨leading, hLeading, rfl⟩
                constructor
                · simp only [white, black, List.length_append,
                    List.length_replicate]
                  omega
                · exact Line.blackRuns_single_block leading block
                    (length - leading - block) (Nat.zero_lt_of_ne_zero hBlock)
              · rintro ⟨hLength, hRuns⟩
                obtain ⟨leading, suffix, _, hCells, hSuffix⟩ :=
                  Line.exists_first_run hRuns
                have hSuffixRuns : Line.blackRuns suffix = [] := by
                  rcases hSuffix with ⟨rfl, _⟩ | ⟨tail, rfl, hTail⟩
                  · rfl
                  · simpa using hTail
                have hSuffixCells :=
                  Line.eq_replicate_false_of_blackRuns_eq_nil hSuffixRuns
                refine ⟨leading, ?_, ?_⟩
                · rw [hCells] at hLength
                  simp only [List.length_append, List.length_replicate] at hLength
                  omega
                · rw [hCells, hSuffixCells]
                  congr 2
                  rw [hCells] at hLength
                  simp only [List.length_append, List.length_replicate] at hLength
                  omega
            · constructor
              · simp [hFits]
              · rintro ⟨_, hRuns⟩
                have hRequired := Clue.requiredLength_le_length_of_blackRuns hRuns
                simp only [Clue.requiredLength] at hRequired
                omega
        | cons next rest =>
            let tailClue := next :: rest
            let needed := block + 1 + Clue.requiredLength tailClue
            rw [rawPlacements]
            simp only [hBlock, ↓reduceIte]
            change (cells ∈ if needed <= length then _ else []) ↔ _
            by_cases hFits : needed <= length
            · simp only [hFits, ↓reduceIte, List.mem_flatMap, List.mem_range,
                List.mem_map]
              constructor
              · rintro ⟨leading, hLeading, suffix, hSuffix, rfl⟩
                have hTail := (ih (length := length - leading - block - 1)
                  (cells := suffix)).mp hSuffix
                constructor
                · simp only [white, black, List.length_append,
                    List.length_replicate, List.length_cons]
                  omega
                · rw [show Line.blackRuns
                      (white leading ++ black block ++ false :: suffix) =
                        block :: Line.blackRuns suffix by
                      simpa [white, black] using
                        Line.blackRuns_block_cons leading block suffix
                          (Nat.zero_lt_of_ne_zero hBlock)]
                  rw [hTail.2]
              · rintro ⟨hLength, hRuns⟩
                obtain ⟨leading, suffix, _, hCells, hSuffix⟩ :=
                  Line.exists_first_run hRuns
                rcases hSuffix with ⟨_, hRest⟩ | ⟨tail, rfl, hTailRuns⟩
                · contradiction
                · refine ⟨leading, ?_, tail, ?_, ?_⟩
                  · rw [hCells] at hLength
                    simp only [List.length_append, List.length_replicate,
                      List.length_cons] at hLength
                    have hTailRequired :=
                      Clue.requiredLength_le_length_of_blackRuns hTailRuns
                    dsimp only [needed, tailClue] at hFits ⊢
                    omega
                  · apply (ih (length := length - leading - block - 1)
                      (cells := tail)).mpr
                    constructor
                    · rw [hCells] at hLength
                      simp only [List.length_append, List.length_replicate,
                        List.length_cons] at hLength
                      omega
                    · exact hTailRuns
                  · simpa [white, black] using hCells.symm
            · constructor
              · dsimp only [needed, tailClue] at hFits ⊢
                simp only [hFits, ↓reduceIte, List.not_mem_nil, false_implies]
              · rintro ⟨_, hRuns⟩
                have hRequired := Clue.requiredLength_le_length_of_blackRuns hRuns
                dsimp only [needed, tailClue] at hFits
                simp only [Clue.requiredLength] at hRequired
                omega

private theorem eraseDups_nodup {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (items : List alpha) : items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro hMem
        rw [List.mem_eraseDups] at hMem
        simp at hMem
      · exact eraseDups_nodup (tail.filter fun other => other != head)
termination_by items.length
decreasing_by
  have hLength := List.length_filter_le (fun other => other != head) tail
  simpa using Nat.lt_succ_of_le hLength

private theorem ofList_ofFn (line : Line length Bool) :
    ofList (List.ofFn line) = line := by
  funext i
  simp [ofList, List.getD]

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

/-- Clue-directed candidates are exactly the semantic candidates. -/
theorem mem_candidates_iff_candidate
    {clue : Clue}
    {line : Line length Cell}
    {candidate : Line length Bool} :
    candidate ∈ candidates clue line ↔ Spec.Candidate clue line candidate := by
  constructor
  · intro hMem
    obtain ⟨hMapped, hCompatible⟩ := List.mem_filter.mp hMem
    obtain ⟨cells, hRaw, hEqual⟩ := List.mem_map.mp hMapped
    have hRawSpec := mem_rawPlacements_iff.mp (List.mem_eraseDups.mp hRaw)
    have hCells : cells = List.ofFn candidate :=
      ofList_injective_of_lengths hRawSpec.1 List.length_ofFn <| by
        rw [hEqual, ofList_ofFn]
    constructor
    · change Line.blackRuns (List.ofFn candidate) = clue
      rw [← hCells]
      exact hRawSpec.2
    · exact (compatible_eq_true_iff _ _).mp hCompatible
  · rintro ⟨hSatisfies, hCompatible⟩
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_map.mpr
      refine ⟨List.ofFn candidate, ?_, ofList_ofFn candidate⟩
      apply List.mem_eraseDups.mpr
      apply mem_rawPlacements_iff.mpr
      exact ⟨List.length_ofFn, hSatisfies⟩
    · exact (compatible_eq_true_iff _ _).mpr hCompatible

/-- The clue-directed candidate list contains no duplicates. -/
theorem candidates_nodup (clue : Clue) (line : Line length Cell) :
    (candidates clue line).Nodup := by
  unfold candidates
  exact (map_ofList_nodup _ (eraseDups_nodup _) fun cells hCells =>
    (mem_rawPlacements_iff.mp (List.mem_eraseDups.mp hCells)).1).filter _

/-- The clue-directed list is an exact finite candidate enumeration. -/
theorem candidates_enumerate (clue : Clue) (line : Line length Cell) :
    Spec.Enumerates clue line (candidates clue line) :=
  ⟨candidates_nodup clue line, fun _ => mem_candidates_iff_candidate⟩

/-- The clue-directed solver meets the declarative single-line specification. -/
theorem solve_exact (clue : Clue) (line : Line length Cell) :
    Spec.ExactOutcome clue line (solve clue line) := by
  let items := candidates clue line
  change Spec.ExactOutcome clue line <|
    if items.isEmpty then none else some {
      candidateCount := items.length
      line := intersect items
    }
  exact Single.Soundness.exactOutcome_of_enumerates items
    (candidates_enumerate clue line)

end LineSolver.Single.Placement
end Nonogram
