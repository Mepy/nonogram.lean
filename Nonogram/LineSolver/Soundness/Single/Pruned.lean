import Nonogram.LineSolver.Single.Pruned
import Nonogram.LineSolver.Soundness.Single.Placement

namespace Nonogram
namespace LineSolver.Single.Pruned

open LineSolver.Single.Internal Pruned.Internal

private theorem compatibleCells_append
    {knownPrefix knownSuffix : List Cell}
    {candidatePrefix candidateSuffix : List Bool}
    (hLength : knownPrefix.length = candidatePrefix.length) :
    compatibleCells (knownPrefix ++ knownSuffix)
        (candidatePrefix ++ candidateSuffix) =
      (compatibleCells knownPrefix candidatePrefix &&
        compatibleCells knownSuffix candidateSuffix) := by
  induction knownPrefix generalizing candidatePrefix with
  | nil =>
      cases candidatePrefix with
      | nil => simp [compatibleCells]
      | cons => simp at hLength
  | cons known knownPrefix ih =>
      cases candidatePrefix with
      | nil => simp at hLength
      | cons candidate candidatePrefix =>
          simp only [List.length_cons, Nat.succ.injEq] at hLength
          simp [compatibleCells, ih hLength, Bool.and_assoc]

private theorem compatibleCells_split
    {known : List Cell}
    {placed suffix : List Bool}
    (hLength : placed.length <= known.length) :
    compatibleCells known (placed ++ suffix) =
      (compatibleCells (known.take placed.length) placed &&
        compatibleCells (known.drop placed.length) suffix) := by
  calc
    compatibleCells known (placed ++ suffix) =
        compatibleCells
          (known.take placed.length ++ known.drop placed.length)
          (placed ++ suffix) := by rw [List.take_append_drop]
    _ = _ := compatibleCells_append <| by
      simp [List.length_take, Nat.min_eq_left hLength]

/-- Pruning retains exactly the compatible clue-directed placements. -/
theorem mem_placements_iff
    {cells : List Bool} :
    cells ∈ placements known clue ↔
      cells ∈ Placement.rawPlacements known.length clue ∧
        compatibleCells known cells = true := by
  induction clue generalizing known cells with
  | nil =>
      rw [placements, Placement.rawPlacements]
      simp only [Placement.Internal.white, List.mem_singleton]
      change (cells ∈
          if compatibleCells known (white known.length) then
            [white known.length]
          else []) ↔
        cells = white known.length ∧ compatibleCells known cells = true
      by_cases hCompatible : compatibleCells known (white known.length) = true
      · simp only [hCompatible, ↓reduceIte, List.mem_singleton]
        constructor
        · intro hCells
          subst cells
          exact ⟨rfl, hCompatible⟩
        · exact And.left
      · have hFalse : compatibleCells known (white known.length) = false := by
          cases hValue : compatibleCells known (white known.length) with
          | false => rfl
          | true => exact (hCompatible hValue).elim
        simp only [hFalse, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil,
          false_iff]
        rintro ⟨rfl, hTrue⟩
        rw [hFalse] at hTrue
        contradiction
  | cons block rest ih =>
      by_cases hBlock : block = 0
      · subst block
        simp [placements, Placement.rawPlacements]
      · cases rest with
        | nil =>
            rw [placements, Placement.rawPlacements]
            simp only [hBlock, ↓reduceIte]
            by_cases hFits : block <= known.length
            · simp only [hFits, ↓reduceIte, List.mem_filterMap,
                List.mem_range, List.mem_map]
              constructor
              · rintro ⟨leading, hLeading, hCandidate⟩
                split at hCandidate
                next hCompatible =>
                  simp only [Option.some.injEq] at hCandidate
                  subst cells
                  exact ⟨⟨leading, hLeading, rfl⟩, hCompatible⟩
                next _ => simp at hCandidate
              · rintro ⟨⟨leading, hLeading, rfl⟩, hCompatible⟩
                refine ⟨leading, hLeading, ?_⟩
                simp only [white, black, Placement.Internal.white,
                  Placement.Internal.black, List.append_assoc] at hCompatible ⊢
                simp [hCompatible]
            · simp [hFits]
        | cons next rest =>
            let tailClue := next :: rest
            let needed := block + 1 + Clue.requiredLength tailClue
            rw [placements, Placement.rawPlacements]
            simp only [hBlock, ↓reduceIte]
            change (cells ∈ if needed <= known.length then _ else []) ↔
              (cells ∈ if needed <= known.length then _ else []) ∧ _
            by_cases hFits : needed <= known.length
            · simp only [hFits, ↓reduceIte, List.mem_flatMap, List.mem_range,
                List.mem_map]
              constructor
              · rintro ⟨leading, hLeading, hCells⟩
                let placed := white leading ++ black block ++ [false]
                change cells ∈
                  if compatibleCells (known.take placed.length) placed then
                    (placements (known.drop placed.length) tailClue).map
                      (placed ++ ·)
                  else [] at hCells
                by_cases hPlaced :
                    compatibleCells (known.take placed.length) placed = true
                · simp only [hPlaced, ↓reduceIte, List.mem_map] at hCells
                  obtain ⟨suffix, hSuffix, rfl⟩ := hCells
                  have hSuffixSpec := ih.mp hSuffix
                  have hDropLength : (known.drop placed.length).length =
                      known.length - leading - block - 1 := by
                    simp only [List.length_drop]
                    dsimp only [placed]
                    simp only [white, black, List.length_append,
                      List.length_replicate, List.length_cons, List.length_nil]
                    omega
                  rw [hDropLength] at hSuffixSpec
                  refine ⟨⟨leading, hLeading, suffix, hSuffixSpec.1, ?_⟩, ?_⟩
                  · simp [placed, white, black, Placement.Internal.white,
                      Placement.Internal.black, List.append_assoc]
                  rw [compatibleCells_split]
                  · rw [Bool.and_eq_true]
                    exact ⟨hPlaced, hSuffixSpec.2⟩
                  · dsimp only [placed]
                    simp only [white, black, List.length_append,
                      List.length_replicate, List.length_cons, List.length_nil]
                    dsimp only [needed, tailClue] at hFits
                    omega
                · simp [hPlaced] at hCells
              · rintro ⟨⟨leading, hLeading, suffix, hSuffix, rfl⟩, hCompatible⟩
                let placed := white leading ++ black block ++ [false]
                have hPlacedLength : placed.length <= known.length := by
                  dsimp only [placed]
                  simp only [white, black, List.length_append,
                    List.length_replicate, List.length_cons, List.length_nil]
                  dsimp only [needed, tailClue] at hFits
                  omega
                have hCompatible' :
                    compatibleCells known (placed ++ suffix) = true := by
                  simpa [placed, white, black, Placement.Internal.white,
                    Placement.Internal.black, List.append_assoc] using hCompatible
                rw [compatibleCells_split hPlacedLength] at hCompatible'
                rw [Bool.and_eq_true] at hCompatible'
                obtain ⟨hPlaced, hSuffixCompatible⟩ := hCompatible'
                have hDropLength : (known.drop placed.length).length =
                    known.length - leading - block - 1 := by
                  simp only [List.length_drop]
                  dsimp only [placed]
                  simp only [white, black, List.length_append,
                    List.length_replicate, List.length_cons, List.length_nil]
                  omega
                refine ⟨leading, hLeading, ?_⟩
                rw [hPlaced]
                simp only [↓reduceIte, List.mem_map]
                refine ⟨suffix, ?_, ?_⟩
                · apply ih.mpr
                  rw [hDropLength]
                  exact ⟨hSuffix, hSuffixCompatible⟩
                · simp [white, black, Placement.Internal.white,
                    Placement.Internal.black, List.append_assoc]
            · simp [hFits]

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

private theorem compatibleCells_ofFn
    (known : Line length Cell)
    (candidate : Line length Bool) :
    compatibleCells (List.ofFn known) (List.ofFn candidate) =
      compatible known candidate := by
  unfold compatible
  induction length with
  | zero => simp [compatibleCells]
  | succ length ih =>
      simp only [List.ofFn_succ, compatibleCells, List.all_cons]
      congr 1
      exact ih (fun i => known i.succ) (fun i => candidate i.succ)

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

/-- Pruned candidates are exactly the semantic candidates. -/
theorem mem_candidates_iff_candidate
    {clue : Clue}
    {line : Line length Cell}
    {candidate : Line length Bool} :
    candidate ∈ candidates clue line ↔ Spec.Candidate clue line candidate := by
  constructor
  · intro hMem
    obtain ⟨cells, hCellsMem, hEqual⟩ := List.mem_map.mp hMem
    have hPlacement := mem_placements_iff.mp <| List.mem_eraseDups.mp hCellsMem
    have hRaw := Placement.mem_rawPlacements_iff.mp hPlacement.1
    have hCells : cells = List.ofFn candidate :=
      ofList_injective_of_lengths
        (by simpa [Line.toList] using hRaw.1)
        List.length_ofFn <| by rw [hEqual, ofList_ofFn]
    constructor
    · change Line.blackRuns (List.ofFn candidate) = clue
      rw [← hCells]
      exact hRaw.2
    · apply (compatible_eq_true_iff _ _).mp
      rw [← compatibleCells_ofFn]
      simpa [Line.toList, hCells] using hPlacement.2
  · rintro ⟨hSatisfies, hCompatible⟩
    apply List.mem_map.mpr
    refine ⟨List.ofFn candidate, ?_, ofList_ofFn candidate⟩
    apply List.mem_eraseDups.mpr
    apply mem_placements_iff.mpr
    constructor
    · apply Placement.mem_rawPlacements_iff.mpr
      exact ⟨by simp [Line.toList], hSatisfies⟩
    · change compatibleCells (List.ofFn line) (List.ofFn candidate) = true
      rw [compatibleCells_ofFn]
      exact (compatible_eq_true_iff _ _).mpr hCompatible

/-- The pruned candidate list contains no duplicates. -/
theorem candidates_nodup (clue : Clue) (line : Line length Cell) :
    (candidates clue line).Nodup := by
  unfold candidates
  apply map_ofList_nodup
  · exact eraseDups_nodup _
  · intro cells hCells
    have hPlacement := mem_placements_iff.mp (List.mem_eraseDups.mp hCells)
    have hRaw := Placement.mem_rawPlacements_iff.mp hPlacement.1
    simpa [Line.toList] using hRaw.1

/-- The pruned list is an exact finite candidate enumeration. -/
theorem candidates_enumerate (clue : Clue) (line : Line length Cell) :
    Spec.Enumerates clue line (candidates clue line) :=
  ⟨candidates_nodup clue line, fun _ => mem_candidates_iff_candidate⟩

/-- The compatibility-pruned solver meets the declarative specification. -/
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

end LineSolver.Single.Pruned
end Nonogram
