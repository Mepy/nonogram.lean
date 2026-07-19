import Nonogram.Basic

namespace Nonogram

/-- The lengths of the black runs in one line, from left to right. -/
abbrev Clue := List Nat

namespace Clue

/-- The least line length needed by a clue, including separators. -/
def requiredLength : Clue -> Nat
  | [] => 0
  | [block] => block
  | block :: next :: rest => block + 1 + requiredLength (next :: rest)

/-- A clue contains only positive runs and fits in a line of this length. -/
def WellFormed (lineLength : Nat) (clue : Clue) : Prop :=
  And
    (forall block, List.Mem block clue -> 0 < block)
    (requiredLength clue <= lineLength)

/-- Executable counterpart of `WellFormed`. -/
def isWellFormed (lineLength : Nat) (clue : Clue) : Bool :=
  clue.all (fun block => decide (0 < block)) &&
    decide (requiredLength clue <= lineLength)

/-- Render a clue as space-separated run lengths; an empty clue is left blank. -/
def render (clue : Clue) : String :=
  if clue.isEmpty then
    ""
  else
    String.intercalate " " (clue.map toString)

end Clue

namespace Line

namespace Internal

/-- Accumulator used by `blackRuns`. Exposed only to support solver proofs. -/
def blackRunsAux : List Bool -> Nat -> List Nat -> List Nat
  | [], current, completed =>
      let completed := if current = 0 then completed else current :: completed
      completed.reverse
  | true :: rest, current, completed =>
      blackRunsAux rest (current + 1) completed
  | false :: rest, current, completed =>
      if current = 0 then
        blackRunsAux rest 0 completed
      else
        blackRunsAux rest 0 (current :: completed)

end Internal

/-- Compute the lengths of all maximal black runs in a Boolean list. -/
def blackRuns (cells : List Bool) : List Nat :=
  Internal.blackRunsAux cells 0 []

namespace Internal

theorem blackRunsAux_completed
    (cells : List Bool)
    (current : Nat)
    (completed : List Nat) :
    blackRunsAux cells current completed =
      completed.reverse ++ blackRunsAux cells current [] := by
  induction cells generalizing current completed with
  | nil =>
      simp [blackRunsAux]
      split <;> simp_all
  | cons cell cells ih =>
      cases cell with
      | false =>
          simp only [blackRunsAux]
          split
          next hCurrent =>
            simpa [hCurrent] using ih 0 completed
          next _ =>
            rw [ih 0 (current :: completed), ih 0 [current]]
            simp [List.reverse_cons, List.append_assoc]
      | true =>
          simp only [blackRunsAux]
          exact ih (current + 1) completed

theorem blackRunsAux_white_prefix
    (leading : Nat)
    (cells : List Bool)
    (completed : List Nat) :
    blackRunsAux (List.replicate leading false ++ cells) 0 completed =
      blackRunsAux cells 0 completed := by
  induction leading with
  | zero => rfl
  | succ leading ih =>
      simp [List.replicate_succ, blackRunsAux, ih]

theorem blackRunsAux_black_prefix
    (block current : Nat)
    (cells : List Bool)
    (completed : List Nat) :
    blackRunsAux (List.replicate block true ++ cells) current completed =
      blackRunsAux cells (current + block) completed := by
  induction block generalizing current with
  | zero => simp
  | succ block ih =>
      simp only [List.replicate_succ, List.cons_append, blackRunsAux]
      rw [ih]
      congr 1
      omega

end Internal

@[simp] theorem blackRuns_white (length : Nat) :
    blackRuns (List.replicate length false) = [] := by
  rw [blackRuns]
  simpa [Internal.blackRunsAux] using
    Internal.blackRunsAux_white_prefix length [] []

theorem blackRuns_block_cons
    (leading block : Nat)
    (suffix : List Bool)
    (hBlock : 0 < block) :
    blackRuns
        (List.replicate leading false ++
          List.replicate block true ++ false :: suffix) =
      block :: blackRuns suffix := by
  rw [blackRuns, List.append_assoc]
  rw [Internal.blackRunsAux_white_prefix, Internal.blackRunsAux_black_prefix]
  simp only [Internal.blackRunsAux, Nat.zero_add]
  split
  next h => omega
  next _ =>
    rw [Internal.blackRunsAux_completed]
    rfl

theorem blackRuns_single_block
    (leading block trailing : Nat)
    (hBlock : 0 < block) :
    blackRuns
        (List.replicate leading false ++
          List.replicate block true ++ List.replicate trailing false) =
      [block] := by
  cases trailing with
  | zero =>
      rw [blackRuns, List.append_assoc]
      rw [Internal.blackRunsAux_white_prefix, Internal.blackRunsAux_black_prefix]
      simp [Internal.blackRunsAux, Nat.ne_of_gt hBlock]
  | succ trailing =>
      rw [List.replicate_succ]
      simpa using blackRuns_block_cons leading block
        (List.replicate trailing false) hBlock

@[simp] theorem blackRuns_false_cons (cells : List Bool) :
    blackRuns (false :: cells) = blackRuns cells := by
  rfl

private theorem exists_initial_black (tail : List Bool) :
    exists block suffix,
      0 < block ∧
      true :: tail = List.replicate block true ++ suffix ∧
      (suffix = [] ∨ exists rest, suffix = false :: rest) := by
  induction tail with
  | nil =>
      exact ⟨1, [], by omega, rfl, Or.inl rfl⟩
  | cons cell tail ih =>
      cases cell with
      | false =>
          exact ⟨1, false :: tail, by omega, rfl, Or.inr ⟨tail, rfl⟩⟩
      | true =>
          obtain ⟨block, suffix, hBlock, hEqual, hSuffix⟩ := ih
          refine ⟨block + 1, suffix, by omega, ?_, hSuffix⟩
          rw [show block + 1 = block.succ by omega, List.replicate_succ]
          exact congrArg (true :: ·) hEqual

private theorem blackRuns_true_ne_nil (tail : List Bool) :
    blackRuns (true :: tail) ≠ [] := by
  obtain ⟨block, suffix, hBlock, hEqual, hSuffix⟩ :=
    exists_initial_black tail
  rw [hEqual]
  rcases hSuffix with rfl | ⟨rest, rfl⟩
  · have hRuns := blackRuns_single_block 0 block 0 hBlock
    intro hNil
    have hEqual : blackRuns (List.replicate block true) = [block] := by
      simpa using hRuns
    simp only [List.append_nil] at hNil
    rw [hEqual] at hNil
    simp at hNil
  · have hRuns := blackRuns_block_cons 0 block rest hBlock
    intro hNil
    have hEqual : blackRuns (List.replicate block true ++ false :: rest) =
        block :: blackRuns rest := by simpa using hRuns
    rw [hEqual] at hNil
    simp at hNil

theorem eq_replicate_false_of_blackRuns_eq_nil
    {cells : List Bool}
    (hRuns : blackRuns cells = []) :
    cells = List.replicate cells.length false := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      cases cell with
      | false =>
          simp only [blackRuns_false_cons] at hRuns
          rw [List.length_cons, List.replicate_succ, ← ih hRuns]
      | true =>
          exact (blackRuns_true_ne_nil cells hRuns).elim

/-- Split a line at its first black run. -/
theorem exists_first_run
    {cells : List Bool}
    {block : Nat}
    {rest : List Nat}
    (hRuns : blackRuns cells = block :: rest) :
    exists leading suffix,
      0 < block ∧
      cells =
        List.replicate leading false ++
          List.replicate block true ++ suffix ∧
      ((suffix = [] ∧ rest = []) ∨
        exists tail, suffix = false :: tail ∧ blackRuns tail = rest) := by
  induction cells with
  | nil => simp [blackRuns, Internal.blackRunsAux] at hRuns
  | cons cell cells ih =>
      cases cell with
      | false =>
          simp only [blackRuns_false_cons] at hRuns
          obtain ⟨leading, suffix, hBlock, hEqual, hSuffix⟩ := ih hRuns
          refine ⟨leading + 1, suffix, hBlock, ?_, hSuffix⟩
          rw [show leading + 1 = leading.succ by omega, List.replicate_succ]
          exact congrArg (false :: ·) hEqual
      | true =>
          obtain ⟨found, suffix, hFound, hEqual, hSuffix⟩ :=
            exists_initial_black cells
          rw [hEqual] at hRuns ⊢
          rcases hSuffix with rfl | ⟨tail, rfl⟩
          · have hFoundRuns := blackRuns_single_block 0 found 0 hFound
            rw [show blackRuns (List.replicate found true ++ []) = [found] by
              simpa using hFoundRuns] at hRuns
            simp only [List.cons.injEq] at hRuns
            obtain ⟨rfl, rfl⟩ := hRuns
            exact ⟨0, [], hFound, by simp, Or.inl ⟨rfl, rfl⟩⟩
          · have hFoundRuns := blackRuns_block_cons 0 found tail hFound
            rw [show blackRuns (List.replicate found true ++ false :: tail) =
                found :: blackRuns tail by simpa using hFoundRuns] at hRuns
            simp only [List.cons.injEq] at hRuns
            obtain ⟨rfl, hTail⟩ := hRuns
            exact ⟨0, false :: tail, hFound, by simp,
              Or.inr ⟨tail, rfl, hTail⟩⟩

/-- Compute the black runs of a finite line. -/
def runs (line : Line length Bool) : List Nat :=
  blackRuns line.toList

/-- A Boolean line satisfies a clue when its black runs equal the clue. -/
def Satisfies (clue : Clue) (line : Line length Bool) : Prop :=
  line.runs = clue

/-- Executable counterpart of `Satisfies`. -/
def satisfies (clue : Clue) (line : Line length Bool) : Bool :=
  line.runs == clue

end Line

namespace Clue

/-- Every line satisfying a clue is at least as long as its required span. -/
theorem requiredLength_le_length_of_blackRuns
    {cells : List Bool}
    {clue : Clue}
    (hRuns : Line.blackRuns cells = clue) :
    requiredLength clue <= cells.length := by
  induction clue generalizing cells with
  | nil => simp [requiredLength]
  | cons block rest ih =>
      obtain ⟨leading, suffix, _, hCells, hSuffix⟩ :=
        Line.exists_first_run hRuns
      cases rest with
      | nil =>
          simp only [requiredLength]
          rw [hCells]
          simp
          omega
      | cons next rest =>
          rcases hSuffix with ⟨_, hRest⟩ | ⟨tail, rfl, hTailRuns⟩
          · contradiction
          · have hTail := ih hTailRuns
            rw [hCells]
            simp only [requiredLength, List.length_append,
              List.length_replicate, List.length_cons]
            omega

end Clue

end Nonogram
