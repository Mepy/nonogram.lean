import Nonogram.LineSolver.Board
import Nonogram.LineSolver.Soundness

namespace Nonogram

namespace LineSolver.BoardSolver

/-!
Board-level correctness for line solving. The theorems cover one row or
column replacement, any finite mixed target sequence, one full row-and-column
pass, and the repeated full passes used by `line **`. Manual cell edits are
outside this module's scope.
-/

private theorem replaceRow_compatible
    {board : Board rows cols}
    {solution : Solution rows cols}
    {row : Fin rows}
    {line : Line cols Cell}
    (hLine : line.Compatible (solution.row row))
    (hBoard : board.Compatible solution) :
    (board.replaceRow row line).Compatible solution where
  cell currentRow col := by
    simp only [Board.replaceRow]
    split
    next h =>
      subst currentRow
      exact hLine col
    next _ => exact hBoard.cell currentRow col

private theorem replaceCol_compatible
    {board : Board rows cols}
    {solution : Solution rows cols}
    {col : Fin cols}
    {line : Line rows Cell}
    (hLine : line.Compatible (solution.col col))
    (hBoard : board.Compatible solution) :
    (board.replaceCol col line).Compatible solution where
  cell row currentCol := by
    simp only [Board.replaceCol]
    split
    next h =>
      subst currentCol
      exact hLine row
    next _ => exact hBoard.cell row currentCol

private theorem replaceRow_refines
    {board : Board rows cols}
    {row : Fin rows}
    {line : Line cols Cell}
    (hLine : line.Refines (board.row row)) :
    (board.replaceRow row line).Refines board where
  cell currentRow col := by
    simp only [Board.replaceRow]
    split
    next h =>
      subst currentRow
      exact hLine col
    next _ => exact Cell.Refines.refl _

private theorem replaceCol_refines
    {board : Board rows cols}
    {col : Fin cols}
    {line : Line rows Cell}
    (hLine : line.Refines (board.col col)) :
    (board.replaceCol col line).Refines board where
  cell row currentCol := by
    simp only [Board.replaceCol]
    split
    next h =>
      subst currentCol
      exact hLine row
    next _ => exact Cell.Refines.refl _

/-- Solving and replacing one selected row or column preserves every puzzle solution. -/
theorem solveTarget_sound
    {puzzle : Puzzle rows cols}
    {oldBoard newBoard : Board rows cols}
    {target : Target rows cols}
    {solved : SolvedTarget rows cols}
    (hSolve : solveTarget puzzle oldBoard target = some (newBoard, solved))
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    newBoard.Compatible solution := by
  cases target with
  | row row =>
      cases hLine : LineSolver.solve (puzzle.rowClues row) (oldBoard.row row) with
      | none => simp [solveTarget, hLine] at hSolve
      | some result =>
          simp only [solveTarget, hLine, Option.some.injEq] at hSolve
          cases hSolve
          exact replaceRow_compatible
            (LineSolver.solve_sound hLine (hSatisfies.row row) fun col =>
              hCompatible.cell row col)
            hCompatible
  | col col =>
      cases hLine : LineSolver.solve (puzzle.colClues col) (oldBoard.col col) with
      | none => simp [solveTarget, hLine] at hSolve
      | some result =>
          simp only [solveTarget, hLine, Option.some.injEq] at hSolve
          cases hSolve
          exact replaceCol_compatible
            (LineSolver.solve_sound hLine (hSatisfies.col col) fun row =>
              hCompatible.cell row col)
            hCompatible

/-- Solving and replacing one selected row or column refines the input board. -/
theorem solveTarget_refines
    {puzzle : Puzzle rows cols}
    {oldBoard newBoard : Board rows cols}
    {target : Target rows cols}
    {solved : SolvedTarget rows cols}
    (hSolve : solveTarget puzzle oldBoard target = some (newBoard, solved)) :
    newBoard.Refines oldBoard := by
  cases target with
  | row row =>
      cases hLine : LineSolver.solve (puzzle.rowClues row) (oldBoard.row row) with
      | none => simp [solveTarget, hLine] at hSolve
      | some result =>
          simp only [solveTarget, hLine, Option.some.injEq] at hSolve
          cases hSolve
          exact replaceRow_refines (LineSolver.solve_refines hLine)
  | col col =>
      cases hLine : LineSolver.solve (puzzle.colClues col) (oldBoard.col col) with
      | none => simp [solveTarget, hLine] at hSolve
      | some result =>
          simp only [solveTarget, hLine, Option.some.injEq] at hSolve
          cases hSolve
          exact replaceCol_refines (LineSolver.solve_refines hLine)

/-- Any successful finite sequence of row and column solves preserves every solution. -/
theorem solveTargets_sound
    {puzzle : Puzzle rows cols}
    {oldBoard : Board rows cols}
    {targets : List (Target rows cols)}
    {result : Result rows cols}
    (hSolve : solveTargets puzzle oldBoard targets = .ok result)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    result.board.Compatible solution := by
  induction targets generalizing oldBoard result with
  | nil =>
      simp only [solveTargets, Except.ok.injEq] at hSolve
      rw [← congrArg Result.board hSolve]
      exact hCompatible
  | cons target targets ih =>
      simp only [solveTargets] at hSolve
      cases hTarget : solveTarget puzzle oldBoard target with
      | none => simp [hTarget] at hSolve
      | some output =>
          rcases output with ⟨nextBoard, solvedTarget⟩
          simp only [hTarget] at hSolve
          cases hRest : solveTargets puzzle nextBoard targets with
          | error failed => simp [hRest] at hSolve
          | ok rest =>
              simp only [hRest, Except.ok.injEq] at hSolve
              rw [← congrArg Result.board hSolve]
              exact ih (result := rest) hRest
                (solveTarget_sound hTarget hSatisfies hCompatible)

/-- Any successful finite sequence of row and column solves refines its input board. -/
theorem solveTargets_refines
    {puzzle : Puzzle rows cols}
    {oldBoard : Board rows cols}
    {targets : List (Target rows cols)}
    {result : Result rows cols}
    (hSolve : solveTargets puzzle oldBoard targets = .ok result) :
    result.board.Refines oldBoard := by
  induction targets generalizing oldBoard result with
  | nil =>
      simp only [solveTargets, Except.ok.injEq] at hSolve
      rw [← congrArg Result.board hSolve]
      exact Board.Refines.refl oldBoard
  | cons target targets ih =>
      simp only [solveTargets] at hSolve
      cases hTarget : solveTarget puzzle oldBoard target with
      | none => simp [hTarget] at hSolve
      | some output =>
          rcases output with ⟨nextBoard, solvedTarget⟩
          simp only [hTarget] at hSolve
          cases hRest : solveTargets puzzle nextBoard targets with
          | error failed => simp [hRest] at hSolve
          | ok rest =>
              simp only [hRest, Except.ok.injEq] at hSolve
              rw [← congrArg Result.board hSolve]
              exact Board.Refines.trans
                (ih (result := rest) hRest)
                (solveTarget_refines hTarget)

/-- One successful full row-and-column pass preserves every puzzle solution. -/
theorem solveAll_sound
    {puzzle : Puzzle rows cols}
    {oldBoard : Board rows cols}
    {result : Result rows cols}
    (hSolve : solveAll puzzle oldBoard = .ok result)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    result.board.Compatible solution :=
  solveTargets_sound hSolve hSatisfies hCompatible

/-- One successful full row-and-column pass refines its input board. -/
theorem solveAll_refines
    {puzzle : Puzzle rows cols}
    {oldBoard : Board rows cols}
    {result : Result rows cols}
    (hSolve : solveAll puzzle oldBoard = .ok result) :
    result.board.Refines oldBoard :=
  solveTargets_refines hSolve

private def isUnknown : Cell -> Bool
  | .unknown => true
  | .filled | .crossed => false

private def unknownCountLine (line : Line length Cell) : Nat :=
  (List.ofFn line).countP isUnknown

private theorem unknownCountLine_le_of_refines
    {newLine oldLine : Line length Cell}
    (hRefines : newLine.Refines oldLine) :
    unknownCountLine newLine <= unknownCountLine oldLine := by
  induction length with
  | zero => simp [unknownCountLine]
  | succ length ih =>
      have hTail :
          Line.Refines (fun i : Fin length => newLine i.succ)
            (fun i : Fin length => oldLine i.succ) :=
        fun i => hRefines i.succ
      have hInduction := ih hTail
      have hHead := hRefines (0 : Fin (length + 1))
      simp only [unknownCountLine, List.ofFn_succ, List.countP_cons] at hInduction ⊢
      cases hOld : oldLine 0 with
      | unknown =>
          cases hNew : newLine 0
          · simpa [isUnknown] using Nat.add_le_add_right hInduction 1
          · simpa [isUnknown] using Nat.le.step hInduction
          · simpa [isUnknown] using Nat.le.step hInduction
      | filled =>
          simp [Cell.Refines, hOld] at hHead
          simp [hHead, isUnknown]
          exact hInduction
      | crossed =>
          simp [Cell.Refines, hOld] at hHead
          simp [hHead, isUnknown]
          exact hInduction

private theorem unknownCountLine_lt_of_refines_of_exists
    {newLine oldLine : Line length Cell}
    (hRefines : newLine.Refines oldLine)
    (hDiff : exists i, newLine i ≠ oldLine i) :
    unknownCountLine newLine < unknownCountLine oldLine := by
  induction length with
  | zero =>
      obtain ⟨i, _⟩ := hDiff
      exact Fin.elim0 i
  | succ length ih =>
      have hTail :
          Line.Refines (fun i : Fin length => newLine i.succ)
            (fun i : Fin length => oldLine i.succ) :=
        fun i => hRefines i.succ
      have hTailLe := unknownCountLine_le_of_refines hTail
      by_cases hHeadEq : newLine 0 = oldLine 0
      · have hDiffTail : exists i : Fin length, newLine i.succ ≠ oldLine i.succ := by
          obtain ⟨i, hi⟩ := hDiff
          refine Fin.cases (motive := fun i => newLine i ≠ oldLine i ->
            exists j : Fin length, newLine j.succ ≠ oldLine j.succ) ?_ ?_ i hi
          · intro h
            exact (h hHeadEq).elim
          · intro j h
            exact ⟨j, h⟩
        have hTailLt := ih hTail hDiffTail
        simp only [unknownCountLine, List.ofFn_succ, List.countP_cons]
        rw [hHeadEq]
        exact Nat.add_lt_add_right hTailLt _
      · have hOldUnknown : oldLine 0 = .unknown := by
          have hHead := hRefines (0 : Fin (length + 1))
          cases hOld : oldLine 0 with
          | unknown => rfl
          | filled =>
              simp [Cell.Refines, hOld] at hHead
              exact (hHeadEq (hHead.trans hOld.symm)).elim
          | crossed =>
              simp [Cell.Refines, hOld] at hHead
              exact (hHeadEq (hHead.trans hOld.symm)).elim
        cases hNew : newLine 0 with
        | unknown => exact (hHeadEq (hNew.trans hOldUnknown.symm)).elim
        | filled =>
            simp only [unknownCountLine, List.ofFn_succ, List.countP_cons]
            simpa [unknownCountLine, hNew, hOldUnknown, isUnknown] using
              Nat.lt_succ_of_le hTailLe
        | crossed =>
            simp only [unknownCountLine, List.ofFn_succ, List.countP_cons]
            simpa [unknownCountLine, hNew, hOldUnknown, isUnknown] using
              Nat.lt_succ_of_le hTailLe

private def finSum (values : Fin length -> Nat) : Nat :=
  (List.ofFn values).sum

private theorem finSum_le
    {left right : Fin length -> Nat}
    (h : forall i, left i <= right i) :
    finSum left <= finSum right := by
  induction length with
  | zero => simp [finSum]
  | succ length ih =>
      simp only [finSum, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (h 0) (ih fun i => h i.succ)

private theorem finSum_lt_of_exists
    {left right : Fin length -> Nat}
    (hLe : forall i, left i <= right i)
    (hLt : exists i, left i < right i) :
    finSum left < finSum right := by
  induction length with
  | zero =>
      obtain ⟨i, _⟩ := hLt
      exact Fin.elim0 i
  | succ length ih =>
      simp only [finSum, List.ofFn_succ, List.sum_cons]
      by_cases hHead : left 0 < right 0
      · exact Nat.add_lt_add_of_lt_of_le hHead
          (finSum_le fun i : Fin length => hLe i.succ)
      · have hHeadEq : left 0 = right 0 :=
          Nat.le_antisymm (hLe 0) (Nat.le_of_not_gt hHead)
        have hTailLt : exists i : Fin length, left i.succ < right i.succ := by
          obtain ⟨i, hi⟩ := hLt
          refine Fin.cases (motive := fun i => left i < right i ->
            exists j : Fin length, left j.succ < right j.succ) ?_ ?_ i hi
          · intro h
            exact (Nat.ne_of_lt h hHeadEq).elim
          · intro j h
            exact ⟨j, h⟩
        rw [hHeadEq]
        exact Nat.add_lt_add_left (ih (fun i => hLe i.succ) hTailLt) _

private theorem finSum_const (length value : Nat) :
    finSum (fun _ : Fin length => value) = length * value := by
  induction length with
  | zero => simp [finSum]
  | succ length ih =>
      rw [show finSum (fun _ : Fin (length + 1) => value) =
        value + finSum (fun _ : Fin length => value) by
          simp [finSum, List.ofFn_succ]]
      rw [ih, Nat.succ_mul, Nat.add_comm]

private def unknownCount (board : Board rows cols) : Nat :=
  finSum fun row => unknownCountLine (board.row row)

private theorem unknownCount_le_cells (board : Board rows cols) :
    unknownCount board <= rows * cols := by
  calc
    unknownCount board <= finSum (fun _ : Fin rows => cols) := by
      apply finSum_le
      intro row
      simpa only [unknownCountLine, List.length_ofFn] using
        (List.countP_le_length (p := isUnknown) (l := List.ofFn (board.row row)))
    _ = rows * cols := finSum_const rows cols

private theorem unknownCount_lt_of_refines_of_exists
    {newBoard oldBoard : Board rows cols}
    (hRefines : newBoard.Refines oldBoard)
    (hDiff : exists row col, newBoard.get row col ≠ oldBoard.get row col) :
    unknownCount newBoard < unknownCount oldBoard := by
  apply finSum_lt_of_exists
  · intro row
    apply unknownCountLine_le_of_refines
    exact fun col => hRefines.cell row col
  · obtain ⟨row, col, hCell⟩ := hDiff
    refine ⟨row, unknownCountLine_lt_of_refines_of_exists
      (fun col => hRefines.cell row col) ?_⟩
    exact ⟨col, hCell⟩

private theorem cell_beq_eq_true_iff (left right : Cell) :
    (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide

private theorem board_ext
    {left right : Board rows cols}
    (h : forall row col, left.get row col = right.get row col) :
    left = right := by
  cases left with
  | mk leftGet =>
      cases right with
      | mk rightGet =>
          congr
          funext row col
          exact h row col

/-- `boardsEqual` is true exactly when all cells of the two boards are equal. -/
theorem boardsEqual_eq_true_iff (left right : Board rows cols) :
    boardsEqual left right = true ↔
      forall row col, left.get row col = right.get row col := by
  constructor
  · intro h row col
    have hRows := List.all_eq_true.mp h
    have hRow := hRows _ (List.mem_ofFn.mpr ⟨row, rfl⟩)
    have hCells := List.all_eq_true.mp hRow
    have hCell := hCells _ (List.mem_ofFn.mpr ⟨col, rfl⟩)
    exact (cell_beq_eq_true_iff _ _).mp hCell
  · intro h
    apply List.all_eq_true.mpr
    intro rowCells hRowMem
    obtain ⟨row, hRow⟩ := List.mem_ofFn.mp hRowMem
    rw [← hRow]
    apply List.all_eq_true.mpr
    intro cell hCellMem
    obtain ⟨col, hCol⟩ := List.mem_ofFn.mp hCellMem
    rw [← hCol]
    exact (cell_beq_eq_true_iff _ _).mpr (h row col)

private theorem exists_cell_ne_of_boardsEqual_eq_false
    {left right : Board rows cols}
    (hEqual : boardsEqual left right = false) :
    exists row col, left.get row col ≠ right.get row col := by
  apply Classical.byContradiction
  intro hNoDiff
  simp only [not_exists] at hNoDiff
  have hAll : forall row col, left.get row col = right.get row col := by
    intro row col
    exact Classical.byContradiction fun h => hNoDiff row col h
  have hTrue := (boardsEqual_eq_true_iff left right).mpr hAll
  rw [hTrue] at hEqual
  contradiction

/-- Another full pass succeeds without changing a stable board. -/
def Stable (puzzle : Puzzle rows cols) (board : Board rows cols) : Prop :=
  exists result, solveAll puzzle board = .ok result ∧ result.board = board

private theorem solveToFixedPointWithFuel_stable
    {puzzle : Puzzle rows cols}
    {fuel passes finalPasses : Nat}
    {oldBoard newBoard : Board rows cols}
    (hFuel : unknownCount oldBoard < fuel)
    (hSolve : solveToFixedPointWithFuel puzzle fuel oldBoard passes =
      .ok (newBoard, finalPasses)) :
    Stable puzzle newBoard := by
  induction fuel generalizing oldBoard newBoard passes finalPasses with
  | zero => exact (Nat.not_lt_zero _ hFuel).elim
  | succ fuel ih =>
      simp only [solveToFixedPointWithFuel] at hSolve
      cases hAll : solveAll puzzle oldBoard with
      | error target => simp [hAll] at hSolve
      | ok result =>
          simp only [hAll] at hSolve
          split at hSolve
          next hEqual =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hSolve
            rw [← hSolve.1]
            refine ⟨result, ?_, rfl⟩
            rw [board_ext ((boardsEqual_eq_true_iff result.board oldBoard).mp hEqual)]
            exact hAll
          next hNotEqual =>
            apply ih
            · have hDecrease : unknownCount result.board < unknownCount oldBoard :=
                unknownCount_lt_of_refines_of_exists
                  (solveAll_refines hAll)
                  (exists_cell_ne_of_boardsEqual_eq_false
                    (Bool.eq_false_iff.mpr hNotEqual))
              exact Nat.lt_of_lt_of_le hDecrease (Nat.le_of_lt_succ hFuel)
            · exact hSolve

/--
The fixed-point solver's `rows * cols + 1` fuel is sufficient: every successful
return is a board on which another full pass makes no change.
-/
theorem solveToFixedPoint_stable
    {puzzle : Puzzle rows cols}
    {oldBoard newBoard : Board rows cols}
    {passes : Nat}
    (hSolve : solveToFixedPoint puzzle oldBoard = .ok (newBoard, passes)) :
    Stable puzzle newBoard := by
  apply solveToFixedPointWithFuel_stable
  · exact Nat.lt_succ_of_le (unknownCount_le_cells oldBoard)
  · exact hSolve

private theorem solveToFixedPointWithFuel_sound
    {puzzle : Puzzle rows cols}
    {fuel passes finalPasses : Nat}
    {oldBoard newBoard : Board rows cols}
    (hSolve : solveToFixedPointWithFuel puzzle fuel oldBoard passes =
      .ok (newBoard, finalPasses))
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    newBoard.Compatible solution := by
  induction fuel generalizing oldBoard newBoard passes finalPasses with
  | zero =>
      simp only [solveToFixedPointWithFuel, Except.ok.injEq, Prod.mk.injEq] at hSolve
      rw [← hSolve.1]
      exact hCompatible
  | succ fuel ih =>
      simp only [solveToFixedPointWithFuel] at hSolve
      cases hAll : solveAll puzzle oldBoard with
      | error target => simp [hAll] at hSolve
      | ok result =>
          simp only [hAll] at hSolve
          split at hSolve
          next _ =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hSolve
            rw [← hSolve.1]
            exact solveAll_sound hAll hSatisfies hCompatible
          next _ =>
            exact ih hSolve (solveAll_sound hAll hSatisfies hCompatible)

private theorem solveToFixedPointWithFuel_refines
    {puzzle : Puzzle rows cols}
    {fuel passes finalPasses : Nat}
    {oldBoard newBoard : Board rows cols}
    (hSolve : solveToFixedPointWithFuel puzzle fuel oldBoard passes =
      .ok (newBoard, finalPasses)) :
    newBoard.Refines oldBoard := by
  induction fuel generalizing oldBoard newBoard passes finalPasses with
  | zero =>
      simp only [solveToFixedPointWithFuel, Except.ok.injEq, Prod.mk.injEq] at hSolve
      rw [← hSolve.1]
      exact Board.Refines.refl oldBoard
  | succ fuel ih =>
      simp only [solveToFixedPointWithFuel] at hSolve
      cases hAll : solveAll puzzle oldBoard with
      | error target => simp [hAll] at hSolve
      | ok result =>
          simp only [hAll] at hSolve
          split at hSolve
          next _ =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hSolve
            rw [← hSolve.1]
            exact solveAll_refines hAll
          next _ =>
            exact Board.Refines.trans (ih hSolve) (solveAll_refines hAll)

/-- Repeated full passes preserve every puzzle solution whenever they succeed. -/
theorem solveToFixedPoint_sound
    {puzzle : Puzzle rows cols}
    {oldBoard newBoard : Board rows cols}
    {passes : Nat}
    (hSolve : solveToFixedPoint puzzle oldBoard = .ok (newBoard, passes))
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    newBoard.Compatible solution :=
  solveToFixedPointWithFuel_sound hSolve hSatisfies hCompatible

/-- Repeated full passes refine the input board whenever they succeed. -/
theorem solveToFixedPoint_refines
    {puzzle : Puzzle rows cols}
    {oldBoard newBoard : Board rows cols}
    {passes : Nat}
    (hSolve : solveToFixedPoint puzzle oldBoard = .ok (newBoard, passes)) :
    newBoard.Refines oldBoard :=
  solveToFixedPointWithFuel_refines hSolve

end LineSolver.BoardSolver

end Nonogram
