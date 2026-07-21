import Nonogram.LineSolver.Multi
import Nonogram.LineSolver.Soundness.Single

namespace Nonogram

namespace LineSolver.Multi

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

private theorem solve_exists_of_candidate
    {clue : Clue}
    {line : Line length Cell}
    {candidate : Line length Bool}
    (hSatisfies : Line.Satisfies clue candidate)
    (hCompatible : line.Compatible candidate) :
    exists result, LineSolver.solve clue line = some result := by
  cases hSolve : LineSolver.solve clue line with
  | some result => exact ⟨result, rfl⟩
  | none =>
      have hExact := LineSolver.solve_exact clue line
      rw [hSolve] at hExact
      rcases hExact with ⟨items, hEnumerates, hLength⟩
      have hMem := (hEnumerates.2 candidate).mpr ⟨hSatisfies, hCompatible⟩
      have hEmpty : items = [] := List.eq_nil_of_length_eq_zero hLength
      rw [hEmpty] at hMem
      simp at hMem

/--
If a complete puzzle solution is compatible with the input board, solving one
target cannot report a contradiction and preserves that solution.
-/
theorem solveTarget_exists_sound
    (puzzle : Puzzle rows cols)
    (oldBoard : Board rows cols)
    (target : Target rows cols)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    exists newBoard solved,
      solveTarget puzzle oldBoard target = some (newBoard, solved) ∧
        newBoard.Compatible solution := by
  cases target with
  | row row =>
      obtain ⟨result, hLine⟩ := solve_exists_of_candidate
        (hSatisfies.row row) (fun col => hCompatible.cell row col)
      change LineSolver.solve (puzzle.rowClues row) (oldBoard.row row) =
        some result at hLine
      let newBoard := oldBoard.replaceRow row result.line
      let solved : SolvedTarget rows cols :=
        ⟨Target.row row, result.candidateCount⟩
      have hTarget :
          solveTarget puzzle oldBoard (.row row) = some (newBoard, solved) := by
        simp only [solveTarget, hLine, newBoard, solved]
      exact ⟨newBoard, solved, hTarget,
        solveTarget_sound hTarget hSatisfies hCompatible⟩
  | col col =>
      obtain ⟨result, hLine⟩ := solve_exists_of_candidate
        (hSatisfies.col col) (fun row => hCompatible.cell row col)
      change LineSolver.solve (puzzle.colClues col) (oldBoard.col col) =
        some result at hLine
      let newBoard := oldBoard.replaceCol col result.line
      let solved : SolvedTarget rows cols :=
        ⟨Target.col col, result.candidateCount⟩
      have hTarget :
          solveTarget puzzle oldBoard (.col col) = some (newBoard, solved) := by
        simp only [solveTarget, hLine, newBoard, solved]
      exact ⟨newBoard, solved, hTarget,
        solveTarget_sound hTarget hSatisfies hCompatible⟩

/--
Any finite target sequence succeeds when a compatible complete puzzle solution
exists, and its result remains compatible with that solution.
-/
theorem solveTargets_exists_sound
    (puzzle : Puzzle rows cols)
    (oldBoard : Board rows cols)
    (targets : List (Target rows cols))
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    exists result,
      solveTargets puzzle oldBoard targets = .ok result ∧
        result.board.Compatible solution := by
  induction targets generalizing oldBoard with
  | nil => exact ⟨⟨oldBoard, []⟩, rfl, hCompatible⟩
  | cons target targets ih =>
      obtain ⟨nextBoard, solved, hTarget, hNextCompatible⟩ :=
        solveTarget_exists_sound puzzle oldBoard target hSatisfies hCompatible
      obtain ⟨rest, hRest, hFinalCompatible⟩ :=
        ih nextBoard hNextCompatible
      refine ⟨⟨rest.board, solved :: rest.solved⟩, ?_, hFinalCompatible⟩
      simp [solveTargets, hTarget, hRest]

/-- A full row-and-column pass succeeds whenever a compatible solution exists. -/
theorem solveAll_exists_sound
    (puzzle : Puzzle rows cols)
    (oldBoard : Board rows cols)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    exists result,
      solveAll puzzle oldBoard = .ok result ∧ result.board.Compatible solution :=
  solveTargets_exists_sound puzzle oldBoard (allTargets rows cols)
    hSatisfies hCompatible

private theorem solveToFixedPointWithFuel_exists_sound
    (puzzle : Puzzle rows cols)
    (fuel : Nat)
    (oldBoard : Board rows cols)
    (passes : Nat)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    exists newBoard finalPasses,
      solveToFixedPointWithFuel puzzle fuel oldBoard passes =
        .ok (newBoard, finalPasses) ∧
      newBoard.Compatible solution := by
  induction fuel generalizing oldBoard passes with
  | zero => exact ⟨oldBoard, passes, rfl, hCompatible⟩
  | succ fuel ih =>
      obtain ⟨result, hAll, hNextCompatible⟩ :=
        solveAll_exists_sound puzzle oldBoard hSatisfies hCompatible
      by_cases hEqual : boardsEqual result.board oldBoard = true
      · refine ⟨result.board, passes + 1, ?_, hNextCompatible⟩
        simp [solveToFixedPointWithFuel, hAll, hEqual]
      · have hFalse : boardsEqual result.board oldBoard = false :=
          Bool.eq_false_iff.mpr hEqual
        obtain ⟨newBoard, finalPasses, hRest, hFinalCompatible⟩ :=
          ih result.board (passes + 1) hNextCompatible
        refine ⟨newBoard, finalPasses, ?_, hFinalCompatible⟩
        simp [solveToFixedPointWithFuel, hAll, hFalse, hRest]

/--
Repeated full-board propagation cannot report a contradiction while a complete
puzzle solution remains compatible, and its result preserves that solution.
-/
theorem solveToFixedPoint_exists_sound
    (puzzle : Puzzle rows cols)
    (oldBoard : Board rows cols)
    {solution : Solution rows cols}
    (hSatisfies : solution.Satisfies puzzle)
    (hCompatible : oldBoard.Compatible solution) :
    exists newBoard passes,
      solveToFixedPoint puzzle oldBoard = .ok (newBoard, passes) ∧
        newBoard.Compatible solution :=
  solveToFixedPointWithFuel_exists_sound puzzle (rows * cols + 1) oldBoard 0
    hSatisfies hCompatible

end LineSolver.Multi

end Nonogram
