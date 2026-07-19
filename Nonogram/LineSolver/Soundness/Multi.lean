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

end LineSolver.Multi

end Nonogram
