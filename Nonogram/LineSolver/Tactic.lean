import Lean
import Nonogram.LineSolver.Multi
import Nonogram.Tactic.Basic
import Nonogram.SolverStep

open Lean Elab Term Meta

namespace Nonogram

declare_syntax_cat nonogramStepLine

/-- One row or column group in a combined `line` command. -/
syntax ident num* : nonogramStepLine

/-- Select every row or column in one group of a combined `line` command. -/
syntax ident "*" : nonogramStepLine

/-- Process every row followed by every column once. -/
syntax "*" : nonogramStepLine

/-- Repeat `*` until a complete pass leaves the board unchanged. -/
syntax "**" : nonogramStepLine

/--
Process a sequence of row and column groups from left to right. For example,
`line row 1 2 col 3 row 4` lets each group use the board updated by the groups
before it. A group with no indices is a no-op. Directions are identifiers to
avoid reserving `row` and `col` as global Lean keywords.
-/
syntax (name := nonogramLineSolver) "line" nonogramStepLine* : nonogramStep

namespace LineSolver.Tactic

open LineSolver.Multi

/-- Elaborate line groups into the sound transcript operations they denote. -/
def elabLineSteps
    (groups : Array (TSyntax `nonogramStepLine)) :
    TermElabM (List (SolverStep rows cols)) := do
  let mut steps : List (SolverStep rows cols) := []
  for group in groups do
    match group with
    | `(nonogramStepLine| $direction:ident $indexStxs:num*) =>
        if direction.getId == `row then
          let rows ← indexStxs.mapM (Nonogram.Tactic.getCoordinate "row" rows)
          steps := steps ++ [.targets (rows.toList.map Target.row)]
        else if direction.getId == `col then
          let cols ← indexStxs.mapM (Nonogram.Tactic.getCoordinate "column" cols)
          steps := steps ++ [.targets (cols.toList.map Target.col)]
        else
          throwErrorAt direction "expected `row` or `col` after `line`"
    | `(nonogramStepLine| $direction:ident *) =>
        if direction.getId == `row then
          steps := steps ++ [.targets (allRows rows cols)]
        else if direction.getId == `col then
          steps := steps ++ [.targets (allCols rows cols)]
        else
          throwErrorAt direction "expected `row` or `col` after `line`"
    | `(nonogramStepLine| *) =>
        steps := steps ++ [.targets (allTargets rows cols)]
    | `(nonogramStepLine| **) =>
        steps := steps ++ [.fixedPoint]
    | _ => throwUnsupportedSyntax
  return steps

private def lineSolverReport (messages : Array String) : Option String :=
  if messages.isEmpty then none else some (String.intercalate "\n" messages.toList)

private def pushCompactLineReport
    (messages : Array String)
    (direction : String)
    (lines : List (Multi.SolvedTarget rows cols)) : Array String :=
  if lines.isEmpty then
    messages
  else
    let indices := lines.map fun solved => toString (solved.target.index + 1)
    let candidateCounts := lines.map fun solved => toString solved.candidateCount
    messages.push <| s!"line {direction} {String.intercalate ", " indices}: " ++
      s!"{String.intercalate ", " candidateCounts} candidate(s)"

private def noCandidateMessage : Target rows cols -> String
  | .row row =>
      s!"`line row {row.val + 1}` found no candidate; the current row contradicts its clue"
  | .col col =>
      s!"`line col {col.val + 1}` found no candidate; the current column contradicts its clue"

/-- Elaborate and execute the groups of one `line` command. -/
def elabLine
    (puzzle : Puzzle rows cols)
    (initialBoard : Board rows cols)
    (groups : Array (TSyntax `nonogramStepLine)) :
    TermElabM (Board rows cols × Option String) := do
  let mut board := initialBoard
  let mut messages := #[]
  for group in groups do
    match group with
    | `(nonogramStepLine| $direction:ident $indexStxs:num*) =>
        if direction.getId == `row then
          let rows ← indexStxs.mapM (Nonogram.Tactic.getCoordinate "row" rows)
          let targets := rows.toList.map Target.row
          match solveTargets puzzle board targets with
          | .error target => throwErrorAt group (noCandidateMessage target)
          | .ok result =>
              board := result.board
              messages := pushCompactLineReport messages "row" result.solved
        else if direction.getId == `col then
          let cols ← indexStxs.mapM (Nonogram.Tactic.getCoordinate "column" cols)
          let targets := cols.toList.map Target.col
          match solveTargets puzzle board targets with
          | .error target => throwErrorAt group (noCandidateMessage target)
          | .ok result =>
              board := result.board
              messages := pushCompactLineReport messages "col" result.solved
        else
          throwErrorAt direction "expected `row` or `col` after `line`"
    | `(nonogramStepLine| $direction:ident *) =>
        if direction.getId == `row then
          match solveTargets puzzle board (allRows rows cols) with
          | .error target => throwErrorAt group (noCandidateMessage target)
          | .ok result =>
              board := result.board
              messages := pushCompactLineReport messages "row" result.solved
        else if direction.getId == `col then
          match solveTargets puzzle board (allCols rows cols) with
          | .error target => throwErrorAt group (noCandidateMessage target)
          | .ok result =>
              board := result.board
              messages := pushCompactLineReport messages "col" result.solved
        else
          throwErrorAt direction "expected `row` or `col` after `line`"
    | `(nonogramStepLine| *) =>
        match solveAll puzzle board with
        | .error target => throwErrorAt group (noCandidateMessage target)
        | .ok result =>
            board := result.board
            messages := pushCompactLineReport messages "row" (result.solved.take rows)
            messages := pushCompactLineReport messages "col" (result.solved.drop rows)
    | `(nonogramStepLine| **) =>
        match solveToFixedPoint puzzle board with
        | .error target => throwErrorAt group (noCandidateMessage target)
        | .ok (newBoard, passes) =>
            board := newBoard
            messages := messages.push s!"line **: stabilized after {passes} pass(es)"
    | _ => throwUnsupportedSyntax
  return (board, lineSolverReport messages)

end LineSolver.Tactic

end Nonogram
