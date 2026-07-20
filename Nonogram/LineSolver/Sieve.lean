import Nonogram.CLI

namespace Nonogram
namespace LineSolver.Sieve

open LineSolver.Multi

/-- Whether a stalled puzzle has one or multiple complete solutions. -/
inductive Classification where
  | unique
  | multiple
  deriving BEq, DecidableEq, Repr

instance : ToString Classification where
  toString
    | .unique => "unique"
    | .multiple => "multiple"

/-- A generated puzzle on which line solving reaches an incomplete fixed point. -/
structure Case (rows cols : Nat) where
  seed : Nat
  generated : CLI.Generated rows cols
  board : Board rows cols
  passes : Nat
  unknownCount : Nat
  classification : Option Classification

private def completedLine (candidate : Line length Bool) : Line length Cell :=
  fun index => if candidate index then .filled else .crossed

private def columnsPossible
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) : Bool :=
  (List.ofFn fun column =>
    match LineSolver.solve (puzzle.colClues column) (board.col column) with
    | some _ => true
    | none => false).all id

/-- Count complete solutions, stopping once `cap` solutions have been found. -/
partial def countSolutionsUpTo
    (puzzle : Puzzle rows cols)
    (cap : Nat)
    (rowIndex : Nat := 0)
    (board : Board rows cols := Board.unknown) : Nat :=
  if cap == 0 then
    0
  else if hRow : rowIndex < rows then
    let row : Fin rows := ⟨rowIndex, hRow⟩
    let candidates := LineSolver.candidates (puzzle.rowClues row) (board.row row)
    let (_, count) := candidates.foldl (fun (remaining, count) candidate =>
      if remaining == 0 then
        (0, count)
      else
        let nextBoard := board.replaceRow row (completedLine candidate)
        if columnsPossible puzzle nextBoard then
          let found := countSolutionsUpTo puzzle remaining (rowIndex + 1) nextBoard
          (remaining - found, count + found)
        else
          (remaining, count)) (cap, 0)
    count
  else
    1

private def classify (puzzle : Puzzle rows cols) : Classification :=
  if countSolutionsUpTo puzzle 2 == 1 then .unique else .multiple

/-- Analyze one generated puzzle, returning `none` when line solving completes it. -/
def analyze
    (seed : Nat)
    (generated : CLI.Generated rows cols)
    (withClassification : Bool) : Except String (Option (Case rows cols)) :=
  match solveToFixedPoint generated.puzzle Board.unknown with
  | .error _ => .error s!"seed {seed}: line solver found a contradiction"
  | .ok (board, passes) =>
      let unknownCount := rows * cols - CLI.decidedCount board
      if unknownCount == 0 then
        .ok none
      else
        let classification :=
          if withClassification then some (classify generated.puzzle) else none
        .ok (some ⟨seed, generated, board, passes, unknownCount, classification⟩)

private def clueSource : Clue -> String
  | [] => "[]"
  | [block] => toString block
  | blocks => "[" ++ String.intercalate " " (blocks.map toString) ++ "]"

/-- Render a puzzle in the source syntax accepted by the clue DSL. -/
def puzzleSource (puzzle : Puzzle rows cols) : String :=
  let rowClues := List.ofFn puzzle.rowClues |>.map clueSource
  let colClues := List.ofFn puzzle.colClues |>.map clueSource
  s!"nonogram from clues\n" ++
    "  rows: " ++ String.intercalate " " rowClues ++ "\n" ++
    "  cols: " ++ String.intercalate " " colClues

end LineSolver.Sieve
end Nonogram
