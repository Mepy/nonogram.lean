import Lean
import Nonogram.Spec

/-! Literal and programmatic constructors for `Puzzle`. -/

open Lean

namespace Nonogram

namespace Puzzle

/--
Build a puzzle from row and column clue lists, with both dimensions inferred
from the list lengths.
-/
def ofClueLists
    (rows : List Clue)
    (columns : List Clue) : Puzzle rows.length columns.length where
  rowClues := rows.get
  colClues := columns.get

@[simp] theorem ofClueLists_rowClues
    (rows : List Clue)
    (columns : List Clue)
    (row : Fin rows.length) :
    (ofClueLists rows columns).rowClues row = rows.get row := rfl

@[simp] theorem ofClueLists_colClues
    (rows : List Clue)
    (columns : List Clue)
    (column : Fin columns.length) :
    (ofClueLists rows columns).colClues column = columns.get column := rfl

end Puzzle

/-- One literal clue in a `nonogram` puzzle expression. -/
declare_syntax_cat nonogramClue

/-- A clue written as its comma-separated block lengths. -/
syntax "[" num,* "]" : nonogramClue

/-- A compact spelling for an empty clue. -/
syntax "-" : nonogramClue

namespace DSL

private structure ParsedClue where
  term : TSyntax `term
  blocks : Array (TSyntax `num)

private def parseClue (clue : TSyntax `nonogramClue) : MacroM ParsedClue := do
  match clue with
  | `(nonogramClue| -) =>
      return ⟨← `([]), #[]⟩
  | `(nonogramClue| [$blocks:num,*]) =>
      return ⟨← `([$blocks,*]), blocks⟩
  | _ => Macro.throwUnsupported

private def validateClue
    (kind : String)
    (index lineLength : Nat)
    (clue : TSyntax `nonogramClue) : MacroM (TSyntax `term) := do
  let parsed ← parseClue clue
  for block in parsed.blocks do
    if block.getNat == 0 then
      Macro.throwErrorAt block
        s!"{kind} clue {index} contains a zero-length block; block lengths must be positive"
  let requiredLength := Clue.requiredLength (parsed.blocks.toList.map (·.getNat))
  if requiredLength > lineLength then
    Macro.throwErrorAt clue
      s!"{kind} clue {index} requires at least {requiredLength} cells, but the puzzle has {lineLength}"
  return parsed.term

end DSL

/--
Construct a puzzle from literal row and column clues. The number of clues in
each section determines the dimensions, and malformed clues are rejected while
the expression is elaborated.
-/
macro (name := nonogramLiteral) "nonogram" "{" ppLine
    "rows" ":" "[" rows:nonogramClue,* "]" "," ppLine
    "columns" ":" "[" columns:nonogramClue,* "]" ppLine
    "}" : term => do
    let rows := rows.getElems
    let columns := columns.getElems
    let mut rowTerms := #[]
    let mut rowIndex := 1
    for row in rows do
      rowTerms := rowTerms.push (← DSL.validateClue "row" rowIndex columns.size row)
      rowIndex := rowIndex + 1
    let mut columnTerms := #[]
    let mut columnIndex := 1
    for column in columns do
      columnTerms := columnTerms.push
        (← DSL.validateClue "column" columnIndex rows.size column)
      columnIndex := columnIndex + 1
    `(Puzzle.ofClueLists [$rowTerms,*] [$columnTerms,*])

end Nonogram
