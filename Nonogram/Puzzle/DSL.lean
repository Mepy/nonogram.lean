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

/-- A clue written as space-separated block lengths; `[]` is an empty clue. -/
syntax "[" num* "]" : nonogramClue

/-- A compact spelling for an empty clue. -/
syntax "-" : nonogramClue

/-- A single-block clue, with bare `0` reserved as an empty clue. -/
syntax num : nonogramClue

namespace SolutionRowParser

open Lean.Parser

private def isCellSymbol (char : Char) : Bool :=
  char == '#' || char == '■' || char == '_' || char == '.' || char == '×'

/-- Parse one unquoted row of a solution bitmap. -/
def row : Parser where
  fn := rawFn (takeWhile1Fn isCellSymbol "solution bitmap row") true
  info := {}

@[combinator_parenthesizer row]
def row.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter row]
def row.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

end SolutionRowParser

/-- Cell symbols registered for tokenization inside solution bitmaps. -/
declare_syntax_cat nonogramSolutionCell
syntax "#" : nonogramSolutionCell
syntax "■" : nonogramSolutionCell
syntax "_" : nonogramSolutionCell
syntax "." : nonogramSolutionCell
syntax "×" : nonogramSolutionCell

/-- One unquoted bitmap row in a `nonogram from solution` expression. -/
declare_syntax_cat nonogramSolutionRow
syntax SolutionRowParser.row : nonogramSolutionRow

namespace DSL

private structure ParsedClue where
  term : TSyntax `term
  blocks : Array (TSyntax `num)

private def parseClue (clue : TSyntax `nonogramClue) : MacroM ParsedClue := do
  match clue with
  | `(nonogramClue| -) =>
      return ⟨← `([]), #[]⟩
  | `(nonogramClue| $block:num) =>
      if block.getNat == 0 then
        return ⟨← `([]), #[]⟩
      else
        return ⟨← `([$block]), #[block]⟩
  | _ =>
      let blocks : Array (TSyntax `num) :=
        clue.raw[1].getArgs.map fun block => ⟨block⟩
      return ⟨← `([$blocks,*]), blocks⟩

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

private def expandClues
    (rows columns : Array (TSyntax `nonogramClue)) : MacroM (TSyntax `term) := do
  let mut rowTerms := #[]
  let mut rowIndex := 1
  for row in rows do
    rowTerms := rowTerms.push (← validateClue "row" rowIndex columns.size row)
    rowIndex := rowIndex + 1
  let mut columnTerms := #[]
  let mut columnIndex := 1
  for column in columns do
    columnTerms := columnTerms.push
      (← validateClue "column" columnIndex rows.size column)
    columnIndex := columnIndex + 1
  `(Puzzle.ofClueLists [$rowTerms,*] [$columnTerms,*])

private def solutionRowText (row : TSyntax `nonogramSolutionRow) : String :=
  row.raw[0].getAtomVal

private def expandSolution
    (rows : Array (TSyntax `nonogramSolutionRow)) : MacroM (TSyntax `term) := do
  let columnCount := match rows[0]? with
    | some row => (solutionRowText row).length
    | none => 0
  let mut cells := #[]
  let mut rowIndex := 1
  for row in rows do
    let text := solutionRowText row
    if text.length != columnCount then
      Macro.throwErrorAt row
        s!"solution row {rowIndex} has width {text.length}, expected {columnCount}"
    let mut columnIndex := 1
    for cell in text.toList do
      match cell with
      | '#' | '■' => cells := cells.push (← `(true))
      | '_' | '.' | '×' => cells := cells.push (← `(false))
      | _ =>
          Macro.throwErrorAt row
            s!"solution row {rowIndex}, column {columnIndex} contains '{cell}'; expected '#', '■', '_', '.', or '×'"
      columnIndex := columnIndex + 1
    rowIndex := rowIndex + 1
  let rowCount : TSyntax `term := ⟨Syntax.mkNatLit rows.size⟩
  let columnCountStx : TSyntax `term := ⟨Syntax.mkNatLit columnCount⟩
  `((show Solution $rowCount $columnCountStx from
      fun row column =>
        [$cells,*].getD (row.val * $columnCountStx + column.val) false))

end DSL

/--
Construct a puzzle from compact row and column clue sections. Each bracketed
group is one clue, and spaces separate its block lengths.
-/
syntax (name := nonogramFromClues) "nonogram" "from" "clues" ppLine
  "rows" ":" nonogramClue* ppLine
  "cols" ":" nonogramClue* : term

@[macro nonogramFromClues] def expandNonogramFromClues : Macro := fun stx => do
  let rowClues : Array (TSyntax `nonogramClue) :=
    stx[5].getArgs.map fun clue => ⟨clue⟩
  let columnClues : Array (TSyntax `nonogramClue) :=
    stx[8].getArgs.map fun clue => ⟨clue⟩
  DSL.expandClues rowClues columnClues

/--
Construct a puzzle from a rectangular, unquoted solution bitmap. `#` and `■`
are black cells; `_`, `.`, and `×` are white cells. The number and width of the
rows determine the dimensions.
-/
syntax (name := nonogramFromSolution) "nonogram" "from" "solution" ppLine
  nonogramSolutionRow* : term

@[macro nonogramFromSolution] def expandNonogramFromSolution : Macro := fun stx => do
  let bitmapRows : Array (TSyntax `nonogramSolutionRow) :=
    stx[3].getArgs.map fun row => ⟨row⟩
  let generatedSolution ← DSL.expandSolution bitmapRows
  `(Solution.toPuzzle $generatedSolution)

end Nonogram
