import Nonogram.Clue

namespace Nonogram

/-- The row and column clues of a finite Nonogram. -/
structure Puzzle (rows cols : Nat) where
  rowClues : Fin rows -> Clue
  colClues : Fin cols -> Clue

namespace Puzzle

/-- Every clue is positive and fits in its corresponding line. -/
def WellFormed (puzzle : Puzzle rows cols) : Prop :=
  And
    (forall r, Clue.WellFormed cols (puzzle.rowClues r))
    (forall c, Clue.WellFormed rows (puzzle.colClues c))

private def spaces (count : Nat) : String :=
  String.ofList (List.replicate count ' ')

private def repeatChar (count : Nat) (char : Char) : String :=
  String.ofList (List.replicate count char)

private def padLeft (width : Nat) (text : String) : String :=
  spaces (width - text.length) ++ text

private def maxStringWidth (texts : List String) : Nat :=
  texts.foldl (fun width text => Nat.max width text.length) 0

private def renderClueSection (clues : List Clue) : String :=
  String.intercalate "\n" (clues.map fun clue => "  " ++ clue.render)

/-- Render the row and column clues without a board. -/
def render (puzzle : Puzzle rows cols) : String :=
  let rowClues := List.ofFn puzzle.rowClues
  let colClues := List.ofFn puzzle.colClues
  "Rows:\n" ++ renderClueSection rowClues ++
    "\nColumns:\n" ++ renderClueSection colClues

/-- Render a current board with its row and column clues. -/
def renderBoard (puzzle : Puzzle rows cols) (board : Board rows cols) : String :=
  let rowClueTexts := List.ofFn fun r => (puzzle.rowClues r).render
  let colClues := List.ofFn puzzle.colClues
  let rowClueWidth := maxStringWidth rowClueTexts
  let clueHeight := colClues.foldl (fun height clue => Nat.max height clue.length) 0
  let cellWidth := colClues.foldl
    (fun width clue =>
      clue.foldl
        (fun width block => Nat.max width (toString block).length)
        width)
    1
  let paddedColClues := colClues.map fun clue =>
    List.replicate (clueHeight - clue.length) "" ++ clue.map toString
  let headerLines := List.range clueHeight |>.map fun level =>
    spaces rowClueWidth ++ " │ " ++
      String.intercalate " "
        (paddedColClues.map fun clue => padLeft cellWidth (clue.getD level ""))
  let boardWidth := if cols = 0 then 0 else cols * (cellWidth + 1) - 1
  let divider := repeatChar rowClueWidth '─' ++ "─┼─" ++ repeatChar boardWidth '─'
  let boardLines := List.ofFn fun r =>
    padLeft rowClueWidth (puzzle.rowClues r).render ++ " │ " ++
      String.intercalate " "
        ((Line.toList (board.row r)).map fun cell => padLeft cellWidth cell.symbol)
  String.intercalate "\n" (headerLines ++ divider :: boardLines)

instance : ToString (Puzzle rows cols) where
  toString := render

instance : Repr (Puzzle rows cols) where
  reprPrec puzzle _ := Std.Format.text puzzle.render

end Puzzle

/-- A complete black/white assignment; `true` means black. -/
abbrev Solution (rows cols : Nat) := Fin rows -> Fin cols -> Bool

namespace Solution

def row (solution : Solution rows cols) (r : Fin rows) : Line cols Bool :=
  fun c => solution r c

def col (solution : Solution rows cols) (c : Fin cols) : Line rows Bool :=
  fun r => solution r c

/-- A solution satisfies all row and column clues. -/
structure Satisfies
    (solution : Solution rows cols)
    (puzzle : Puzzle rows cols) : Prop where
  row : forall r, Line.Satisfies (puzzle.rowClues r) (solution.row r)
  col : forall c, Line.Satisfies (puzzle.colClues c) (solution.col c)

instance (clue : Clue) (line : Line length Bool) :
    Decidable (Line.Satisfies clue line) :=
  inferInstanceAs (Decidable (line.runs = clue))

instance (solution : Solution rows cols) (puzzle : Puzzle rows cols) :
    Decidable (solution.Satisfies puzzle) :=
  if hRow : forall r, Line.Satisfies (puzzle.rowClues r) (solution.row r) then
    if hCol : forall c, Line.Satisfies (puzzle.colClues c) (solution.col c) then
      isTrue ⟨hRow, hCol⟩
    else
      isFalse fun h => hCol h.col
  else
    isFalse fun h => hRow h.row

end Solution

namespace Puzzle

def Solvable (puzzle : Puzzle rows cols) : Prop :=
  exists solution : Solution rows cols, solution.Satisfies puzzle

def UniquelySolvable (puzzle : Puzzle rows cols) : Prop :=
  exists solution : Solution rows cols,
    And
      (solution.Satisfies puzzle)
      (forall other, other.Satisfies puzzle -> other = solution)

/-- A valid puzzle has well-formed clues and exactly one solution. -/
def Valid (puzzle : Puzzle rows cols) : Prop :=
  And puzzle.WellFormed puzzle.UniquelySolvable

end Puzzle

namespace Cell

/-- Current cell information does not contradict a completed cell. -/
def Compatible (cell : Cell) (solutionCell : Bool) : Prop :=
  match cell with
  | .unknown => True
  | .filled => solutionCell = true
  | .crossed => solutionCell = false

/-- `new` keeps all information already present in `old`. -/
def Refines (new old : Cell) : Prop :=
  match old with
  | .unknown => True
  | .filled => new = .filled
  | .crossed => new = .crossed

end Cell

namespace Board

/-- The board contains no information contradicting a complete solution. -/
structure Compatible
    (board : Board rows cols)
    (solution : Solution rows cols) : Prop where
  cell : forall r c, Cell.Compatible (board.get r c) (solution r c)

/-- The first board contains at least all information in the second board. -/
structure Refines
    (newBoard oldBoard : Board rows cols) : Prop where
  cell : forall r c, Cell.Refines (newBoard.get r c) (oldBoard.get r c)

end Board

/-- A complete solution still possible under the clues and current board. -/
def IsCandidate
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (solution : Solution rows cols) : Prop :=
  And (solution.Satisfies puzzle) (board.Compatible solution)

def Board.Consistent
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) : Prop :=
  exists solution : Solution rows cols, IsCandidate puzzle board solution

def ForcedFilled
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (r : Fin rows)
    (c : Fin cols) : Prop :=
  forall solution, IsCandidate puzzle board solution -> solution r c = true

def ForcedCrossed
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (r : Fin rows)
    (c : Fin cols) : Prop :=
  forall solution, IsCandidate puzzle board solution -> solution r c = false

end Nonogram
