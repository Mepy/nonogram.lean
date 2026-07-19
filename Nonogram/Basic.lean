import Std

namespace Nonogram

/-- The information currently recorded in one square of the board. -/
inductive Cell where
  /-- Nothing has been deduced about this square yet. -/
  | unknown
  /-- This square is known to be black. -/
  | filled
  /-- This square is known not to be black. -/
  | crossed
  deriving BEq, DecidableEq, Inhabited

namespace Cell

/-- A compact symbol used by the board renderer. -/
def symbol : Cell -> String
  | .unknown => "?"
  | .filled => "■"
  | .crossed => "×"

instance : Repr Cell where
  reprPrec cell _ := Std.Format.text cell.symbol

instance : ToString Cell where
  toString := symbol

end Cell

/-- A finite line. Its length is part of its type. -/
abbrev Line (length : Nat) (alpha : Type) := Fin length -> alpha

namespace Line

/-- Enumerate a finite line in increasing index order. -/
def toList (line : Line length alpha) : List alpha :=
  List.ofFn line

end Line

/--
The current state of a `rows x cols` board.

Every coordinate is in bounds by construction.
-/
structure Board (rows cols : Nat) where
  get : Fin rows -> Fin cols -> Cell

namespace Board

/-- A board on which no square has been decided. -/
def unknown : Board rows cols where
  get := fun _ _ => .unknown

/-- Read one horizontal line. -/
def row (board : Board rows cols) (r : Fin rows) : Line cols Cell :=
  fun c => board.get r c

/-- Read one vertical line. -/
def col (board : Board rows cols) (c : Fin cols) : Line rows Cell :=
  fun r => board.get r c

/-- Replace one square, leaving every other square unchanged. -/
def set
    (board : Board rows cols)
    (targetRow : Fin rows)
    (targetCol : Fin cols)
    (value : Cell) : Board rows cols where
  get r c :=
    if r = targetRow ∧ c = targetCol then value else board.get r c

/-- Replace one complete horizontal line. -/
def replaceRow
    (board : Board rows cols)
    (target : Fin rows)
    (line : Line cols Cell) : Board rows cols where
  get r c := if r = target then line c else board.get r c

/-- Replace one complete vertical line. -/
def replaceCol
    (board : Board rows cols)
    (target : Fin cols)
    (line : Line rows Cell) : Board rows cols where
  get r c := if c = target then line r else board.get r c

private def renderLine (line : Line length Cell) : String :=
  String.intercalate " " ((Line.toList line).map Cell.symbol)

/-- Render a board row by row. -/
def render (board : Board rows cols) : String :=
  String.intercalate "\n" <|
    List.ofFn fun r => renderLine (board.row r)

instance : ToString (Board rows cols) where
  toString := render

instance : Repr (Board rows cols) where
  reprPrec board _ := Std.Format.text board.render

end Board

end Nonogram
