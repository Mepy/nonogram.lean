import Nonogram.Semantics

namespace Nonogram

namespace LineSolver

/-- The observable result of analyzing one finite line. -/
structure Result (length : Nat) where
  candidateCount : Nat
  line : Line length Cell

namespace Spec

/-- A completed Boolean line satisfies the clue and agrees with all known cells. -/
def Candidate
    (clue : Clue)
    (known : Line length Cell)
    (candidate : Line length Bool) : Prop :=
  And (Line.Satisfies clue candidate) (known.Compatible candidate)

/-- A cell can have `value` in at least one semantic candidate. -/
def CanBe
    (clue : Clue)
    (known : Line length Cell)
    (index : Fin length)
    (value : Bool) : Prop :=
  exists candidate, Candidate clue known candidate ∧ candidate index = value

/-- A duplicate-free list contains exactly all semantic candidates. -/
def Enumerates
    (clue : Clue)
    (known : Line length Cell)
    (items : List (Line length Bool)) : Prop :=
  And items.Nodup (forall candidate, candidate ∈ items ↔ Candidate clue known candidate)

/-- `count` is the cardinality of the semantic candidate set. -/
def HasCandidateCount
    (clue : Clue)
    (known : Line length Cell)
    (count : Nat) : Prop :=
  exists items, Enumerates clue known items ∧ items.length = count

/-- A reported cell records exactly which Boolean values remain possible. -/
def ExactCell
    (clue : Clue)
    (known : Line length Cell)
    (index : Fin length) : Cell -> Prop
  | .unknown => And (CanBe clue known index false) (CanBe clue known index true)
  | .filled => And (CanBe clue known index true) (Not (CanBe clue known index false))
  | .crossed => And (CanBe clue known index false) (Not (CanBe clue known index true))

/-- Every reported cell exactly summarizes all semantic candidates. -/
def ExactLine
    (clue : Clue)
    (known inferred : Line length Cell) : Prop :=
  forall index, ExactCell clue known index (inferred index)

/-- A successful result has the exact positive candidate count and exact cell summary. -/
def ExactResult
    (clue : Clue)
    (known : Line length Cell)
    (result : Result length) : Prop :=
  And
    (HasCandidateCount clue known result.candidateCount)
    (And (0 < result.candidateCount) (ExactLine clue known result.line))

/--
The complete behavioral specification of a single-line solver. `none` means
there are exactly zero candidates; `some` returns their exact count and cellwise
intersection.
-/
def ExactOutcome
    (clue : Clue)
    (known : Line length Cell) : Option (Result length) -> Prop
  | none => HasCandidateCount clue known 0
  | some result => ExactResult clue known result

/-- The exact summary of one cell is unique. -/
theorem exactCell_unique
    {clue : Clue}
    {known : Line length Cell}
    {index : Fin length}
    {left right : Cell}
    (hLeft : ExactCell clue known index left)
    (hRight : ExactCell clue known index right) :
    left = right := by
  cases left <;> cases right <;> simp_all [ExactCell]

/-- The exact inferred line is unique. -/
theorem exactLine_unique
    {clue : Clue}
    {known left right : Line length Cell}
    (hLeft : ExactLine clue known left)
    (hRight : ExactLine clue known right) :
    left = right := by
  funext index
  exact exactCell_unique (hLeft index) (hRight index)

end Spec

end LineSolver

end Nonogram
