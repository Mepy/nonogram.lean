import Lean

open Lean Elab Term

namespace Nonogram

/-- One command in a `nono` proof block. -/
declare_syntax_cat nonogramStep

namespace Tactic

/-- Parse a one-based coordinate and check it against a concrete bound. -/
def getCoordinate
    (label : String)
    (bound : Nat)
    (stx : TSyntax `num) : TermElabM (Fin bound) := do
  let value := stx.getNat
  if value == 0 then
    throwErrorAt stx "Nonogram coordinates are 1-based; expected a positive number"
  let index := value - 1
  if h : index < bound then
    return ⟨index, h⟩
  else
    throwErrorAt stx "{label} {value} is outside the range 1..{bound}"

end Tactic

end Nonogram
