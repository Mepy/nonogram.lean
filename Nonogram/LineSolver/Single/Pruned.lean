import Nonogram.LineSolver.Single.Internal

namespace Nonogram
namespace LineSolver.Single.Pruned

open LineSolver.Single.Internal

namespace Internal

def white (length : Nat) : List Bool :=
  List.replicate length false

def black (length : Nat) : List Bool :=
  List.replicate length true

/-- Check two equally positioned list segments for cell compatibility. -/
def compatibleCells : List Cell -> List Bool -> Bool
  | [], [] => true
  | known :: knownTail, candidate :: candidateTail =>
      compatibleCell known candidate && compatibleCells knownTail candidateTail
  | _, _ => false

end Internal

open Internal

/--
Generate clue placements while discarding a branch as soon as its newly
placed prefix contradicts a known cell.
-/
def placements (known : List Cell) : Clue -> List (List Bool)
  | [] =>
      let candidate := white known.length
      if compatibleCells known candidate then [candidate] else []
  | block :: rest =>
      if block = 0 then
        []
      else
        match rest with
        | [] =>
            if block <= known.length then
              List.range (known.length - block + 1) |>.filterMap fun leading =>
                let candidate :=
                  white leading ++ black block ++
                    white (known.length - leading - block)
                if compatibleCells known candidate then some candidate else none
            else
              []
        | _ :: _ =>
            let needed := block + 1 + Clue.requiredLength rest
            if needed <= known.length then
              List.range (known.length - needed + 1) |>.flatMap fun leading =>
                let placed := white leading ++ black block ++ [false]
                if compatibleCells (known.take placed.length) placed then
                  (placements (known.drop placed.length) rest).map (placed ++ ·)
                else
                  []
            else
              []

/-- Candidates generated with compatibility pruning during block placement. -/
def candidates (clue : Clue) (line : Line length Cell) : List (Line length Bool) :=
  (placements line.toList clue).eraseDups.map ofList

/-- Analyze one line using compatibility-pruned placement generation. -/
def solve (clue : Clue) (line : Line length Cell) : Option (Result length) :=
  let candidates := candidates clue line
  if candidates.isEmpty then
    none
  else
    some {
      candidateCount := candidates.length
      line := intersect candidates
    }

end LineSolver.Single.Pruned
end Nonogram
