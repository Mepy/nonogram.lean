import Nonogram.LineSolver.Single.Internal

namespace Nonogram

namespace LineSolver.Single.Placement

open LineSolver.Single.Internal

namespace Internal

def white (length : Nat) : List Bool :=
  List.replicate length false

def black (length : Nat) : List Bool :=
  List.replicate length true

end Internal

open Internal

/--
Generate only Boolean lists whose black blocks have the requested lengths.
Malformed zero-sized blocks and clues that do not fit produce no placements.
-/
def rawPlacements (length : Nat) : Clue -> List (List Bool)
  | [] => [white length]
  | block :: rest =>
      if block = 0 then
        []
      else
        match rest with
        | [] =>
            if block <= length then
              List.range (length - block + 1) |>.map fun leading =>
                white leading ++ black block ++ white (length - leading - block)
            else
              []
        | _ :: _ =>
            let needed := block + 1 + Clue.requiredLength rest
            if needed <= length then
              List.range (length - needed + 1) |>.flatMap fun leading =>
                let suffixLength := length - leading - block - 1
                (rawPlacements suffixLength rest).map fun suffix =>
                  white leading ++ black block ++ false :: suffix
            else
              []

/-- Clue-directed placements that also agree with all currently known cells. -/
def candidates (clue : Clue) (line : Line length Cell) : List (Line length Bool) :=
  (rawPlacements length clue).eraseDups.map ofList |>.filter fun candidate =>
    compatible line candidate

/-- Analyze one line using clue-directed placement generation. -/
def solve (clue : Clue) (line : Line length Cell) : Option (Result length) :=
  let candidates := candidates clue line
  if candidates.isEmpty then
    none
  else
    some {
      candidateCount := candidates.length
      line := intersect candidates
    }

end LineSolver.Single.Placement

end Nonogram
