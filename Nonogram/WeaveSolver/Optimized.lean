import Nonogram.WeaveSolver.Spec

namespace Nonogram

namespace WeaveSolver.Optimized

/-- A constant-space summary of the candidates found by a search subtree. -/
inductive Summary (rows cols : Nat) where
  | none
  | one (board : Board rows cols)
  /-- `many extra` represents `extra + 2` candidates. -/
  | many (extra : Nat)

namespace Summary

/-- The exact number of candidates represented by a summary. -/
def candidateCount : Summary rows cols -> Nat
  | .none => 0
  | .one _ => 1
  | .many extra => extra + 2

/-- Combine summaries from two disjoint DFS subtrees. -/
def merge : Summary rows cols -> Summary rows cols -> Summary rows cols
  | .none, right => right
  | left, .none => left
  | .one _, .one _ => .many 0
  | .one _, .many extra => .many (extra + 1)
  | .many extra, .one _ => .many (extra + 1)
  | .many leftExtra, .many rightExtra => .many (leftExtra + rightExtra + 2)

/-- Reference summary of an already materialized candidate list. -/
def ofCandidates : List (Board rows cols) -> Summary rows cols
  | [] => .none
  | [board] => .one board
  | _ :: _ :: rest => .many rest.length

end Summary

/-- Count exhaustive assignments without constructing their boards as a list. -/
def assignmentCountRaw
    (board : Board rows cols) : List (Coordinate rows cols) -> Nat
  | [] => 1
  | coordinate :: coordinates =>
      match board.get coordinate.row coordinate.col with
      | .unknown =>
          assignmentCountRaw
              (board.set coordinate.row coordinate.col .filled) coordinates +
            assignmentCountRaw
              (board.set coordinate.row coordinate.col .crossed) coordinates
      | .filled | .crossed => assignmentCountRaw board coordinates

/-- Exact assignment count, with duplicate coordinates ignored. -/
def assignmentCount
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) : Nat :=
  assignmentCountRaw board coordinates.eraseDups

/--
Depth-first assignment search. Each leaf is propagated and immediately folded
into a constant-space summary, so neither assignments nor survivors are
materialized as an exponential-size list.
-/
def searchRaw
    (puzzle : Puzzle rows cols)
    (board : Board rows cols) :
    List (Coordinate rows cols) -> Summary rows cols
  | [] =>
      match Spec.propagate puzzle board with
      | none => .none
      | some solved => .one solved
  | coordinate :: coordinates =>
      match board.get coordinate.row coordinate.col with
      | .unknown =>
          Summary.merge
            (searchRaw puzzle
              (board.set coordinate.row coordinate.col .filled) coordinates)
            (searchRaw puzzle
              (board.set coordinate.row coordinate.col .crossed) coordinates)
      | .filled | .crossed => searchRaw puzzle board coordinates

/-- Run the streaming search after normalizing duplicate coordinates. -/
def search
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) : Summary rows cols :=
  searchRaw puzzle board coordinates.eraseDups

/-- Streaming DFS implementation of weave. -/
def solve
    (puzzle : Puzzle rows cols)
    (board : Board rows cols)
    (coordinates : List (Coordinate rows cols)) :
    Except Unit (Result rows cols) :=
  let attemptedCount := assignmentCount board coordinates
  match search puzzle board coordinates with
  | .none => .error ()
  | .one candidate => .ok ⟨candidate, 1, attemptedCount, true⟩
  | .many extra => .ok ⟨board, extra + 2, attemptedCount, false⟩

end WeaveSolver.Optimized

end Nonogram
