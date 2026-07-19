import Nonogram.LineSolver.Single

/-!
Run with `lake exe NonogramBench`. Timings are informational and deliberately
have no fixed pass/fail threshold; candidate-count disagreement is an error.
-/

namespace Nonogram.Benchmarks.LineSolver

open Nonogram

structure BenchmarkCase where
  name : String
  width : Nat
  clue : Clue
  known : Line width Cell
  iterations : Nat

private def unknownCase : BenchmarkCase where
  name := "unconstrained"
  width := 20
  clue := List.replicate 6 1
  known := fun _ => .unknown
  iterations := 10

private def partialCase : BenchmarkCase where
  name := "partially constrained"
  width := 20
  clue := List.replicate 6 1
  known := fun index =>
    if index.val = 0 || index.val = 2 then
      .filled
    else if index.val = 1 then
      .crossed
    else
      .unknown
  iterations := 10

private def solvedCase : BenchmarkCase where
  name := "fully constrained"
  width := 20
  clue := List.replicate 6 1
  known := fun index =>
    if index.val <= 10 && index.val % 2 = 0 then .filled else .crossed
  iterations := 10

private def measure
    (iterations : Nat)
    (compute : Unit -> List (Line length Bool)) : IO (Nat × Nat) := do
  let start <- IO.monoNanosNow
  let mut totalCandidates := 0
  for _ in List.range iterations do
    totalCandidates := totalCandidates + (compute ()).length
  let finish <- IO.monoNanosNow
  return (totalCandidates / iterations, finish - start)

private def formatDuration (nanos iterations : Nat) : String :=
  let average := nanos / iterations
  s!"{average / 1000} us avg, {nanos / 1000000} ms total"

private def runCase (benchmark : BenchmarkCase) : IO Unit := do
  let (placementCount, placementTime) <- measure benchmark.iterations fun _ =>
    Nonogram.LineSolver.Single.Placement.candidates benchmark.clue benchmark.known
  let (prunedCount, prunedTime) <- measure benchmark.iterations fun _ =>
    Nonogram.LineSolver.Single.Pruned.candidates benchmark.clue benchmark.known
  if placementCount != prunedCount then
    throw <| IO.userError <|
      s!"{benchmark.name}: candidate count mismatch: " ++
        s!"Placement={placementCount}, Pruned={prunedCount}"
  IO.println benchmark.name
  IO.println s!"  candidates: {placementCount}"
  IO.println s!"  Placement: {formatDuration placementTime benchmark.iterations}"
  IO.println s!"  Pruned:    {formatDuration prunedTime benchmark.iterations}"

def run : IO Unit := do
  IO.println "Single-line candidate generation benchmark"
  IO.println "width: 20, clue: [1, 1, 1, 1, 1, 1]"
  for benchmark in [unknownCase, partialCase, solvedCase] do
    runCase benchmark

end Nonogram.Benchmarks.LineSolver

def main : IO Unit :=
  Nonogram.Benchmarks.LineSolver.run
