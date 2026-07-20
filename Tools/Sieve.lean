import Nonogram.LineSolver.Sieve

namespace Nonogram.Tools.Sieve

open Nonogram
open Nonogram.LineSolver.Sieve

structure Config where
  rows : Nat := 5
  cols : Nat := 5
  density : Nat := 50
  startSeed : Nat := 0
  seeds : Nat := 100
  limit : Nat := 5
  classify : Bool := false
  reveal : Bool := false
  help : Bool := false

private def parseNat (option value : String) : Except String Nat :=
  match value.toNat? with
  | some number => .ok number
  | none => .error s!"{option} expects a natural number, got `{value}`"

def Config.parse (args : List String) : Except String Config := do
  let rec go : List String -> Config -> Except String Config
    | [], config => .ok config
    | "--rows" :: value :: rest, config => do
        go rest { config with rows := ← parseNat "--rows" value }
    | "--cols" :: value :: rest, config => do
        go rest { config with cols := ← parseNat "--cols" value }
    | "--density" :: value :: rest, config => do
        go rest { config with density := ← parseNat "--density" value }
    | "--start" :: value :: rest, config => do
        go rest { config with startSeed := ← parseNat "--start" value }
    | "--seeds" :: value :: rest, config => do
        go rest { config with seeds := ← parseNat "--seeds" value }
    | "--limit" :: value :: rest, config => do
        go rest { config with limit := ← parseNat "--limit" value }
    | "--classify" :: rest, config => go rest { config with classify := true }
    | "--reveal" :: rest, config => go rest { config with reveal := true }
    | "--help" :: rest, config => go rest { config with help := true }
    | "-h" :: rest, config => go rest { config with help := true }
    | "--" :: rest, config => go rest config
    | option :: _, _ => .error s!"unknown or incomplete option `{option}`"
  let config ← go args {}
  if config.help then return config
  unless 0 < config.rows && config.rows <= 12 do
    throw "--rows must be in the range 1..12"
  unless 0 < config.cols && config.cols <= 12 do
    throw "--cols must be in the range 1..12"
  unless 0 < config.density && config.density < 100 do
    throw "--density must be in the range 1..99"
  unless 0 < config.seeds do throw "--seeds must be positive"
  unless 0 < config.limit do throw "--limit must be positive"
  if config.classify && config.rows * config.cols > 36 then
    throw "--classify is limited to puzzles with at most 36 cells"
  return config

def usage : String :=
  "Usage: lake exe nonoSieve -- [options]\n\n" ++
  "Options:\n" ++
  "  --rows N       puzzle rows (default 5)\n" ++
  "  --cols N       puzzle columns (default 5)\n" ++
  "  --density N    black-cell percentage (default 50)\n" ++
  "  --start N      first seed to scan (default 0)\n" ++
  "  --seeds N      number of seeds to scan (default 100)\n" ++
  "  --limit N      stop after this many stalled cases (default 5)\n" ++
  "  --classify     count up to two global solutions\n" ++
  "  --reveal       print the generated solution\n" ++
  "  -h, --help     show this help"

private def printCase
    (index : Nat)
    (result : Case rows cols)
    (reveal : Bool) : IO Unit := do
  let classification :=
    match result.classification with
    | some value => s!", {value}"
    | none => ""
  IO.println (s!"\n[{index}] seed {result.seed}: {result.unknownCount}/{rows * cols} unknown " ++
    s!"after {result.passes} pass(es){classification}")
  IO.println s!"reproduce: lake exe nonogram -- --rows {rows} --cols {cols} --seed {result.seed}"
  IO.println "\nClues:"
  IO.println (puzzleSource result.generated.puzzle)
  IO.println "\nLine-solver fixed point:"
  IO.println (result.generated.puzzle.renderBoard result.board)
  if reveal then
    IO.println "\nGenerated solution:"
    IO.println (result.generated.puzzle.renderBoard (CLI.solutionBoard result.generated.solution))

def run (args : List String) : IO UInt32 := do
  let config ← match Config.parse args with
    | .ok config => pure config
    | .error message =>
        IO.eprintln s!"error: {message}\n\n{usage}"
        return 2
  if config.help then
    IO.println usage
    return 0
  IO.println (s!"Scanning {config.seeds} seed(s) from {config.startSeed} " ++
    s!"for stalled {config.rows} x {config.cols} puzzles...")
  let mut found := 0
  let mut scanned := 0
  for offset in List.range config.seeds do
    if found < config.limit then
      let seed := config.startSeed + offset
      let generated := CLI.generate config.rows config.cols config.density seed
      match analyze seed generated config.classify with
      | .error message =>
          IO.eprintln s!"error: {message}"
          return 1
      | .ok none => pure ()
      | .ok (some result) =>
          found := found + 1
          printCase found result config.reveal
      scanned := scanned + 1
  IO.println s!"\nScanned {scanned} seed(s); found {found} stalled puzzle(s)."
  return 0

end Nonogram.Tools.Sieve

def main (args : List String) : IO UInt32 :=
  Nonogram.Tools.Sieve.run args
