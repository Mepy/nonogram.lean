# nonogram-lean

A finite Nonogram model in Lean 4, including typed boards, clues, board rendering
with clues, solutions, puzzle validity, candidate states, and contracts for
deduction rules.

Define a puzzle from literal row and column clues with `nonogram from clues`.
The number of entries in each section determines the dimensions, so the
annotation below is optional. A bare positive number is a single-block clue;
use `[1 1]` for multiple blocks. `[]`, `-`, and bare `0` all mean an empty clue:

```lean
def crossPuzzle : Puzzle 5 5 := nonogram from clues
  rows: 1 1 5 1 1
  cols: 1 1 5 1 1
```

Literal clues are checked at compile time: every block must be positive and
each clue must fit its row or column. For computed inputs,
`Puzzle.ofClueLists rows columns` constructs a puzzle whose dimensions are the
two list lengths.

A completed bitmap can generate both sets of clues directly. Rows need no
quotes or commas; `#` and `■` are black, while `_`, `.`, and `×` are white:

```lean
def crossPuzzle : Puzzle 5 5 := nonogram from solution
  __#__
  __#__
  #####
  __#__
  __#__
```

For an existing `solution : Solution rows cols`, `solution.rowClue r` and
`solution.colClue c` derive individual clues, and `solution.toPuzzle` derives
the complete puzzle. The solution satisfies that generated puzzle by
`solution.satisfies_toPuzzle`.

Run the CLI to generate a reproducible random solution, derive its clues, and
solve it with the same line solver used by the tactics:

```bash
lake exe Nonogram -- --rows 5 --cols 5 --seed 42
```

Press Enter for the next productive row or column, or enter tactic-like
commands such as `line row 1 3 col 2`, `line *`, `line **`, `fill 2 3`, and
`gram`. Each seed maps directly to one random solution; generation does not
filter puzzles according to what the current line solver can recover. The seed
is printed so the puzzle can be reproduced.

Session directives use a `#` prefix. `#new` starts another game with the next
seed, while `#new 1729` uses an explicit seed. Successful `fill`, `cross`,
`clear`, and `line` commands are recorded as the user's solving transcript.
Once the current board is complete and satisfies the clues, `#export` prints
standalone Lean source containing the puzzle as `nonogram from clues` and that
transcript as a replayable `nono` proof:

```text
nono> #new 42
nono> line row 2 col 1
nono> #export
```

Before exporting, the CLI replays the recorded transcript from an unknown board
and verifies that it reproduces the current solution. `#new` clears both the
board and transcript. `#show`, `#reveal`, `#help`, and `#quit` provide the
remaining session controls.

Use `--auto` to apply productive line deductions until they solve the puzzle or
reach a fixed point, and `--reveal` to show the generated solution afterward:

```bash
lake exe Nonogram -- --seed 42 --auto --reveal
```

Solve a concrete puzzle as a theorem with the `nono` term elaborator:

```lean
def diagonal : Puzzle 2 2 where
  rowClues _ := [1]
  colClues _ := [1]

theorem diagonal_solvable : diagonal.Solvable := nono
  fill 1 1
  cross 1 2
  cross 2 1
  fill 2 2
  gram
```

The theorem type `diagonal.Solvable` contains the concrete puzzle value, so all
row and column clues are fixed before `nono` starts.

`fill`, `cross`, and `clear` use 1-based row and column coordinates. Lean's
InfoView shows the current `Board` with its clues at `nono` and after every
edit. `line row i ...` and `line col j ...` enumerate every candidate
compatible with each line's clue and current cells, then record the cells on
which all candidates agree. Row and column groups can be chained in one command,
as in `line row 1 2 3 col 2 row 2`; groups are processed from left to right on
the updated board. A group with no indices is a no-op, while `row *` and `col *`
select every line in that direction. A bare `line` is also a no-op; `line *`
processes every row followed by every column, and `line **` repeats that pass
until the board stops changing. `*` and `**` are line groups too, so they can be
mixed with row and column groups and are evaluated from left to right. Each
InfoView panel shows its tactic report above the updated board. `gram` accepts
only a complete board satisfying every clue and then constructs the
`Solution.Satisfies` proof.

Commands may be separated by line breaks, semicolons, or both:

```lean
example : diagonal.Solvable := nono;
  line **;
  gram;
```

```bash
lake build
lake exe Nonogram
```
