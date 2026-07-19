# nonogram-lean

A finite Nonogram model in Lean 4, including typed boards, clues, board rendering
with clues, solutions, puzzle validity, candidate states, and contracts for
deduction rules.

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
edit. `line row i` and `line col j` enumerate every candidate
compatible with that line's clue and current cells, then record the cells on
which all candidates agree. `gram` accepts only a complete board satisfying
every clue and then constructs the `Solution.Satisfies` proof.

```bash
lake build
lake exe Nonogram
```
