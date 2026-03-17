# Analysis of Boolean Functions — Agent Guide

Lean 4 formalization of *Analysis of Boolean Functions* by Ryan O'Donnell, built on Mathlib.

## Build

```bash
lake build
```

Verify the build passes with no errors or warnings before considering a change complete.

## Project Workflow

### Chapter-by-chapter PRs

We formalize one chapter at a time, in order. Each chapter gets its own PR.
No work on chapter N+1 begins until the PR for chapter N is approved and merged.

### Module structure

For each topic module `X`, create three files:

- **`X/Defs.lean`** — All definitions, structures, and type classes. This is the
  public API that downstream code imports.
- **`X/Internal.lean`** — Proof internals: helper lemmas, technical machinery,
  and intermediate results. Imports `X/Defs`. This file exists so that the
  main module stays clean and reviewable.
- **`X.lean`** — The main theorems and propositions from the book. Imports
  `X/Internal` (which transitively brings in `X/Defs`). This is what
  reviewers focus on alongside `X/Defs`.

**Review scope**: Only `X.lean` and `X/Defs.lean` need careful review.
`X/Internal.lean` contains proof plumbing that is validated by the type checker.

### Book chapter → module mapping

Each chapter maps to a namespace under `BooleanAnalysis`:

| Chapter | Module name |
|---------|------------|
| 1. Boolean functions and the Fourier expansion | `BooleanAnalysis.FourierExpansion` |
| 2. Basic concepts and social choice | `BooleanAnalysis.SocialChoice` |
| 3. Spectral structure and learning | `BooleanAnalysis.SpectralStructure` |
| 4. DNF formulas and small-depth circuits | `BooleanAnalysis.DNFFormulas` |
| 5. Majority and threshold functions | `BooleanAnalysis.Majority` |
| 6. Pseudorandomness and F₂-polynomials | `BooleanAnalysis.Pseudorandomness` |
| 7. Property testing, PCPPs, and CSPs | `BooleanAnalysis.PropertyTesting` |
| 8. Generalized domains | `BooleanAnalysis.GeneralizedDomains` |
| 9. Basics of hypercontractivity | `BooleanAnalysis.Hypercontractivity` |
| 10. Advanced hypercontractivity | `BooleanAnalysis.AdvancedHypercontractivity` |
| 11. Gaussian space and Invariance Principles | `BooleanAnalysis.GaussianSpace` |

### PR conventions

- Branch name: `chapter-N` (e.g., `chapter-1`)
- PR title: `Chapter N: <chapter title>`
- PR body: list the main definitions and theorems formalized
- Ensure CI passes before requesting review

### What to formalize

Focus on definitions, propositions, theorems, and lemmas from the book.
Skip exercises unless they are referenced by later proofs. Skip computational
examples that don't yield reusable lemmas.

## Proof Development Workflow

### Stay grounded in the proof state

Use Lean MCP tools constantly — never write tactic blocks blind.

- **`lean_goal`** at a `sorry` or tactic to see exact hypotheses and goal.
- **`lean_diagnostic_messages`** for fast per-file error checking (prefer over `lake build`).
- **`lean_multi_attempt`** to trial candidate closers (`simp`, `omega`, `exact?`, `aesop`) without editing the file.

### Sorry-sketch first

For non-trivial proofs, stub out the full `have`-step structure with `sorry`
in each gap, check it compiles, then fill each `sorry` one at a time —
checking diagnostics after each.

### One tactic at a time

Replace a `sorry` with one tactic plus new `sorry`s for remaining subgoals.
Check the proof state after each step. After `induction`/`cases`, inspect
each branch individually.

### Never guess Mathlib names

Use search tools to find lemmas:

1. **Known locally?** → `lean_local_search`
2. **Natural language** → `lean_leansearch`
3. **Type pattern** → `lean_loogle`
4. **Conceptual/semantic** → `lean_leanfinder`
5. **What closes this goal?** → `lean_state_search`
6. **What to feed `simp`?** → `lean_hammer_premise`

After finding a name, use `lean_hover_info` to confirm its signature.

### When stuck

- If cycling on the same step, stop and decompose: extract a helper lemma,
  try a different strategy, or reconsider the definitions.
- Use `lean_code_actions` to capture `exact?`/`apply?`/`rw?` suggestions.

## Tactic Tips

- When `omega` fails on `match`/`if`/`max`:
  - **`match`**: use `cases` or `split` to eliminate the discriminant.
  - **`if`**: use `split_ifs`, or `simp only [ite_true, ite_false]`.
  - **`max`**: use `le_max_left`/`le_max_right` directly, or `max_le`.
- Use `dsimp only` to reduce projections (`.1`, `.2`), constructor matches,
  and `let` bindings left behind by `simp only`.
- Use `first | tac1 | tac2` when different case-split branches need
  different strategies.

## Proof Standards

- No `sorry` in finished proofs.
- No custom axioms beyond Lean's core (`Classical.choice`, `propext`,
  `Quot.sound`, `funext`).
- Follow Mathlib naming conventions and tactic style.
