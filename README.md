# Analysis of Boolean Functions — Lean 4 Formalization

Lean 4 formalization of [Analysis of Boolean Functions](https://arxiv.org/abs/2105.10386) by Ryan O'Donnell, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Building

```bash
lake build
```

## Structure

The formalization follows the book chapter by chapter. Each module `X` is split into:

- **`X.Defs`** — Definitions (the public interface)
- **`X.Internal`** — Proof internals (depends on `X.Defs`)
- **`X`** — Main theorems (depends on `X.Internal` and `X.Defs`)

This separation lets reviewers focus on `X` and `X.Defs` without wading through proof machinery.

## Chapters

1. Boolean functions and the Fourier expansion
2. Basic concepts and social choice
3. Spectral structure and learning
4. DNF formulas and small-depth circuits
5. Majority and threshold functions
6. Pseudorandomness and F₂-polynomials
7. Property testing, PCPPs, and CSPs
8. Generalized domains
9. Basics of hypercontractivity
10. Advanced hypercontractivity
11. Gaussian space and Invariance Principles
