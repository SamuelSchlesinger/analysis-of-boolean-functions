/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger

# Chapter 1: Boolean functions and the Fourier expansion — Definitions

This file contains the core definitions for Fourier analysis of Boolean functions
following Chapter 1 of "Analysis of Boolean Functions" by Ryan O'Donnell.

We work with the Hamming cube modeled as `Fin n → ZMod 2`, with the encoding
`χ : ZMod 2 → ℝ` sending `0 ↦ 1` and `1 ↦ -1`. This corresponds to the book's
convention of representing the cube as `{-1, 1}^n` via the map `b ↦ (-1)^b`.

## Notation

Within the `BooleanAnalysis` namespace, we provide notation that mirrors
the book's conventions:

* `𝔼[f]` — uniform expectation over the Hamming cube
* `⟪f, g⟫` — inner product `𝔼[f·g]`
* `χ S` — parity function on set `S`
* `𝓕 f S` — Fourier coefficient of `f` on `S`
* `𝐖 f k` — Fourier weight of `f` at degree `k`
* `Var[f]` — variance of `f`
* `Cov[f, g]` — covariance of `f` and `g`
* `f ⊛ g` — convolution
* `𝟙 A` — indicator function of `A`
-/

import Mathlib

namespace BooleanAnalysis

open Finset BigOperators

variable {n : ℕ}

/-! ### Basic types -/

/-- The Hamming cube `𝔽₂ⁿ` is `Fin n → ZMod 2`. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2

/-- A function `f : 𝔽₂ⁿ → ℝ` is Boolean-valued if its range is `{-1, 1}`.
    In the ±1 encoding, this means `f(x) = ±1` for all `x`. -/
def IsBooleanValued (f : Cube n → ℝ) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

/-! ### §1.2 The encoding and parity functions -/

/-- The encoding `χ : ZMod 2 → ℝ` defined by `χ(b) = (-1)^b`.
    Concretely, `χ(0) = 1` and `χ(1) = -1`. (Book §1.2) -/
def chi : ZMod 2 → ℝ :=
  fun b => if b = 0 then 1 else -1

/-- The parity function `χ S : 𝔽₂ⁿ → ℝ` for `S ⊆ [n]`, defined by
    `(χ S)(x) = ∏_{i ∈ S} χ(xᵢ) = (-1)^(∑_{i ∈ S} xᵢ)`. (Definition 1.2) -/
noncomputable def parityFun (S : Finset (Fin n)) : Cube n → ℝ :=
  fun x => ∏ i ∈ S, chi (x i)

scoped prefix:max "χ" => parityFun

/-! ### §1.3–1.4 Expectation, inner product, Fourier coefficients -/

/-- The uniform expectation `𝔼[f] = 2⁻ⁿ · ∑_x f(x)`. -/
noncomputable def expect (f : Cube n → ℝ) : ℝ :=
  (1 : ℝ) / 2 ^ n * ∑ x : Cube n, f x

scoped notation "𝔼[" f "]" => expect f

/-- The inner product on functions `𝔽₂ⁿ → ℝ`, defined by
    `⟪f, g⟫ = 𝔼[f·g]`. (Definition 1.3) -/
noncomputable def innerProd (f g : Cube n → ℝ) : ℝ :=
  𝔼[fun x => f x * g x]

scoped notation "⟪" f ", " g "⟫" => innerProd f g

/-- The Fourier coefficient `𝓕 f S = ⟪f, χ S⟫`.
    (Proposition 1.8 / our definition) -/
noncomputable def fourierCoeff (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ⟪f, χ S⟫

scoped notation "𝓕" => fourierCoeff

/-! ### §1.4 Variance, covariance, mean -/

/-- The variance of `f : 𝔽₂ⁿ → ℝ`, defined as
    `Var[f] = 𝔼[f²] - 𝔼[f]²`. (Proposition 1.13) -/
noncomputable def variance (f : Cube n → ℝ) : ℝ :=
  𝔼[fun x => f x ^ 2] - (𝔼[f]) ^ 2

scoped notation "Var[" f "]" => variance f

/-- The covariance of `f, g : 𝔽₂ⁿ → ℝ`, defined as
    `Cov[f, g] = 𝔼[f·g] - 𝔼[f]·𝔼[g]`. (Proposition 1.16) -/
noncomputable def covariance (f g : Cube n → ℝ) : ℝ :=
  𝔼[fun x => f x * g x] - 𝔼[f] * 𝔼[g]

scoped notation "Cov[" f ", " g "]" => covariance f g

/-- The relative Hamming distance between functions `f` and `g`,
    `dist(f, g) = Pr_x[f(x) ≠ g(x)]`. (Definition 1.10) -/
noncomputable def hammingDist (f g : Cube n → ℝ) : ℝ :=
  𝔼[fun x => if f x = g x then 0 else 1]

/-! ### §1.4 Fourier weight distribution -/

/-- The Fourier weight of `f` on set `S`, defined as `(𝓕 f S)²`.
    (Definition 1.17) -/
noncomputable def fourierWeight (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  𝓕 f S ^ 2

/-- The spectral sample for a Boolean-valued `f`, the distribution on
    subsets of `[n]` where `S` has probability `(𝓕 f S)²`.
    (Definition 1.18) -/
noncomputable def spectralSample (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  fourierWeight f S

/-- The Fourier weight of `f` at degree `k`:
    `𝐖 f k = ∑_{|S|=k} (𝓕 f S)²`. (Definition 1.19) -/
noncomputable def fourierWeightAtDegree (f : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
    fourierWeight f S

scoped notation "𝐖" => fourierWeightAtDegree

/-- The degree-k part of `f`: `f^{=k} = ∑_{|S|=k} 𝓕 f S · χ S`.
    (Definition 1.19) -/
noncomputable def degreePart (f : Cube n → ℝ) (k : ℕ) : Cube n → ℝ :=
  fun x => ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
    𝓕 f S * (χ S) x

/-- The degree-at-most-k part of `f`: `f^{≤k} = ∑_{|S|≤k} 𝓕 f S · χ S`.
    (Definition 1.19) -/
noncomputable def lowDegreePart (f : Cube n → ℝ) (k : ℕ) : Cube n → ℝ :=
  fun x => ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k),
    𝓕 f S * (χ S) x

/-! ### §1.5 Probability densities and convolution -/

/-- A probability density on `𝔽₂ⁿ` is a nonnegative function with
    `𝔼[φ] = 1`. (Definition 1.20) -/
structure IsDensity (φ : Cube n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  expect_one : 𝔼[φ] = 1

/-- The 0-1 indicator function of a set `A ⊆ 𝔽₂ⁿ`.
    `(𝟙 A)(x) = 1` if `x ∈ A`, else `0`. (Definition 1.22) -/
noncomputable def indicator (A : Finset (Cube n)) : Cube n → ℝ :=
  fun x => if x ∈ A then 1 else 0

scoped prefix:max "𝟙" => indicator

/-- The density function associated to a nonempty set `A ⊆ 𝔽₂ⁿ`:
    `φ_A = (1 / 𝔼[𝟙 A]) · 𝟙 A`. (Definition 1.22) -/
noncomputable def setDensity (A : Finset (Cube n)) : Cube n → ℝ :=
  fun x => (1 / 𝔼[𝟙 A]) * (𝟙 A) x

/-- The convolution of `f, g : 𝔽₂ⁿ → ℝ`, defined by
    `(f ⊛ g)(x) = 𝔼_y[f(y)·g(x + y)]`. (Definition 1.24) -/
noncomputable def convolution (f g : Cube n → ℝ) : Cube n → ℝ :=
  fun x => 𝔼[fun y => f y * g (x + y)]

scoped infixl:70 " ⊛ " => convolution

/-! ### §1.6 Linearity and the BLR test -/

/-- A function `f : 𝔽₂ⁿ → 𝔽₂` (encoded as `Cube n → ℝ` with ±1 values)
    is *linear* if it equals some parity function `χ S`.
    Equivalently, `f(x+y) = f(x)·f(y)` for all `x, y`. (Definition 1.28) -/
def IsLinear (f : Cube n → ℝ) : Prop :=
  ∃ S : Finset (Fin n), ∀ x, f x = (χ S) x

/-- Two Boolean-valued functions are `ε`-close if `dist(f, g) ≤ ε`.
    (Definition 1.29) -/
def IsClose (ε : ℝ) (f g : Cube n → ℝ) : Prop :=
  hammingDist f g ≤ ε

/-- A Boolean-valued function is `ε`-close to a property `P` if there
    exists `g` satisfying `P` with `dist(f, g) ≤ ε`. (Definition 1.29) -/
def IsCloseToProperty (ε : ℝ) (f : Cube n → ℝ)
    (P : (Cube n → ℝ) → Prop) : Prop :=
  ∃ g, P g ∧ IsClose ε f g

/-- The BLR acceptance probability: `Pr_{x,y}[f(x)·f(y) = f(x+y)]`,
    which equals `1/2 + 1/2 · ∑_S 𝓕 f S ^ 3`. -/
noncomputable def blrAcceptProb (f : Cube n → ℝ) : ℝ :=
  𝔼[fun x => 𝔼[fun y => if f x * f y = f (x + y) then (1 : ℝ) else 0]]

end BooleanAnalysis
