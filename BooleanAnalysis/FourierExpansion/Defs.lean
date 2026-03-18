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

## Main definitions

* `BooleanAnalysis.chi` — the encoding `ZMod 2 → ℝ`, `b ↦ (-1)^b`
* `BooleanAnalysis.parityFun` — the parity function `χ_S` for `S : Finset (Fin n)`
* `BooleanAnalysis.fourierCoeff` — the Fourier coefficient `f̂(S)`
* `BooleanAnalysis.innerProd` — the inner product `⟨f, g⟩ = 𝔼[f·g]`
* `BooleanAnalysis.fourierWeight` — the Fourier weight `f̂(S)²`
* `BooleanAnalysis.fourierWeightAtDegree` — `W^k[f]`, weight at degree `k`
* `BooleanAnalysis.convolution` — convolution `f * g` on `𝔽₂ⁿ`

## Notation

Within the `BooleanAnalysis` namespace, we provide notation that mirrors
the book's conventions:

* `𝔼[f]` — uniform expectation over the Hamming cube
* `⟪f, g⟫` — inner product `𝔼[f·g]`
* `χ S` — parity function on set `S`
* `𝓕 f S` — Fourier coefficient of `f` on `S`
* `𝐖 k f` — Fourier weight of `f` at degree `k`
-/

import Mathlib

namespace BooleanAnalysis

open Finset BigOperators

variable {n : ℕ}

/-- The Hamming cube `𝔽₂ⁿ` is `Fin n → ZMod 2`. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2

/-- The encoding `χ : ZMod 2 → ℝ` defined by `χ(b) = (-1)^b`.
    Concretely, `χ(0) = 1` and `χ(1) = -1`. (Book §1.2) -/
def chi : ZMod 2 → ℝ :=
  fun b => if b = 0 then 1 else -1

/-- The parity function `χ_S : 𝔽₂ⁿ → ℝ` for `S ⊆ [n]`, defined by
    `χ_S(x) = ∏_{i ∈ S} χ(xᵢ) = (-1)^(∑_{i ∈ S} xᵢ)`. (Definition 1.2) -/
noncomputable def parityFun (S : Finset (Fin n)) : Cube n → ℝ :=
  fun x => ∏ i ∈ S, chi (x i)

scoped prefix:max "χ" => parityFun

/-- The uniform expectation `𝔼_{x ~ 𝔽₂ⁿ}[f(x)] = 2⁻ⁿ · ∑_x f(x)`. -/
noncomputable def expect (f : Cube n → ℝ) : ℝ :=
  (1 : ℝ) / 2 ^ n * ∑ x : Cube n, f x

scoped notation "𝔼[" f "]" => expect f

/-- The inner product on functions `𝔽₂ⁿ → ℝ`, defined by
    `⟪f, g⟫ = 𝔼_x[f(x)·g(x)] = 2⁻ⁿ · ∑_x f(x)·g(x)`. (Definition 1.3) -/
noncomputable def innerProd (f g : Cube n → ℝ) : ℝ :=
  𝔼[fun x => f x * g x]

scoped notation "⟪" f ", " g "⟫" => innerProd f g

/-- The Fourier coefficient `f̂(S) = ⟪f, χ_S⟫ = 𝔼_x[f(x)·χ_S(x)]`.
    (Proposition 1.8) -/
noncomputable def fourierCoeff (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ⟪f, χ S⟫

scoped notation "𝓕" => fourierCoeff

/-- The Fourier weight of `f` on set `S`, defined as `f̂(S)²`.
    (Definition 1.17) -/
noncomputable def fourierWeight (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  𝓕 f S ^ 2

/-- The Fourier weight of `f` at degree `k`, defined as
    `𝐖 k f = ∑_{|S|=k} f̂(S)²`. (Definition 1.19) -/
noncomputable def fourierWeightAtDegree (f : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
    fourierWeight f S

scoped notation "𝐖" => fourierWeightAtDegree

/-- The relative Hamming distance between Boolean-valued functions `f` and `g`,
    `dist(f, g) = Pr_x[f(x) ≠ g(x)]`. (Definition 1.10) -/
noncomputable def hammingDist (f g : Cube n → ℝ) : ℝ :=
  𝔼[fun x => if f x = g x then 0 else 1]

/-- The convolution of `f, g : 𝔽₂ⁿ → ℝ`, defined by
    `(f ⊛ g)(x) = 𝔼_y[f(y)·g(x + y)]`. (Definition 1.24) -/
noncomputable def convolution (f g : Cube n → ℝ) : Cube n → ℝ :=
  fun x => 𝔼[fun y => f y * g (x + y)]

scoped infixl:70 " ⊛ " => convolution

/-- A probability density on `𝔽₂ⁿ` is a nonnegative function with
    `𝔼[φ] = 1`. (Definition 1.20) -/
structure IsDensity (φ : Cube n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  expect_one : 𝔼[φ] = 1

/-- A function `f : 𝔽₂ⁿ → ℝ` is Boolean-valued if its range is `{-1, 1}`.
    In the ±1 encoding, this means `f(x)² = 1` for all `x`. -/
def IsBooleanValued (f : Cube n → ℝ) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

end BooleanAnalysis
