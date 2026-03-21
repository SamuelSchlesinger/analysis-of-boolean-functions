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
* `‖f‖₂` — L² norm `√⟪f, f⟫`
* `χ S` — parity function on set `S`
* `𝓕 f S` — Fourier coefficient of `f` on `S`
* `𝐖 f k` — Fourier weight of `f` at degree `k`
* `Var[f]` — variance of `f`
* `Cov[f, g]` — covariance of `f` and `g`
* `f ⊛ g` — convolution
* `𝟙 P` — indicator function of predicate `P`
* `Pr[P]` — uniform probability `𝔼[𝟙 P]`
* `Pr₂[P]` — joint uniform probability over pairs
-/

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic

namespace BooleanAnalysis

open Finset BigOperators Classical

variable {n : ℕ}

/-! ### Basic types -/

/-- The Hamming cube `𝔽₂ⁿ` is `Fin n → ZMod 2`. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2

/-- `L2Cube n` is the space of functions `𝔽₂ⁿ → ℝ` equipped with the
    uniform-measure L² inner product. The `def` (rather than `abbrev`) blocks
    typeclass resolution from seeing through to `Cube n → ℝ`, avoiding a
    norm diamond with Mathlib's Pi-type sup norm.

    Named after the L² space on the Boolean cube from O'Donnell's
    *Analysis of Boolean Functions* (§1.3). -/
def L2Cube (n : ℕ) := Cube n → ℝ

namespace L2Cube

instance : AddCommGroup (L2Cube n) := inferInstanceAs (AddCommGroup (Cube n → ℝ))
noncomputable instance : Module ℝ (L2Cube n) := inferInstanceAs (Module ℝ (Cube n → ℝ))
instance : Inhabited (L2Cube n) := inferInstanceAs (Inhabited (Cube n → ℝ))

instance : FunLike (L2Cube n) (Cube n) ℝ where
  coe f := f
  coe_injective' f g h := show (f : Cube n → ℝ) = g from h

@[ext]
theorem ext {f g : L2Cube n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem zero_apply (x : Cube n) : (0 : L2Cube n) x = 0 := rfl
@[simp] theorem add_apply (f g : L2Cube n) (x : Cube n) : (f + g) x = f x + g x := rfl
@[simp] theorem neg_apply (f : L2Cube n) (x : Cube n) : (-f) x = -(f x) := rfl
@[simp] theorem sub_apply (f g : L2Cube n) (x : Cube n) : (f - g) x = f x - g x := rfl
@[simp] theorem smul_apply (r : ℝ) (f : L2Cube n) (x : Cube n) : (r • f) x = r * f x := rfl

/-- Coerce a function to `L2Cube`. -/
def ofFun (f : Cube n → ℝ) : L2Cube n := f

/-- Extract the underlying function. -/
def toFun (f : L2Cube n) : Cube n → ℝ := f

@[simp] theorem toFun_ofFun (f : Cube n → ℝ) : toFun (ofFun f) = f := rfl
@[simp] theorem ofFun_toFun (f : L2Cube n) : ofFun (toFun f) = f := rfl

end L2Cube

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
  Finset.univ.expect f

scoped notation "𝔼[" f "]" => expect f

/-- The inner product on functions `𝔽₂ⁿ → ℝ`, defined by
    `⟪f, g⟫ = 𝔼[f·g]`. (Definition 1.3) -/
noncomputable def innerProd (f g : Cube n → ℝ) : ℝ :=
  𝔼[fun x => f x * g x]

scoped notation "⟪" f ", " g "⟫" => innerProd f g

/-- The `L²` norm: `‖f‖₂ = √⟪f, f⟫`. (§1.3, page 24) -/
noncomputable def l2Norm (f : Cube n → ℝ) : ℝ :=
  Real.sqrt ⟪f, f⟫

scoped notation "‖" f "‖₂" => l2Norm f

/-- The Fourier coefficient `𝓕 f S = ⟪f, χ S⟫`.
    (Proposition 1.8 / our definition) -/
noncomputable def fourierCoeff (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ⟪f, χ S⟫

scoped notation "𝓕" => fourierCoeff

/-! ### §1.4 Mean, variance, covariance -/

/-- A function `f : 𝔽₂ⁿ → ℝ` is *unbiased* (or *balanced*) if `𝔼[f] = 0`.
    (Definition 1.11) -/
def IsUnbiased (f : Cube n → ℝ) : Prop := 𝔼[f] = 0

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

/-- The 0-1 indicator function of a predicate `P` on `𝔽₂ⁿ`.
    `(𝟙 P)(x) = 1` if `P x`, else `0`.

    The book (Definition 1.22) defines `𝟙_A` for a set `A ⊆ 𝔽₂ⁿ`. We generalize
    to predicates so that probability expressions like `Pr_x[P(x)] = 𝔼[𝟙 P]`
    read cleanly without `Finset.univ.filter` boilerplate. For the set version,
    use `𝟙 (· ∈ A)`. -/
noncomputable def indicator (P : Cube n → Prop) : Cube n → ℝ :=
  fun x => if P x then 1 else 0

scoped prefix:max "𝟙" => indicator

/-- The uniform probability `Pr_x[P(x)] = 𝔼[𝟙 P]`. -/
noncomputable def prob (P : Cube n → Prop) : ℝ := 𝔼[𝟙 P]

scoped notation "Pr[" P "]" => prob P

/-- The joint uniform probability `Pr_{x,y}[P(x,y)] = 𝔼_x[𝔼_y[𝟙 (P x)]]`.
    Equivalent to the uniform probability over the product space by Fubini. -/
noncomputable def prob₂ (P : Cube n → Cube n → Prop) : ℝ :=
  𝔼[fun x => 𝔼[𝟙 (P x)]]

scoped notation "Pr₂[" P "]" => prob₂ P

/-- The relative Hamming distance between functions `f` and `g`,
    `dist(f, g) = Pr_x[f(x) ≠ g(x)]`. (Definition 1.10) -/
noncomputable def hammingDist (f g : Cube n → ℝ) : ℝ :=
  Pr[fun x => f x ≠ g x]

/-! ### §1.4 Fourier weight distribution -/

/-- The Fourier weight of `f` on set `S`, defined as `(𝓕 f S)²`.
    (Definition 1.17) -/
noncomputable def fourierWeight (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  𝓕 f S ^ 2

/-- The spectral sample distribution of a Boolean-valued function `f`.
    For each `S ⊆ [n]`, the spectral sample assigns probability `(𝓕 f S)²`.
    By Parseval's theorem, these sum to `1` for Boolean-valued `f`.
    (Definition 1.18) -/
noncomputable def spectralSample (f : Cube n → ℝ) : Finset (Fin n) → ℝ :=
  fun S => fourierWeight f S

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

/-- The Fourier weight of `f` at degrees above `k`:
    `𝐖^{>k}[f] = ∑_{|S|>k} (𝓕 f S)²`. (Definition 1.19) -/
noncomputable def fourierWeightAbove (f : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card > k),
    fourierWeight f S

/-- The *(real) degree* of `f : 𝔽₂ⁿ → ℝ`:
    `deg(f) = max { |S| : 𝓕 f S ≠ 0 }`. (Exercise 1.10, referenced in main text)

    Returns `none` for the zero function (which has no nonzero Fourier coefficients).
    The book leaves the degree undefined in this case. -/
noncomputable def degree (f : Cube n → ℝ) : Option ℕ :=
  let support := Finset.univ.filter (fun S : Finset (Fin n) => 𝓕 f S ≠ 0)
  if support = ∅ then none
  else some (support.sup Finset.card)

/-! ### §1.5 Probability densities and convolution -/

/-- A probability density on `𝔽₂ⁿ` is a nonnegative function with
    `𝔼[φ] = 1`. (Definition 1.20) -/
structure IsDensity (φ : Cube n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  expect_one : 𝔼[φ] = 1

/-- The density function associated to a nonempty set `A ⊆ 𝔽₂ⁿ`:
    `φ_A = (1 / 𝔼[𝟙 A]) · 𝟙 A`. (Definition 1.22)

    **Warning**: This definition is junk when `A = ∅`, since it divides by
    `𝔼[𝟙 ∅] = 0`. The book requires `A` to be nonempty. Theorems using
    `setDensity` should include a hypothesis `A.Nonempty` where needed. -/
noncomputable def setDensity (A : Finset (Cube n)) : Cube n → ℝ :=
  fun x => (1 / 𝔼[𝟙 (· ∈ A)]) * (𝟙 (· ∈ A)) x

/-- The convolution of `f, g : 𝔽₂ⁿ → ℝ`, defined by
    `(f ⊛ g)(x) = 𝔼_y[f(y)·g(x + y)]`. (Definition 1.24) -/
noncomputable def convolution (f g : Cube n → ℝ) : Cube n → ℝ :=
  fun x => 𝔼[fun y => f y * g (x + y)]

scoped infixl:70 " ⊛ " => convolution

/-! ### §1.6 Linearity and the BLR test -/

/-- A function `f : 𝔽₂ⁿ → 𝔽₂` (encoded as `Cube n → ℝ` with ±1 values)
    is *linear* if it equals some parity function `χ S`. (Definition 1.28) -/
def IsLinear (f : Cube n → ℝ) : Prop :=
  ∃ S : Finset (Fin n), ∀ x, f x = (χ S) x

/-- A function `f : 𝔽₂ⁿ → ℝ` is *multiplicative* if `f(x+y) = f(x)·f(y)` for all
    `x, y`. This is the characterization (1') of linearity from §1.6. -/
def IsMultiplicative (f : Cube n → ℝ) : Prop :=
  ∀ x y, f (x + y) = f x * f y

/-- A function `f : 𝔽₂ⁿ → ℝ` satisfies the *triple product property* if
    `f(x+y+z) = f(x)·f(y)·f(z)` for all `x, y, z`. This is the
    characterization (2') of linearity from §1.6. -/
def IsTripleMultiplicative (f : Cube n → ℝ) : Prop :=
  ∀ x y z, f (x + y + z) = f x * f y * f z

/-- Two Boolean-valued functions are `ε`-close if `dist(f, g) ≤ ε`.
    (Definition 1.29) -/
def IsClose (f g : Cube n → ℝ) (ε : ℝ) : Prop :=
  hammingDist f g ≤ ε

/-- A Boolean-valued function is `ε`-close to a property `P` if there
    exists `g` satisfying `P` with `dist(f, g) ≤ ε`. (Definition 1.29) -/
def IsCloseToProperty (f : Cube n → ℝ)
    (P : (Cube n → ℝ) → Prop) (ε : ℝ) : Prop :=
  ∃ g, P g ∧ IsClose f g ε

/-- The BLR acceptance probability: `Pr_{x,y}[f(x)·f(y) = f(x+y)]`,
    which equals `1/2 + 1/2 · ∑_S 𝓕 f S ^ 3`. -/
noncomputable def blrAcceptProb (f : Cube n → ℝ) : ℝ :=
  Pr₂[fun x y => f x * f y = f (x + y)]

end BooleanAnalysis
