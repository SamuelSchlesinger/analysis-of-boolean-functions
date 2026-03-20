/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger

# Chapter 1: Boolean functions and the Fourier expansion

This file contains the main theorems from Chapter 1 of "Analysis of Boolean
Functions" by Ryan O'Donnell.

## References

* Ryan O'Donnell, *Analysis of Boolean Functions*, Chapter 1.
-/

import BooleanAnalysis.FourierExpansion.Internal

namespace BooleanAnalysis

open Finset BigOperators Internal

variable {n : ℕ}

/-! ### §1.2 The Fourier expansion theorem -/

/-- **Theorem 1.1** (Fourier expansion existence): Every function `f : 𝔽₂ⁿ → ℝ` can be
    expressed as `f(x) = ∑_S 𝓕 f S · (χ S) x`. -/
theorem fourier_expansion (f : Cube n → ℝ) (x : Cube n) :
    f x = ∑ S : Finset (Fin n), 𝓕 f S * (χ S) x :=
  BooleanAnalysis.Internal.fourier_expansion_proof f x

/-- **Theorem 1.1** (Fourier uniqueness): If `f(x) = ∑_S c_S · χ_S(x)` for all `x`,
    then `c_S = 𝓕 f S` for all `S`. Together with `fourier_expansion`, this establishes
    the parity functions as an orthonormal basis for the space of functions `𝔽₂ⁿ → ℝ`. -/
theorem fourier_uniqueness (f : Cube n → ℝ) (c : Finset (Fin n) → ℝ)
    (h : ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x) :
    ∀ S, c S = 𝓕 f S :=
  Internal.fourier_uniqueness_proof f c h

/-! ### §1.3 Orthonormality of parity functions -/

/-- **Equation 1.5**: `(χ S)(x + y) = (χ S) x · (χ S) y`. -/
theorem parityFun_add' (S : Finset (Fin n)) (x y : Cube n) :
    (χ S) (x + y) = (χ S) x * (χ S) y :=
  parityFun_add S x y

/-- **Fact 1.6**: `(χ S) x · (χ T) x = (χ (S △ T)) x`. -/
theorem parityFun_mul (S T : Finset (Fin n)) (x : Cube n) :
    (χ S) x * (χ T) x = (χ (symmDiff S T)) x :=
  BooleanAnalysis.Internal.parityFun_mul S T x

/-- **Fact 1.7**: `𝔼[χ S] = 1` if `S = ∅` and `𝔼[χ S] = 0` if `S ≠ ∅`. -/
theorem expect_parityFun (S : Finset (Fin n)) :
    𝔼[χ S] = if S = ∅ then 1 else 0 :=
  Internal.expect_parityFun_proof S

/-- **Theorem 1.5** (orthonormality): The parity functions are orthonormal:
    `⟪χ S, χ T⟫ = 1` if `S = T` and `0` otherwise. -/
theorem parityFun_orthonormal (S T : Finset (Fin n)) :
    ⟪χ S, χ T⟫ = if S = T then 1 else 0 :=
  Internal.parityFun_orthonormal_proof S T

/-- **Theorem 1.5** (spanning): Every function `f : 𝔽₂ⁿ → ℝ` is a linear combination
    of parity functions. Together with `parityFun_orthonormal`, this establishes
    that the parity functions form an orthonormal basis for the space of functions
    `𝔽₂ⁿ → ℝ`. -/
theorem parityFun_span (f : Cube n → ℝ) :
    ∃ c : Finset (Fin n) → ℝ, ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x :=
  ⟨𝓕 f, fourier_expansion f⟩

/-! ### §1.4 Basic Fourier formulas -/

/-- **Proposition 1.8**: `𝓕 f S = ⟪f, χ S⟫`. This is true by definition. -/
theorem fourierCoeff_eq_innerProd (f : Cube n → ℝ) (S : Finset (Fin n)) :
    𝓕 f S = ⟪f, χ S⟫ := rfl

/-- **Parseval's Theorem**: `⟪f, f⟫ = ∑ S, (𝓕 f S) ^ 2`. -/
theorem parseval (f : Cube n → ℝ) :
    ⟪f, f⟫ = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 := by
  rw [BooleanAnalysis.Internal.plancherel_proof]; congr 1; ext S; rw [sq]

/-- **Parseval's Theorem** (Boolean case): For Boolean-valued `f`,
    `∑ S, (𝓕 f S) ^ 2 = 1`. -/
theorem parseval_boolean (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 = 1 := by
  rw [← parseval]
  simp only [innerProd, expect_unfold]
  simp_rw [show ∀ x : Cube n, f x * f x = 1 from
    fun x => by rcases hf x with h | h <;> simp [h],
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]; simp [ZMod.card]

/-- The inner product `⟪f, f⟫` is nonnegative. -/
theorem innerProd_self_nonneg (f : Cube n → ℝ) : 0 ≤ ⟪f, f⟫ :=
  Internal.innerProd_self_nonneg f

/-- `‖f‖₂² = ⟪f, f⟫`. -/
theorem l2Norm_sq (f : Cube n → ℝ) : ‖f‖₂ ^ 2 = ⟪f, f⟫ :=
  Internal.l2Norm_sq_eq_innerProd f

/-- `‖f‖₂² = ∑_S (𝓕 f S)²` (Parseval via L² norm). -/
theorem l2Norm_sq_eq_sum_fourierCoeff_sq (f : Cube n → ℝ) :
    ‖f‖₂ ^ 2 = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 :=
  Internal.l2Norm_sq_eq_sum_fourierCoeff_sq f

/-- **Plancherel's Theorem**: `⟪f, g⟫ = ∑ S, (𝓕 f S) · (𝓕 g S)`. -/
theorem plancherel (f g : Cube n → ℝ) :
    ⟪f, g⟫ = ∑ S : Finset (Fin n), (𝓕 f S) * (𝓕 g S) :=
  BooleanAnalysis.Internal.plancherel_proof f g

/-- **Proposition 1.9a**: For Boolean-valued `f, g`,
    `⟪f, g⟫ = Pr[f(x) = g(x)] - Pr[f(x) ≠ g(x)]`. -/
theorem innerProd_eq_agree_sub_disagree (f g : Cube n → ℝ)
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    ⟪f, g⟫ = (1 - hammingDist f g) - hammingDist f g := by
  have := Internal.innerProd_add_two_hammingDist f g hf hg; linarith

/-- **Proposition 1.9b**: For Boolean-valued `f, g`,
    `⟪f, g⟫ = 1 - 2·dist(f, g)`. -/
theorem innerProd_eq_one_sub_two_dist (f g : Cube n → ℝ)
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    ⟪f, g⟫ = 1 - 2 * hammingDist f g := by
  rw [innerProd_eq_agree_sub_disagree f g hf hg]; ring

/-- **Fact 1.12**: The mean of `f` equals its empty-set Fourier coefficient:
    `𝔼[f] = 𝓕 f ∅`. -/
theorem expect_eq_fourierCoeff_empty (f : Cube n → ℝ) :
    𝔼[f] = 𝓕 f ∅ := by
  simp [fourierCoeff, innerProd, parityFun_empty]

/-- **Proposition 1.13**: The variance of `f` in terms of Fourier coefficients:
    `Var[f] = ∑_{S ≠ ∅} (𝓕 f S)²`. -/
theorem variance_eq_sum_fourierCoeff_sq (f : Cube n → ℝ) :
    Var[f] = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅),
      (𝓕 f S) ^ 2 := by
  have hef : 𝔼[fun x => f x ^ 2] = ⟪f, f⟫ := by simp [innerProd, expect, sq]
  simp only [variance]
  rw [hef, parseval, expect_eq_fourierCoeff_empty]
  have := Finset.sum_erase_eq_sub (f := fun S => (fourierCoeff f S) ^ 2)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [← this]
  congr 1
  ext S; simp [Finset.mem_erase, Finset.mem_filter, and_comm]

/-- **Fact 1.14**: For Boolean-valued `f`,
    `Var[f] = 1 - 𝔼[f]² = 4·Pr[f=1]·Pr[f=-1] ∈ [0, 1]`. -/
theorem variance_boolean (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    Var[f] = 1 - (𝔼[f]) ^ 2 := by
  unfold variance
  have h1 : 𝔼[fun x => f x ^ 2] = 1 := by
    simp only [expect_unfold]
    have : ∀ x : Cube n, f x ^ 2 = 1 := by
      intro x; rcases hf x with h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    simp [Fintype.card_fin, ZMod.card]
  linarith

/-- **Fact 1.14** (probability form): For Boolean-valued `f`,
    `Var[f] = 4 · Pr[f = 1] · Pr[f = -1]`. -/
theorem variance_boolean_prob (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    Var[f] = 4 * Pr[fun x => f x = 1] * Pr[fun x => f x = -1] := by
  rw [variance_boolean f hf, expect_boolean_eq_prob_diff f hf]
  have := prob_boolean_sum_one f hf
  nlinarith [sq_nonneg (Pr[fun x => f x = 1] - Pr[fun x => f x = -1])]

/-- **Fact 1.14** (lower bound): For Boolean-valued `f`, `0 ≤ Var[f]`. -/
theorem variance_boolean_nonneg (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    0 ≤ Var[f] := by
  rw [variance_boolean f hf]
  have hexp := expect_boolean_eq_prob_diff f hf
  have hsum := prob_boolean_sum_one f hf
  have hp1 : 0 ≤ Pr[fun x => f x = 1] := prob_nonneg _
  have hp2 : 0 ≤ Pr[fun x => f x = -1] := prob_nonneg _
  nlinarith [sq_nonneg (𝔼[f])]

/-- **Fact 1.14** (upper bound): For Boolean-valued `f`, `Var[f] ≤ 1`. -/
theorem variance_boolean_le_one (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    Var[f] ≤ 1 := by
  rw [variance_boolean f hf]; nlinarith [sq_abs (𝔼[f])]

/-- **Proposition 1.15**: For Boolean-valued `f`, `2ε ≤ Var[f] ≤ 4ε`
    where `ε = min(dist(f, 1), dist(f, -1))`.

    Here `1` and `-1` denote the constant functions. -/
theorem variance_dist_bounds (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    let ε := min (hammingDist f (fun _ => 1)) (hammingDist f (fun _ => -1))
    2 * ε ≤ Var[f] ∧ Var[f] ≤ 4 * ε := by
  rw [Internal.hammingDist_const_one f hf, Internal.hammingDist_const_neg_one f hf]
  rw [variance_boolean_prob f hf]
  exact Internal.variance_dist_bounds_arith
    (Pr[fun x => f x = 1]) (Pr[fun x => f x = -1])
    (Internal.prob_nonneg _) (Internal.prob_nonneg _)
    (Internal.prob_boolean_sum_one f hf)

/-- **Proposition 1.16**: The covariance in terms of Fourier coefficients:
    `Cov[f, g] = ∑_{S ≠ ∅} (𝓕 f S) · (𝓕 g S)`. -/
theorem covariance_eq_sum_fourierCoeff (f g : Cube n → ℝ) :
    Cov[f, g] = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅),
      (𝓕 f S) * (𝓕 g S) := by
  rw [covariance, ← show ⟪f, g⟫ = 𝔼[fun x => f x * g x] from rfl]
  rw [plancherel, expect_eq_fourierCoeff_empty, expect_eq_fourierCoeff_empty]
  have := Finset.sum_erase_eq_sub (f := fun S => fourierCoeff f S * fourierCoeff g S)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [← this]
  congr 1
  ext S; simp [Finset.mem_erase, Finset.mem_filter, and_comm]

/-! ### §1.5 Probability densities and convolution -/

/-- **Fact 1.21**: If `φ` is a density and `g : 𝔽₂ⁿ → ℝ`, then
    `𝔼_{y ~ φ}[g(y)] = ⟪φ, g⟫`.

    In our formalization this is definitional: `innerProd f g` is defined as
    `𝔼[fun x => f x * g x]`. -/
theorem expect_density_eq_innerProd (φ g : Cube n → ℝ) (_hφ : IsDensity φ) :
    𝔼[fun x => φ x * g x] = ⟪φ, g⟫ := rfl

/-- **Fact 1.23**: Every Fourier coefficient of `φ_{0}` is 1; i.e.,
    `φ_{0}(y) = ∑_S (χ S) y`. -/
theorem setDensity_singleton_zero :
    ∀ y : Cube n, setDensity ({0} : Finset (Cube n)) y =
      ∑ S : Finset (Fin n), (χ S) y :=
  Internal.setDensity_singleton_zero_proof

/-- **Fact 1.23** (Fourier coefficient form): Every Fourier coefficient of
    `φ_{0}` is `1`, i.e., `𝓕 φ_{0} S = 1` for all `S`. -/
theorem fourierCoeff_setDensity_singleton_zero (S : Finset (Fin n)) :
    𝓕 (setDensity ({0} : Finset (Cube n))) S = 1 :=
  Internal.fourierCoeff_setDensity_singleton_zero_proof S

/-- **Proposition 1.25**: If `φ` is a density and `g : 𝔽₂ⁿ → ℝ`, then
    `(φ ⊛ g)(x) = 𝔼_{y ~ φ}[g(x + y)]`.

    In our formalization this is definitional: `convolution f g` is defined as
    `fun x => 𝔼[fun y => f y * g (x + y)]`. -/
theorem convolution_density (φ g : Cube n → ℝ) (_hφ : IsDensity φ) (x : Cube n) :
    (φ ⊛ g) x = 𝔼[fun y => φ y * g (x + y)] := rfl

/-- **Proposition 1.26**: If `φ` and `ψ` are both densities, then `φ ⊛ ψ`
    is also a density. -/
theorem convolution_density_isDensity (φ ψ : Cube n → ℝ)
    (hφ : IsDensity φ) (hψ : IsDensity ψ) :
    IsDensity (φ ⊛ ψ) :=
  Internal.convolution_density_isDensity_proof φ ψ hφ hψ

/-- **Theorem 1.27** (Convolution theorem):
    `𝓕 (f ⊛ g) S = (𝓕 f S) · (𝓕 g S)`. -/
theorem fourierCoeff_convolution (f g : Cube n → ℝ) (S : Finset (Fin n)) :
    𝓕 (f ⊛ g) S = (𝓕 f S) * (𝓕 g S) :=
  Internal.fourierCoeff_convolution_proof f g S

/-! ### §1.6 Linearity characterizations -/

/-- **(1')** For Boolean-valued `f`, linearity is equivalent to multiplicativity:
    `f = χ S` for some `S` iff `f(x+y) = f(x)·f(y)` for all `x, y`. -/
theorem isLinear_iff_isMultiplicative (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    IsLinear f ↔ IsMultiplicative f :=
  Internal.isLinear_iff_isMultiplicative f hf

/-- **(2')** For Boolean-valued `f`, linearity is equivalent to the triple product
    property plus `f(0) = 1`:
    `f = χ S` iff `f(x+y+z) = f(x)·f(y)·f(z)` for all `x, y, z` and `f(0) = 1`.

    The condition `f(0) = 1` is necessary: `-χ S` satisfies the triple product
    property but is not linear (since `(-χ S)(0) = -1 ≠ 1 = (χ T)(0)`). -/
theorem isLinear_iff_isTripleMultiplicative (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    IsLinear f ↔ IsTripleMultiplicative f ∧ f 0 = 1 :=
  Internal.isLinear_iff_isTripleMultiplicative f hf

/-! ### §1.6 The BLR test -/

/-- **Equation 1.10**: The BLR acceptance probability in terms of Fourier coefficients:
    `Pr_{x,y}[f(x)·f(y) = f(x+y)] = 1/2 + 1/2 · ∑_S (𝓕 f S)³`. -/
theorem blrAcceptProb_eq (f : Cube n → ℝ) (hf : IsBooleanValued f) :
    blrAcceptProb f = 1 / 2 + 1 / 2 * ∑ S : Finset (Fin n), (𝓕 f S) ^ 3 :=
  Internal.blrAcceptProb_eq_proof f hf

/-- **BLR completeness**: If `f` is linear (i.e., `f = χ_S` for some `S`),
    then the BLR test accepts with probability 1. -/
theorem blr_completeness (f : Cube n → ℝ) (hf : IsLinear f) :
    blrAcceptProb f = 1 :=
  Internal.blr_completeness_proof f hf

/-- **Theorem 1.30** (BLR soundness): If the BLR test accepts `f` with
    probability `1 - ε`, then `f` is `ε`-close to being linear. -/
theorem blr_soundness (f : Cube n → ℝ) (hf : IsBooleanValued f) (ε : ℝ)
    (hε : blrAcceptProb f ≥ 1 - ε) :
    IsCloseToProperty f IsLinear ε :=
  Internal.blr_soundness_proof f hf ε hε

/-- **Proposition 1.31** (Local correctability): If `f` is `ε`-close to the
    linear function `χ S`, then for every `x`, the algorithm
    "choose `y` uniformly, output `f(y) · f(x + y)`" outputs `(χ S) x`
    with probability at least `1 - 2ε`. -/
theorem local_correctability (f : Cube n → ℝ) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) (hclose : IsClose f (χ S) ε) (x : Cube n) :
    Pr[fun y => f y * f (x + y) = (χ S) x] ≥ 1 - 2 * ε :=
  Internal.local_correctability_proof f hf S ε hclose x

end BooleanAnalysis
