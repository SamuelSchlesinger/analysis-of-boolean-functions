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
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace BooleanAnalysis

open Finset BigOperators

variable {n : ℕ}

/-! ### §1.2 The Fourier expansion theorem -/

/-- **Theorem 1.1** (Fourier expansion existence): Every function `f : 𝔽₂ⁿ → ℝ` can be
    expressed as `f(x) = ∑_S 𝓕 f S · (χ S) x`. -/
theorem fourier_expansion (f : BooleanFunction n) (x : Cube n) :
    f x = ∑ S : Finset (Fin n), 𝓕 f S * (χ S) x :=
  Internal.fourier_expansion_proof f x

/-- **Theorem 1.1** (Fourier uniqueness): If `f(x) = ∑_S c_S · χ_S(x)` for all `x`,
    then `c_S = 𝓕 f S` for all `S`. Together with `fourier_expansion`, this establishes
    the parity functions as an orthonormal basis for the space of functions `𝔽₂ⁿ → ℝ`. -/
theorem fourier_uniqueness (f : BooleanFunction n) (c : Finset (Fin n) → ℝ)
    (h : ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x) :
    ∀ S, c S = 𝓕 f S :=
  Internal.fourier_uniqueness_proof f c h

/-! ### §1.3 Orthonormality of parity functions -/

/-- **Equation 1.5**: `(χ S)(x + y) = (χ S) x · (χ S) y`. -/
theorem parityFun_add (S : Finset (Fin n)) (x y : Cube n) :
    (χ S) (x + y) = (χ S) x * (χ S) y :=
  Internal.parityFun_add S x y

/-- **Fact 1.6**: `(χ S) x · (χ T) x = (χ (S △ T)) x`. -/
theorem parityFun_mul (S T : Finset (Fin n)) (x : Cube n) :
    (χ S) x * (χ T) x = (χ (symmDiff S T)) x :=
  Internal.parityFun_mul S T x

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
theorem parityFun_span (f : BooleanFunction n) :
    ∃ c : Finset (Fin n) → ℝ, ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x :=
  ⟨𝓕 f, fourier_expansion f⟩

/-! ### §1.4 Basic Fourier formulas -/

/-- **Proposition 1.8**: `𝓕 f S = ⟪f, χ S⟫`. This is true by definition. -/
theorem fourierCoeff_eq_inner (f : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 f S = ⟪f, χ S⟫ := rfl

/-- **Parseval's Theorem**: `⟪f, f⟫ = ∑ S, (𝓕 f S) ^ 2`. -/
theorem parseval (f : BooleanFunction n) :
    ⟪f, f⟫ = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 :=
  Internal.parseval_proof f

/-- **Parseval's Theorem** (Boolean case): For Boolean-valued `f`,
    `∑ S, (𝓕 f S) ^ 2 = 1`. -/
theorem parseval_boolean (f : BooleanFunction n) (hf : IsBooleanValued f) :
    ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 = 1 :=
  Internal.parseval_boolean_proof f hf

/-- The inner product `⟪f, f⟫` is nonneg. -/
theorem inner_self_nonneg' (f : BooleanFunction n) : 0 ≤ ⟪f, f⟫ := by
  rw [real_inner_self_eq_norm_sq]; positivity

/-- `‖f‖₂² = ⟪f, f⟫`. -/
theorem norm_sq_eq_inner (f : BooleanFunction n) : ‖f‖₂ ^ 2 = ⟪f, f⟫ :=
  (real_inner_self_eq_norm_sq f).symm

/-- `‖f‖₂² = ∑_S (𝓕 f S)²` (Parseval via L² norm). -/
theorem norm_sq_eq_sum_fourierCoeff_sq (f : BooleanFunction n) :
    ‖f‖₂ ^ 2 = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 := by
  rw [norm_sq_eq_inner, parseval]

/-- **Plancherel's Theorem**: `⟪f, g⟫ = ∑ S, (𝓕 f S) · (𝓕 g S)`. -/
theorem plancherel (f g : BooleanFunction n) :
    ⟪f, g⟫ = ∑ S : Finset (Fin n), (𝓕 f S) * (𝓕 g S) :=
  Internal.plancherel_proof f g

/-- **Proposition 1.9a**: For Boolean-valued `f, g`,
    `⟪f, g⟫ = Pr[f(x) = g(x)] - Pr[f(x) ≠ g(x)]`. -/
theorem inner_eq_agree_sub_disagree (f g : BooleanFunction n)
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    ⟪f, g⟫ = (1 - hammingDist f g) - hammingDist f g := by
  have := Internal.inner_add_two_hammingDist f g hf hg; linarith

/-- **Proposition 1.9b**: For Boolean-valued `f, g`,
    `⟪f, g⟫ = 1 - 2·dist(f, g)`. -/
theorem inner_eq_one_sub_two_dist (f g : BooleanFunction n)
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    ⟪f, g⟫ = 1 - 2 * hammingDist f g := by
  rw [inner_eq_agree_sub_disagree f g hf hg]; ring

/-- **Fact 1.12**: The mean of `f` equals its empty-set Fourier coefficient:
    `𝔼[f] = 𝓕 f ∅`. -/
theorem expect_eq_fourierCoeff_empty (f : BooleanFunction n) :
    𝔼[f] = 𝓕 f ∅ := by
  simp [fourierCoeff, inner_eq_expect]

/-- **Proposition 1.13**: The variance of `f` in terms of Fourier coefficients:
    `Var[f] = ∑_{S ≠ ∅} (𝓕 f S)²`. -/
theorem variance_eq_sum_fourierCoeff_sq (f : BooleanFunction n) :
    Var[f] = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅),
      (𝓕 f S) ^ 2 := by
  have hef : 𝔼[fun x => f x ^ 2] = ⟪f, f⟫ := by
    rw [inner_eq_expect]; congr 1; ext x; ring
  simp only [variance]
  rw [hef, parseval, expect_eq_fourierCoeff_empty]
  have := Finset.sum_erase_eq_sub (f := fun S => (fourierCoeff f S) ^ 2)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [← this]
  congr 1
  ext S; simp [Finset.mem_erase, Finset.mem_filter, and_comm]

/-- **Fact 1.14**: For Boolean-valued `f`,
    `Var[f] = 1 - 𝔼[f]² = 4·Pr[f=1]·Pr[f=-1] ∈ [0, 1]`. -/
theorem variance_boolean (f : BooleanFunction n) (hf : IsBooleanValued f) :
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
theorem variance_boolean_prob (f : BooleanFunction n) (hf : IsBooleanValued f) :
    Var[f] = 4 * Pr[fun x => f x = 1] * Pr[fun x => f x = -1] := by
  rw [variance_boolean f hf, Internal.expect_boolean_eq_prob_diff f hf]
  have := Internal.prob_boolean_sum_one f hf
  nlinarith [sq_nonneg (Pr[fun x => f x = 1] - Pr[fun x => f x = -1])]

/-- **Fact 1.14** (lower bound): For Boolean-valued `f`, `0 ≤ Var[f]`. -/
theorem variance_boolean_nonneg (f : BooleanFunction n) (hf : IsBooleanValued f) :
    0 ≤ Var[f] := by
  rw [variance_boolean f hf]
  have hexp := Internal.expect_boolean_eq_prob_diff f hf
  have hsum := Internal.prob_boolean_sum_one f hf
  have hp1 : 0 ≤ Pr[fun x => f x = 1] := Internal.prob_nonneg _
  have hp2 : 0 ≤ Pr[fun x => f x = -1] := Internal.prob_nonneg _
  nlinarith [sq_nonneg (𝔼[f])]

/-- **Fact 1.14** (upper bound): For Boolean-valued `f`, `Var[f] ≤ 1`. -/
theorem variance_boolean_le_one (f : BooleanFunction n) (hf : IsBooleanValued f) :
    Var[f] ≤ 1 := by
  rw [variance_boolean f hf]; nlinarith [sq_abs (𝔼[f])]

/-- **Proposition 1.15**: For Boolean-valued `f`, `2ε ≤ Var[f] ≤ 4ε`
    where `ε = min(dist(f, 1), dist(f, -1))`.

    Here `1` and `-1` denote the constant functions. -/
theorem variance_dist_bounds (f : BooleanFunction n) (hf : IsBooleanValued f) :
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
theorem covariance_eq_sum_fourierCoeff (f g : BooleanFunction n) :
    Cov[f, g] = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅),
      (𝓕 f S) * (𝓕 g S) := by
  rw [covariance, ← inner_eq_expect]
  rw [plancherel, expect_eq_fourierCoeff_empty, expect_eq_fourierCoeff_empty]
  have := Finset.sum_erase_eq_sub (f := fun S => fourierCoeff f S * fourierCoeff g S)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [← this]
  congr 1
  ext S; simp [Finset.mem_erase, Finset.mem_filter, and_comm]

/-! ### §1.4 Spectral sample distribution -/

/-- **Definition 1.18** (Spectral sample): For Boolean-valued `f`, the squared
    Fourier coefficients `(𝓕 f S)²` form a probability distribution on `2^[n]`,
    represented as a `PMF`. By Parseval's theorem, `∑_S (𝓕 f S)² = 1`. -/
noncomputable def spectralSample (f : BooleanFunction n) (hf : IsBooleanValued f) :
    PMF (Finset (Fin n)) :=
  PMF.ofFintype (fun S => ENNReal.ofReal (fourierWeight f S)) (by
    simp only [fourierWeight,
      ← ENNReal.ofReal_sum_of_nonneg (fun S _ => sq_nonneg (𝓕 f S))]
    rw [parseval_boolean f hf]; simp)

/-! ### §1.5 Probability densities and convolution -/

/-- **Fact 1.21**: `𝔼[f·g] = ⟪f, g⟫` for all `f, g`.

    The book states this for densities `φ`, interpreting `𝔼_{y ~ φ}[g(y)] = ⟪φ, g⟫`,
    but the identity holds for all functions since our inner product is defined as
    `⟪f, g⟫ = 𝔼[f·g]`. -/
theorem expect_mul_eq_inner (f g : BooleanFunction n) :
    𝔼[fun x => f x * g x] = ⟪f, g⟫ :=
  (inner_eq_expect f g).symm

/-- **Definition 1.22** (Set density is a density): For nonempty `A ⊆ 𝔽₂ⁿ`,
    the set density `φ_A` is a valid probability density. -/
theorem setDensity_isDensity (A : Finset (Cube n)) (hA : A.Nonempty) :
    IsDensity (setDensity A) :=
  Internal.setDensity_isDensity_proof A hA

/-- Convert a density on `𝔽₂ⁿ` to a Mathlib `PMF`, bridging the book's real-valued
    density convention with Mathlib's measure-theoretic probability API.

    The book's density satisfies `𝔼[φ] = (1/2ⁿ) · ∑_x φ(x) = 1`, so
    `∑_x φ(x) = 2ⁿ`. The PMF assigns mass `φ(x) / 2ⁿ` to each `x`. -/
noncomputable def IsDensity.toPMF {φ : BooleanFunction n} (hφ : IsDensity φ) :
    PMF (Cube n) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (φ x / 2 ^ n)) (by
    have hsum : ∑ x : Cube n, φ x / 2 ^ n = 1 := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      have h := hφ.expect_one; simp only [expect_unfold] at h
      have h2n : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
      rw [show (∑ x : Cube n, φ x) * (2 ^ n)⁻¹ = 1 / 2 ^ n * ∑ x, φ x from by ring]
      linarith
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
      div_nonneg (hφ.nonneg x) (by positivity)), hsum]
    simp)

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

/-- **Fact 1.23** (general form): The Fourier coefficients of the set density `φ_A`
    are `𝓕 φ_A S = (1/|A|) · ∑_{x ∈ A} χ_S(x)`, i.e., the uniform average of `χ_S`
    over `A`. -/
theorem fourierCoeff_setDensity (A : Finset (Cube n)) (hA : A.Nonempty)
    (S : Finset (Fin n)) :
    𝓕 (setDensity A) S = (1 / A.card) * ∑ x ∈ A, (χ S) x :=
  Internal.fourierCoeff_setDensity_proof A hA S

/-- **Proposition 1.25**: `(f ⊛ g)(x) = 𝔼_y[f(y)·g(x + y)]`.

    The book states this for densities, but our definition of convolution makes
    this hold definitionally for all functions. -/
theorem convolution_eq (f g : BooleanFunction n) (x : Cube n) :
    (f ⊛ g) x = 𝔼[fun y => f y * g (x + y)] := rfl

/-- **Proposition 1.26**: If `φ` and `ψ` are both densities, then `φ ⊛ ψ`
    is also a density. -/
theorem convolution_density_isDensity (φ ψ : BooleanFunction n)
    (hφ : IsDensity φ) (hψ : IsDensity ψ) :
    IsDensity (φ ⊛ ψ) :=
  Internal.convolution_density_isDensity_proof φ ψ hφ hψ

/-- **Theorem 1.27** (Convolution theorem):
    `𝓕 (f ⊛ g) S = (𝓕 f S) · (𝓕 g S)`. -/
theorem fourierCoeff_convolution (f g : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 (f ⊛ g) S = (𝓕 f S) * (𝓕 g S) :=
  Internal.fourierCoeff_convolution_proof f g S

/-! ### §1.6 Linearity characterizations -/

/-- **Definition 1.28** (equivalence): For Boolean-valued `f`, linearity is
    equivalent to multiplicativity:
    `f = χ S` for some `S` iff `f(x+y) = f(x)·f(y)` for all `x, y`. -/
theorem isLinear_iff_isMultiplicative (f : BooleanFunction n) (hf : IsBooleanValued f) :
    IsLinear f ↔ IsMultiplicative f :=
  Internal.isLinear_iff_isMultiplicative f hf

/-! ### §1.6 The BLR test -/

/-- **Equation 1.10**: The BLR acceptance probability in terms of Fourier coefficients:
    `Pr_{x,y}[f(x)·f(y) = f(x+y)] = 1/2 + 1/2 · ∑_S (𝓕 f S)³`. -/
theorem blrAcceptProb_eq (f : BooleanFunction n) (hf : IsBooleanValued f) :
    blrAcceptProb f = 1 / 2 + 1 / 2 * ∑ S : Finset (Fin n), (𝓕 f S) ^ 3 :=
  Internal.blrAcceptProb_eq_proof f hf

/-- **BLR completeness**: If `f` is linear (i.e., `f = χ_S` for some `S`),
    then the BLR test accepts with probability 1. -/
theorem blr_completeness (f : BooleanFunction n) (hf : IsLinear f) :
    blrAcceptProb f = 1 :=
  Internal.blr_completeness_proof f hf

/-- **Theorem 1.30** (BLR soundness): If the BLR test accepts `f` with
    probability `1 - ε`, then `f` is `ε`-close to being linear. -/
theorem blr_soundness (f : BooleanFunction n) (hf : IsBooleanValued f) (ε : ℝ)
    (hε : blrAcceptProb f ≥ 1 - ε) :
    IsCloseToProperty f IsLinear ε :=
  Internal.blr_soundness_proof f hf ε hε

/-- **Proposition 1.31** (Local correctability): If `f` is `ε`-close to the
    linear function `χ S`, then for every `x`, the algorithm
    "choose `y` uniformly, output `f(y) · f(x + y)`" outputs `(χ S) x`
    with probability at least `1 - 2ε`. -/
theorem local_correctability (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) (hclose : IsClose f (χ S) ε) (x : Cube n) :
    Pr[fun y => f y * f (x + y) = (χ S) x] ≥ 1 - 2 * ε :=
  Internal.local_correctability_proof f hf S ε hclose x

end BooleanAnalysis
