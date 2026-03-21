/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger

# L²(𝔽₂ⁿ) — The inner product space of functions on the Boolean cube

This file defines `L2Cube n`, a type synonym for `Cube n → ℝ` equipped with
the uniform-measure inner product `⟪f, g⟫ = 𝔼[f·g] = (1/2ⁿ) · ∑_x f(x)·g(x)`.

This matches the conventions of O'Donnell's *Analysis of Boolean Functions*
(§1.3), where the inner product is an expectation rather than a raw sum.

The `def` (rather than `abbrev`) ensures that Lean's typeclass resolution does
NOT see through `L2Cube n` to `Cube n → ℝ`, avoiding a norm diamond with the
Pi-type sup norm that Mathlib puts on function types.

## Main results

- `L2Cube.innerProductSpace`: The `InnerProductSpace ℝ (L2Cube n)` instance
  with inner product `(1/2ⁿ) · ∑_x f(x) · g(x)`.
-/

import BooleanAnalysis.FourierExpansion.Internal
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace BooleanAnalysis

open Finset BigOperators

variable {n : ℕ}

/-- `L2Cube n` is the space of functions `𝔽₂ⁿ → ℝ` equipped with the
    uniform-measure inner product `⟪f, g⟫ = 𝔼[f·g]`.

    Named after the L² space on the Boolean cube that appears throughout
    O'Donnell's *Analysis of Boolean Functions*. -/
def L2Cube (n : ℕ) := Cube n → ℝ

namespace L2Cube

/-! ### Transfer algebraic instances from `Cube n → ℝ`

Following Mathlib's `WithLp` pattern, we use `inferInstanceAs` to transfer
instances through the definitional equality `L2Cube n = (Cube n → ℝ)`. -/

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

/-! ### Inner product -/

/-- The uniform-measure inner product: `⟪f, g⟫ = (1/2ⁿ) · ∑_x f(x)·g(x)`. -/
noncomputable instance instInner : Inner ℝ (L2Cube n) where
  inner f g := (1 / (2 : ℝ) ^ n) * ∑ x : Cube n, f x * g x

theorem inner_def (f g : L2Cube n) :
    @inner ℝ _ instInner f g = (1 / (2 : ℝ) ^ n) * ∑ x : Cube n, f x * g x := rfl

/-- The inner product on `L2Cube` matches `BooleanAnalysis.innerProd` on the
    underlying functions. -/
theorem inner_eq_innerProd (f g : L2Cube n) :
    @inner ℝ _ instInner f g = innerProd (toFun f) (toFun g) := by
  simp only [inner_def, innerProd, expect, toFun, Finset.expect_eq_sum_div_card]
  have : Finset.card Finset.univ = Fintype.card (Cube n) := Finset.card_univ
  rw [this, show (Fintype.card (Cube n) : ℝ) = 2 ^ n from by simp [ZMod.card]]
  field_simp

/-! ### InnerProductSpace instance -/

private theorem inner_comm (f g : L2Cube n) :
    @inner ℝ _ instInner f g = @inner ℝ _ instInner g f := by
  simp only [inner_def]; congr 1; apply Finset.sum_congr rfl; intro x _; ring

private theorem inner_add_left (f g h : L2Cube n) :
    @inner ℝ _ instInner (f + g) h = @inner ℝ _ instInner f h + @inner ℝ _ instInner g h := by
  simp only [inner_def, add_apply, add_mul, Finset.sum_add_distrib, mul_add]

private theorem inner_smul_left (r : ℝ) (f g : L2Cube n) :
    @inner ℝ _ instInner (r • f) g = r * @inner ℝ _ instInner f g := by
  simp only [inner_def, smul_apply, Finset.mul_sum]; ring_nf

private theorem inner_self_nonneg (f : L2Cube n) :
    0 ≤ @inner ℝ _ instInner f f := by
  simp only [inner_def]
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg; intro x _; exact mul_self_nonneg (f x)

private theorem inner_self_eq_zero {f : L2Cube n} (h : @inner ℝ _ instInner f f = 0) :
    f = 0 := by
  simp only [inner_def] at h
  have h2n : (0 : ℝ) < 1 / 2 ^ n := by positivity
  have hsum : ∑ x : Cube n, f x * f x = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · exact h1
  ext x
  have : f x * f x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg (f x))).mp hsum
      x (Finset.mem_univ x)
  simpa [mul_self_eq_zero] using this

noncomputable instance instCore : PreInnerProductSpace.Core ℝ (L2Cube n) where
  conj_inner_symm f g := by simp [inner_comm f g]
  re_inner_nonneg f := by simp [inner_self_nonneg f]
  add_left := inner_add_left
  smul_left f g r := by rw [inner_smul_left]; simp

noncomputable instance instFullCore : InnerProductSpace.Core ℝ (L2Cube n) where
  toCore := instCore
  definite := @inner_self_eq_zero n

noncomputable instance : NormedAddCommGroup (L2Cube n) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ instFullCore

noncomputable instance innerProductSpace : InnerProductSpace ℝ (L2Cube n) :=
  InnerProductSpace.ofCore instCore

/-! ### Parity functions as an orthonormal basis -/

open BooleanAnalysis in
/-- The parity function `χ S` lifted to `L2Cube n`. -/
noncomputable def parityBasis (S : Finset (Fin n)) : L2Cube n :=
  ofFun (χ S)

theorem parityBasis_apply (S : Finset (Fin n)) (x : Cube n) :
    parityBasis S x = (χ S) x := rfl

/-- The parity functions are orthonormal under the uniform-measure inner product. -/
theorem parityBasis_orthonormal : Orthonormal ℝ (parityBasis (n := n)) := by
  rw [orthonormal_iff_ite]
  intro i j
  -- The `inner` from `InnerProductSpace` agrees with our `instInner`
  change @inner ℝ _ instInner (parityBasis i) (parityBasis j) = _
  rw [inner_eq_innerProd]
  exact Internal.parityFun_orthonormal_proof i j

/-- The parity functions span `L2Cube n`. -/
theorem parityBasis_span : ⊤ ≤ Submodule.span ℝ (Set.range (parityBasis (n := n))) := by
  intro f _
  -- f = ∑_S f̂(S) · χ_S by the Fourier expansion
  have hexp : ∀ x, f x = ∑ S : Finset (Fin n), fourierCoeff f S * (χ S) x :=
    Internal.fourier_expansion_proof f
  -- Show f = ∑_S f̂(S) • parityBasis S as an element of L2Cube
  have hf : f = ∑ S : Finset (Fin n), fourierCoeff f S • parityBasis S := by
    ext x
    have : (∑ S : Finset (Fin n), fourierCoeff f S • parityBasis S) x =
        ∑ S : Finset (Fin n), fourierCoeff f S * (χ S) x := by
      show (∑ S, fourierCoeff f S • parityBasis S : Cube n → ℝ) x = _
      simp [Finset.sum_apply, parityBasis, ofFun]
    rw [this]; exact hexp x
  rw [hf]
  exact Submodule.sum_mem _ (fun S _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩))

/-- The parity functions form an orthonormal basis for `L2Cube n`. -/
noncomputable def parityOrthonormalBasis : OrthonormalBasis (Finset (Fin n)) ℝ (L2Cube n) :=
  OrthonormalBasis.mk parityBasis_orthonormal parityBasis_span

@[simp] theorem parityOrthonormalBasis_apply (S : Finset (Fin n)) :
    parityOrthonormalBasis S = parityBasis S := by
  show (OrthonormalBasis.mk parityBasis_orthonormal parityBasis_span) S = _
  simp [OrthonormalBasis.coe_mk]

/-! ### Free theorems from the orthonormal basis -/

/-- **Fourier expansion** (from `OrthonormalBasis`):
    `f = ∑_S ⟪χ_S, f⟫ • χ_S`. -/
theorem fourier_expansion_L2 (f : L2Cube n) :
    f = ∑ S : Finset (Fin n), (parityOrthonormalBasis.repr f).ofLp S • parityBasis S := by
  have := parityOrthonormalBasis.sum_repr f
  simp only [parityOrthonormalBasis_apply] at this
  exact this.symm

/-- **Plancherel's theorem** (from `OrthonormalBasis`):
    `⟪f, g⟫ = ∑_S ⟪f, χ_S⟫ · ⟪χ_S, g⟫`. -/
theorem plancherel_L2 (f g : L2Cube n) :
    @inner ℝ _ instInner f g =
      ∑ S : Finset (Fin n),
        @inner ℝ _ instInner f (parityBasis S) *
        @inner ℝ _ instInner (parityBasis S) g := by
  have := parityOrthonormalBasis.sum_inner_mul_inner f g
  simp only [parityOrthonormalBasis_apply] at this
  exact this.symm

/-- **Parseval's theorem** (from `OrthonormalBasis`):
    `∑_S ⟪f, χ_S⟫² = ‖f‖²`. -/
theorem parseval_L2 (f : L2Cube n) :
    ∑ S : Finset (Fin n), @inner ℝ _ instInner f (parityBasis S) ^ 2 = ‖f‖ ^ 2 := by
  have := parityOrthonormalBasis.sum_sq_inner_left f
  simp only [parityOrthonormalBasis_apply] at this
  exact this

/-- **Fourier coefficient = inner product** (from `OrthonormalBasis`):
    The `repr` coefficients are inner products with the basis vectors. -/
theorem repr_eq_inner (f : L2Cube n) (S : Finset (Fin n)) :
    (parityOrthonormalBasis.repr f).ofLp S = @inner ℝ _ instInner (parityBasis S) f := by
  change _ = inner ℝ (parityBasis S) f
  have := parityOrthonormalBasis.repr_apply_apply f S
  simp only [parityOrthonormalBasis_apply] at this
  exact this

end L2Cube

end BooleanAnalysis
