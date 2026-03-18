/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger

# Chapter 1: Boolean functions and the Fourier expansion — Internal lemmas

Technical helper lemmas for the Fourier expansion theory. These support the
main results in `BooleanAnalysis.FourierExpansion` but are not intended for
direct use by downstream code.
-/

import BooleanAnalysis.FourierExpansion.Defs

namespace BooleanAnalysis.Internal

open Finset BigOperators BooleanAnalysis

variable {n : ℕ}

/-- `χ(0) = 1`. -/
@[simp]
theorem chi_zero : chi (0 : ZMod 2) = 1 := by
  unfold chi; norm_num

/-- `χ(1) = -1`. -/
@[simp]
theorem chi_one : chi (1 : ZMod 2) = -1 := by
  unfold chi; norm_num

/-- `χ(b)² = 1` for all `b : ZMod 2`. -/
theorem chi_sq (b : ZMod 2) : chi b ^ 2 = 1 := by
  fin_cases b <;> (unfold chi; split_ifs <;> norm_num)

/-- `χ(b) = 1` or `χ(b) = -1`. -/
theorem chi_eq_one_or_neg_one (b : ZMod 2) : chi b = 1 ∨ chi b = -1 := by
  fin_cases b
  · left; exact chi_zero
  · right; exact chi_one

/-- Every element of `ZMod 2` is `0` or `1`. -/
private theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left; rwa [ZMod.val_eq_zero] at h
  · right; exact Fin.ext h

/-- `χ` is multiplicative: `χ(a + b) = χ(a) · χ(b)`. -/
theorem chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [chi, show (1 : ZMod 2) + 1 = 0 from Fin.ext (by decide)]

/-- `χ(b) ≠ 0` for all `b : ZMod 2`. -/
theorem chi_ne_zero (b : ZMod 2) : chi b ≠ 0 := by
  rcases chi_eq_one_or_neg_one b with h | h <;> simp [h]

/-- The parity function on the empty set is the constant function 1. -/
@[simp]
theorem parityFun_empty : parityFun (∅ : Finset (Fin n)) = fun _ => 1 := by
  ext x; simp [parityFun]

/-- Parity functions are multiplicative: `χ_S(x + y) = χ_S(x) · χ_S(y)`.
    (Equation 1.5 in the book) -/
theorem parityFun_add (S : Finset (Fin n)) (x y : Cube n) :
    parityFun S (x + y) = parityFun S x * parityFun S y := by
  simp only [parityFun]
  rw [← Finset.prod_mul_distrib]
  congr 1; ext i; exact chi_add (x i) (y i)

/-- `χ_S(x)² = 1` for all `S` and `x`. -/
theorem parityFun_sq (S : Finset (Fin n)) (x : Cube n) :
    parityFun S x ^ 2 = 1 := by
  simp only [parityFun, ← Finset.prod_pow]
  simp [chi_sq]

/-- `χ_S(0) = 1`. -/
@[simp]
theorem parityFun_zero (S : Finset (Fin n)) : parityFun S 0 = 1 := by
  simp [parityFun, chi_zero]

end BooleanAnalysis.Internal
