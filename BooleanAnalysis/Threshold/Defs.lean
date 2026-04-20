/-
Copyright (c) 2026 Aleksei Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov

# Chapter 5: Majority and threshold functions — Definitions
-/

import BooleanAnalysis.FourierExpansion.Defs

namespace BooleanAnalysis

open Finset BigOperators

variable {n : ℕ}

/-! ### §5.1 Linear threshold functions -/

/-- A Boolean function `f` is a Linear Threshold Function (LTF) if it can be represented
    as the sign of a degree-1 polynomial.
    (Definition 5.1 in O'Donnell) -/
def IsLTF (f : BooleanFunction n) : Prop :=
  ∃ (w : Fin n → ℝ) (θ : ℝ), ∀ x : Cube n,
    f x = if (∑ i, w i * chi (x i)) ≥ θ then 1 else -1

end BooleanAnalysis
