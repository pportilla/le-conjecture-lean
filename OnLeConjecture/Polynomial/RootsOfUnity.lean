/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# A nontrivial complex root of unity

This file formalizes the root selection used in the final collision argument
for the case of order two.
-/

public section

namespace OnLeConjecture.Polynomial

/-- If `a ≥ 2` divides both `k` and `L`, there is a complex number different
from one whose `k`th and `L`th powers are one. -/
theorem exists_nontrivial_root_fixed_by_multiples
    (a k L : ℕ) (ha : 2 ≤ a) (hak : a ∣ k) (haL : a ∣ L) :
    ∃ η : ℂ, η ≠ 1 ∧ η ^ k = 1 ∧ η ^ L = 1 := by
  let η := Complex.exp (2 * Real.pi * Complex.I / a)
  have hprimitive : IsPrimitiveRoot η a :=
    Complex.isPrimitiveRoot_exp a (by omega)
  refine ⟨η, hprimitive.ne_one ha, ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := hak
    rw [pow_mul, hprimitive.pow_eq_one, one_pow]
  · obtain ⟨q, rfl⟩ := haL
    rw [pow_mul, hprimitive.pow_eq_one, one_pow]

end OnLeConjecture.Polynomial
