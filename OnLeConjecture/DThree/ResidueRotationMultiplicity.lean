/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ResidueRotationCollision
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Multiplicity on a residual rotation component

The restricted third difference on a rotation component is a nonzero scalar
multiple of the dehomogenized third form. This file records its exact root
multiplicity and its local polynomial factorization.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Multiplication by the nonzero rotation character does not change the
root multiplicity. -/
theorem rotationRestrictedDifference_rootMultiplicity
    {zeta : ℂ} {r : ℕ} {p : ℂ[X]} {x : ℂ}
    (hzeta : zeta ^ r ≠ 1) (hp : p ≠ 0) :
    (rotationRestrictedDifference zeta r p).rootMultiplicity x =
      p.rootMultiplicity x := by
  have hscalar : (1 - zeta ^ r : ℂ) ≠ 0 :=
    sub_ne_zero.mpr hzeta.symm
  have hconstant : C (1 - zeta ^ r) ≠ (0 : ℂ[X]) :=
    C_ne_zero.mpr hscalar
  rw [rotationRestrictedDifference_eq,
    rootMultiplicity_mul (mul_ne_zero hconstant hp),
    rootMultiplicity_C, zero_add]

/-- At a root, the restricted difference is a positive power of the local
linear factor times a polynomial that does not vanish there. -/
theorem exists_rotationRestrictedDifference_local_factorization
    {zeta : ℂ} {r : ℕ} {p : ℂ[X]} {x : ℂ}
    (hzeta : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      ∃ quotient : ℂ[X],
        rotationRestrictedDifference zeta r p =
          (X - C x) ^ multiplicity * quotient ∧
        quotient.eval x ≠ 0 := by
  let difference := rotationRestrictedDifference zeta r p
  have hdifference : difference ≠ 0 := by
    dsimp only [difference]
    rw [rotationRestrictedDifference_eq]
    exact mul_ne_zero (C_ne_zero.mpr (sub_ne_zero.mpr hzeta.symm)) hp
  have hxDifference : difference.IsRoot x := by
    dsimp only [difference]
    rw [rotationRestrictedDifference_eq]
    change (C (1 - zeta ^ r) * p).eval x = 0
    rw [eval_mul, eval_C, hx,
      mul_zero]
  let multiplicity := difference.rootMultiplicity x
  let quotient := difference /ₘ (X - C x) ^ multiplicity
  refine ⟨multiplicity, ?_, quotient, ?_, ?_⟩
  · exact (rootMultiplicity_pos hdifference).2 hxDifference
  · simpa only [difference, multiplicity, quotient] using
      (pow_mul_divByMonic_rootMultiplicity_eq difference x).symm
  · simpa only [difference, multiplicity, quotient] using
      eval_divByMonic_pow_rootMultiplicity_ne_zero x hdifference

/-- The multiplicity in the local factorization equals the multiplicity of
the dehomogenized third form. -/
theorem exists_rotationRestrictedDifference_factorization_with_sourceMultiplicity
    {zeta : ℂ} {r : ℕ} {p : ℂ[X]} {x : ℂ}
    (hzeta : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    0 < p.rootMultiplicity x ∧
      ∃ quotient : ℂ[X],
        rotationRestrictedDifference zeta r p =
          (X - C x) ^ p.rootMultiplicity x * quotient ∧
        quotient.eval x ≠ 0 := by
  have hpositive : 0 < p.rootMultiplicity x :=
    (rootMultiplicity_pos hp).2 hx
  let difference := rotationRestrictedDifference zeta r p
  have hdifference : difference ≠ 0 := by
    dsimp only [difference]
    rw [rotationRestrictedDifference_eq]
    exact mul_ne_zero (C_ne_zero.mpr (sub_ne_zero.mpr hzeta.symm)) hp
  have hmultiplicity : difference.rootMultiplicity x = p.rootMultiplicity x :=
    rotationRestrictedDifference_rootMultiplicity hzeta hp
  let quotient := difference /ₘ (X - C x) ^ difference.rootMultiplicity x
  refine ⟨hpositive, quotient, ?_, ?_⟩
  · simpa only [difference, quotient, hmultiplicity] using
      (pow_mul_divByMonic_rootMultiplicity_eq difference x).symm
  · simpa only [difference, quotient] using
      eval_divByMonic_pow_rootMultiplicity_ne_zero x hdifference

end OnLeConjecture.DThree
