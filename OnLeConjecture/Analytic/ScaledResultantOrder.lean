/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResultantRootOrder
public import OnLeConjecture.Analytic.ParametricResultant

/-!
# Resultant orders under a weighted polynomial scaling

Weighted polynomial scaling extracts an exact power of the parameter from
the resultant. A common root of the residual polynomials makes the bound
strict. This argument does not require a Puiseux splitting field.

Applications must construct the scaled polynomials from the analytic
weighted-order bounds. That construction is not assumed to follow merely
from the notation used here.
-/

public section

namespace OnLeConjecture.Analytic.PolynomialResultant

open _root_.Polynomial

/-- An exact weighted scaling identity for the ordinary polynomial
resultant. -/
theorem resultant_weighted_scaleRoots
    {R : Type*} [CommRing R] [IsDomain R]
    (P Q : R[X]) (t : R) (ht : t ≠ 0) (r L : ℕ)
    (hL : r * Q.natDegree ≤ L) :
    (P.scaleRoots (t ^ r)).resultant
        (C (t ^ (L - r * Q.natDegree)) * Q.scaleRoots (t ^ r)) =
      t ^ (L * P.natDegree) * P.resultant Q := by
  have htPower : t ^ (L - r * Q.natDegree) ≠ 0 := pow_ne_zero _ ht
  have hscale := resultant_scaleRoots P Q (t ^ r)
  simp only [natDegree_scaleRoots] at hscale
  simp only [natDegree_C_mul htPower, natDegree_scaleRoots]
  rw [resultant_C_mul_right, hscale, ← mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
  have hexp : (L - r * Q.natDegree) * P.natDegree +
      r * (P.natDegree * Q.natDegree) = L * P.natDegree := by
    calc
      (L - r * Q.natDegree) * P.natDegree + r * (P.natDegree * Q.natDegree) =
          (L - r * Q.natDegree + r * Q.natDegree) * P.natDegree := by ring
      _ = L * P.natDegree := by rw [Nat.sub_add_cancel hL]
  rw [hexp]

end OnLeConjecture.Analytic.PolynomialResultant

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Scaling extracts an exact finite summand from the extended resultant
order, including when the residual resultant is zero. -/
theorem vanishingOrder_resultant_weighted_scaleRoots
    (P Q : Polynomial (Germ 1)) (r L : ℕ) (hL : r * Q.natDegree ≤ L) :
    vanishingOrder
        ((P.scaleRoots (coordinate (0 : Fin 1) ^ r)).resultant
          (C (coordinate (0 : Fin 1) ^ (L - r * Q.natDegree)) *
            Q.scaleRoots (coordinate (0 : Fin 1) ^ r))) =
      (L * P.natDegree : ℕ) + vanishingOrder (P.resultant Q) := by
  rw [PolynomialResultant.resultant_weighted_scaleRoots
    P Q (coordinate (0 : Fin 1)) coordinate_zero_ne_zero r L hL,
    vanishingOrder_mul, vanishingOrder_coordinate_pow]

/-- The weighted scaling identity implies the weak resultant bound. -/
theorem mul_le_vanishingOrder_resultant_weighted_scaleRoots
    (P Q : Polynomial (Germ 1)) (r L : ℕ) (hL : r * Q.natDegree ≤ L) :
    ((L * P.natDegree : ℕ) : ℕ∞) ≤ vanishingOrder
      ((P.scaleRoots (coordinate (0 : Fin 1) ^ r)).resultant
        (C (coordinate (0 : Fin 1) ^ (L - r * Q.natDegree)) *
          Q.scaleRoots (coordinate (0 : Fin 1) ^ r))) := by
  rw [vanishingOrder_resultant_weighted_scaleRoots P Q r L hL]
  exact le_self_add

/-- A common root after taking constant terms forces a strictly larger
resultant order in the weighted scaling identity. -/
theorem mul_lt_vanishingOrder_resultant_weighted_scaleRoots
    (P Q : Polynomial (Germ 1)) (r L : ℕ) (hL : r * Q.natDegree ≤ L)
    (hP : P.Monic) (z : ℂ)
    (hPz : (P.map (valueRingHom 1)).IsRoot z)
    (hQz : (Q.map (valueRingHom 1)).IsRoot z) :
    ((L * P.natDegree : ℕ) : ℕ∞) < vanishingOrder
      ((P.scaleRoots (coordinate (0 : Fin 1) ^ r)).resultant
        (C (coordinate (0 : Fin 1) ^ (L - r * Q.natDegree)) *
          Q.scaleRoots (coordinate (0 : Fin 1) ^ r))) := by
  have hvalue : valueRingHom 1 (P.resultant Q) = 0 :=
    PolynomialResultant.map_resultant_eq_zero_of_common_root
      P Q Q.natDegree hP le_rfl (valueRingHom 1) hPz hQz
  have horder : (1 : ℕ∞) ≤ vanishingOrder (P.resultant Q) := by
    rw [← vanishingOrder_coordinate, vanishingOrder_le_iff_dvd]
    rw [← Ideal.mem_span_singleton, ← maximalIdeal_one_eq_span_coordinate]
    exact mem_maximalIdeal_iff.mpr hvalue
  rw [vanishingOrder_resultant_weighted_scaleRoots P Q r L hL]
  have hnext : ((L * P.natDegree + 1 : ℕ) : ℕ∞) ≤
      ((L * P.natDegree : ℕ) : ℕ∞) + vanishingOrder (P.resultant Q) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_left horder
      (((L * P.natDegree : ℕ) : ℕ∞))
  have hstrict : ((L * P.natDegree : ℕ) : ℕ∞) <
      ((L * P.natDegree + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self (L * P.natDegree)
  exact hstrict.trans_le hnext

end OnLeConjecture.Analytic.Germ
