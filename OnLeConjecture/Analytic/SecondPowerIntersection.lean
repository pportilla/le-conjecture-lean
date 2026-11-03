/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedIntersectionBound

/-!
# Multiplication by a coordinate power in an intersection pair

For a distinguished monic polynomial of degree `m`, multiplying the other
analytic germ by `y^K` adds `m K` to the intersection number. This permits
weighted intersection estimates without a lower bound on the weighted
order of the second germ relative to the first.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Multiplication by a power of the second coordinate preserves finite
intersection with a distinguished monic polynomial and adds its degree
times that power to the intersection multiplicity. -/
theorem exists_finite_intersection_second_power_mul_eq
    (m K : ℕ) (hm : 0 < m) (P : Polynomial (Germ 1))
    (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1)
    (H : Germ 2)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H) :
    ∃ hfinite' : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
        (coordinate (1 : Fin 2) ^ K * H),
      PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
        (coordinate (1 : Fin 2) ^ K * H) hfinite' =
      m * K + PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation P) H hfinite := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨R, hR⟩ := exists_polynomial_mod_distinguished d P hP hPm hdist H
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hR
  have hdivision : H = firstCoordinatePolynomialEvaluation P * q +
      firstCoordinatePolynomialEvaluation R := by
    rw [← hq]
    ring
  obtain ⟨hinter, hres⟩ := intersectionMultiplicity_eq_remainder_resultant_order
    (d + 1) (by omega) P R hP hPm hdist H q hdivision hfinite
  let c := coordinate (0 : Fin 1) ^ K
  have hc : c ≠ 0 := pow_ne_zero _ coordinate_zero_ne_zero
  have hresmul : P.resultant (C c * R) =
      coordinate (0 : Fin 1) ^ ((d + 1) * K) * P.resultant R := by
    simp only [natDegree_C_mul hc]
    rw [resultant_C_mul_right, hPm]
    simp only [c, ← pow_mul, Nat.mul_comm]
  have hresmulNe : P.resultant (C c * R) ≠ 0 := by
    rw [hresmul]
    exact mul_ne_zero (pow_ne_zero _ coordinate_zero_ne_zero) hres
  have hfiniteR := hasFiniteIntersection_of_resultant_ne_zero
    d P (C c * R) hP hPm hdist hresmulNe
  have heval : firstCoordinatePolynomialEvaluation (C c * R) =
      coordinate (1 : Fin 2) ^ K * firstCoordinatePolynomialEvaluation R := by
    rw [firstCoordinatePolynomialEvaluation, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    change hyperplaneExtension 1 (coordinate (0 : Fin 1) ^ K) * _ = _
    rw [map_pow, hyperplaneExtension_coordinate_plane]
    rfl
  have hdivision' : coordinate (1 : Fin 2) ^ K * H =
      firstCoordinatePolynomialEvaluation P * (coordinate (1 : Fin 2) ^ K * q) +
        firstCoordinatePolynomialEvaluation (C c * R) := by
    rw [hdivision, heval]
    ring
  have hideal := PlaneCurve.pairIdeal_eq_of_remainder
    (firstCoordinatePolynomialEvaluation P) (coordinate (1 : Fin 2) ^ K * H)
    (firstCoordinatePolynomialEvaluation (C c * R))
    (coordinate (1 : Fin 2) ^ K * q) hdivision'
  have hfinite' := hfiniteR.of_pairIdeal_eq hideal.symm
  refine ⟨hfinite', ?_⟩
  obtain ⟨hinter', _⟩ := intersectionMultiplicity_eq_remainder_resultant_order
    (d + 1) (by omega) P (C c * R) hP hPm hdist
    (coordinate (1 : Fin 2) ^ K * H) (coordinate (1 : Fin 2) ^ K * q)
    hdivision' hfinite'
  rw [hinter', hinter, hresmul, vanishingOrder_mul, vanishingOrder_coordinate_pow,
    ENat.toNat_add (ENat.natCast_ne_top _) (vanishingOrder_eq_top_iff.not.mpr hres)]
  simp

/-- The weak weighted intersection estimate for every threshold `L`,
without assuming that it exceeds the weight of the first polynomial. -/
theorem weighted_intersection_lower_bound_any_order
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (H : Germ 2) (hH : H ∈ weightedOrderIdeal r L)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H) :
    m * L ≤ PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation P) H hfinite := by
  let K := r * m
  obtain ⟨hfinite', hinter⟩ := exists_finite_intersection_second_power_mul_eq m K hm P hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds r m hr P hcoeff) H hfinite
  have hcoordinate : coordinate (1 : Fin 2) ^ K ∈ weightedOrderIdeal r K := by
    simpa only [pow_zero, one_mul, Nat.mul_zero, zero_add] using
      monomial_mem_weightedOrderIdeal_of_threshold r K 0 K hr (by simp)
  have horder : coordinate (1 : Fin 2) ^ K * H ∈ weightedOrderIdeal r (K + L) :=
    weightedOrderIdeal_mul_mem r K L hr hcoordinate hH
  have hbound := weighted_intersection_lower_bound r (K + L) m hr hm
    (by dsimp only [K]; omega) P hP hPm hcoeff
      (coordinate (1 : Fin 2) ^ K * H) horder hfinite'
  rw [hinter, Nat.mul_add] at hbound
  omega

end OnLeConjecture.Analytic.Germ
