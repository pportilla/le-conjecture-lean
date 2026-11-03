/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedIntersectionStrict
public import OnLeConjecture.Analytic.SecondPowerIntersection

/-!
# Strict weighted intersection bounds at every second degree

Multiplication of the second germ by a coordinate power preserves the
initial root in the chart `y = 1`. The exact change of intersection
multiplicity removes the restriction on its weighted degree.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The strict weighted intersection bound from a common initial root,
with no lower bound on the weighted degree of the second germ. -/
theorem weighted_intersection_strict_lower_bound_any_order
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : _root_.Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (H : Germ 2) (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H)
    (z : ℂ) (hProot : MvPolynomial.eval ![z, 1] P₀ = 0)
    (hHroot : MvPolynomial.eval ![z, 1] H₀ = 0) :
    m * L < PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation P) H hfinite := by
  let K := r * m
  obtain ⟨hfinite', hinter⟩ := exists_finite_intersection_second_power_mul_eq m K hm P hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds r m hr P hcoeff) H hfinite
  have hY : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![r, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![r, 1] 1
  have hYK : (MvPolynomial.X (1 : Fin 2) ^ K : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![r, 1] K := by
    simpa using hY.pow K
  have hcoordinate : coordinate (1 : Fin 2) ^ K ∈ weightedOrderIdeal r K := by
    simpa only [map_pow, coordinatePolynomialAlgHom_X] using
      coordinatePolynomial_mem_weightedOrderIdeal r K hr hYK
  have htail : coordinate (1 : Fin 2) ^ K * H -
      coordinatePolynomialAlgHom 2 (MvPolynomial.X (1 : Fin 2) ^ K * H₀) ∈
      weightedOrderIdeal r (K + L + 1) := by
    have hproduct := weightedOrderIdeal_mul_mem r K (L + 1) hr hcoordinate hHtail
    simpa only [map_mul, map_pow, coordinatePolynomialAlgHom_X, mul_sub,
      Nat.add_assoc] using hproduct
  have hroot : MvPolynomial.eval ![z, 1]
      (MvPolynomial.X (1 : Fin 2) ^ K * H₀) = 0 := by
    simp [hHroot]
  have hbound := weighted_intersection_strict_lower_bound_of_initial_common_root
    r (K + L) m hr hm (by dsimp only [K]; omega) P hP hPm hcoeff
    (coordinate (1 : Fin 2) ^ K * H) P₀ (MvPolynomial.X (1 : Fin 2) ^ K * H₀)
    hP₀ hP₀ne (hYK.mul hH₀) hPtail htail hfinite' z hProot hroot
  rw [hinter, Nat.mul_add] at hbound
  omega

end OnLeConjecture.Analytic.Germ
