/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SecondPowerIntersection
public import OnLeConjecture.Analytic.WeightedIntersectionStrictAnyOrder

/-!
# Unit factors in weighted intersection estimates

Multiplying the first generator by an analytic unit preserves the
intersection ideal. The weighted estimates therefore apply to a
Weierstrass polynomial multiplied by its preparation unit. No claim about
preserving its Jacobian divisor under this multiplication is made.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- Multiplication of the first germ by a unit leaves the intersection
ideal unchanged. -/
theorem pairIdeal_unit_mul_left (U f g : Germ 2) (hU : IsUnit U) :
    pairIdeal (U * f) g = pairIdeal f g := by
  simp only [pairIdeal_eq_span, Ideal.span_insert,
    Ideal.span_singleton_mul_left_unit hU]

/-- Finite intersection is unchanged by a unit in the first generator. -/
theorem hasFiniteIntersection_unit_mul_left_iff
    (U f g : Germ 2) (hU : IsUnit U) :
    HasFiniteIntersection (U * f) g ↔ HasFiniteIntersection f g := by
  rw [HasFiniteIntersection, HasFiniteIntersection, pairIdeal_unit_mul_left U f g hU]

/-- The complex dimensions of the actual local algebras agree after
multiplication of the first germ by a unit. -/
theorem intersectionMultiplicity_unit_mul_left
    (U f g : Germ 2) (hU : IsUnit U)
    (hfinite : HasFiniteIntersection (U * f) g)
    (hfinite' : HasFiniteIntersection f g) :
    intersectionMultiplicity (U * f) g hfinite = intersectionMultiplicity f g hfinite' := by
  change Module.finrank ℂ _ = Module.finrank ℂ _
  rw [pairIdeal_unit_mul_left U f g hU]

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic.Germ

/-- Multiplication by an analytic germ multiplies a specified weighted
initial form by its value at the origin. -/
theorem mul_weighted_initial_tail
    (r D : ℕ) (hr : 0 < r) (U f : Germ 2)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![r, 1] D)
    (htail : f - coordinatePolynomialAlgHom 2 P ∈ weightedOrderIdeal r (D + 1)) :
    U * f - coordinatePolynomialAlgHom 2 (MvPolynomial.C (valueRingHom 2 U) * P) ∈
      weightedOrderIdeal r (D + 1) := by
  have hU : U - constRingHom 2 (valueRingHom 2 U) ∈ weightedOrderIdeal r 1 := by
    rw [weightedOrderIdeal_one_eq_maximalIdeal r hr, mem_maximalIdeal_iff]
    simp only [map_sub, valueRingHom_const, sub_self]
  have hf : f ∈ weightedOrderIdeal r D := by
    have hsum := (weightedOrderIdeal r D).add_mem
      (weightedOrderIdeal_antitone r D (D + 1) hr (by omega) htail)
      (coordinatePolynomial_mem_weightedOrderIdeal r D hr hP)
    simpa only [sub_add_cancel] using hsum
  have hfirst := weightedOrderIdeal_mul_mem r 1 D hr hU hf
  have hsecond := Ideal.mul_mem_left (weightedOrderIdeal r (D + 1))
    (constRingHom 2 (valueRingHom 2 U)) htail
  have heq : U * f - coordinatePolynomialAlgHom 2
      (MvPolynomial.C (valueRingHom 2 U) * P) =
    (U - constRingHom 2 (valueRingHom 2 U)) * f +
      constRingHom 2 (valueRingHom 2 U) * (f - coordinatePolynomialAlgHom 2 P) := by
    rw [map_mul, coordinatePolynomialAlgHom_C]
    ring
  rw [heq]
  exact (weightedOrderIdeal r (D + 1)).add_mem
    (by simpa [Nat.add_comm] using hfirst) hsecond

/-- The weak weighted intersection bound retains an arbitrary analytic
Weierstrass preparation unit in the first germ. -/
theorem weighted_intersection_unit_lower_bound_any_order
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (U H : Germ 2) (hU : IsUnit U) (hH : H ∈ weightedOrderIdeal r L)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (U * firstCoordinatePolynomialEvaluation P) H) :
    m * L ≤ PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) H hfinite := by
  have hfinite' := (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff
    U (firstCoordinatePolynomialEvaluation P) H hU).mp hfinite
  rw [PlaneCurve.intersectionMultiplicity_unit_mul_left
    U (firstCoordinatePolynomialEvaluation P) H hU hfinite hfinite']
  exact weighted_intersection_lower_bound_any_order r L m hr hm P hP hPm hcoeff H hH hfinite'

/-- The strict estimate uses initial forms of the actual unit-multiplied
first germ. Its initial form need not equal the bare polynomial's initial
form, and the unit is not removed from any Jacobian hypothesis. -/
theorem weighted_intersection_unit_strict_lower_bound_any_order
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (U H : Germ 2) (hU : IsUnit U) (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : U * firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hHtail : H - coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) H)
    (z : ℂ) (hProot : MvPolynomial.eval ![z, 1] P₀ = 0)
    (hHroot : MvPolynomial.eval ![z, 1] H₀ = 0) :
    m * L < PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) H hfinite := by
  obtain ⟨u, rfl⟩ := hU
  let V : Germ 2 := ↑u⁻¹
  let c : ℂ := valueRingHom 2 V
  have hc : c ≠ 0 := valueRingHom_ne_zero_of_isUnit (Units.isUnit u⁻¹)
  have hbareTail := mul_weighted_initial_tail r (r * m) hr V
    ((u : Germ 2) * firstCoordinatePolynomialEvaluation P) P₀ hP₀ hPtail
  have hcancel : V * ((u : Germ 2) * firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation P := by
    dsimp only [V]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hcancel] at hbareTail
  have hbareNe : MvPolynomial.C c * P₀ ≠ 0 :=
    mul_ne_zero (by simpa only [ne_eq, MvPolynomial.C_eq_zero] using hc) hP₀ne
  have hfinite' := (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff
    (u : Germ 2) (firstCoordinatePolynomialEvaluation P) H u.isUnit).mp hfinite
  rw [PlaneCurve.intersectionMultiplicity_unit_mul_left
    (u : Germ 2) (firstCoordinatePolynomialEvaluation P) H u.isUnit hfinite hfinite']
  apply weighted_intersection_strict_lower_bound_any_order r L m hr hm P hP hPm hcoeff
    H (MvPolynomial.C c * P₀) H₀ (hP₀.C_mul c) hbareNe hH₀ hbareTail hHtail hfinite' z
  · simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, hProot, mul_zero]
  · exact hHroot

end OnLeConjecture.Analytic.Germ
