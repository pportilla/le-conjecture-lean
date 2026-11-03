/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightRamification
public import OnLeConjecture.Polynomial.CoordinatePowerDivisibility

/-!
# Separation of homogeneous polynomials by two weight order ideals

A nonzero homogeneous polynomial does not belong to the next weighted
order ideal. Ramification reduces this assertion to the proved one weight
statement, and coefficient recovery makes the reduction injective.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem eq_zero_of_isTwoWeightHomogeneous_coordinatePolynomial_mem_succ
    (a b D : ℕ) (ha : 0 < a) (hb : 0 < b) {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsWeightedHomogeneous ![a, b] D)
    (hmem : coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal a b (D + 1)) :
    P = 0 := by
  have hpull := secondCoordinatePowerGerm_pullback_mem_weightedOrderIdeal
    a b (D + 1) ha hb (coordinatePolynomialAlgHom 2 P) hmem
  rw [secondCoordinatePowerGerm_pullback_coordinatePolynomial] at hpull
  have hzero := eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ a D ha
    (isWeightedHomogeneous_secondCoordinatePower_substitution a b D P hP) hpull
  ext d
  rw [← OnLeConjecture.Polynomial.coeff_second_power_substitution b hb P d, hzero]
  simp

end OnLeConjecture.Analytic.Germ
