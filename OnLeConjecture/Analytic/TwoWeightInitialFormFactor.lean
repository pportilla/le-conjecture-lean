/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightRamification
public import OnLeConjecture.Polynomial.CoordinatePowerDivisibility

/-!
# Coordinate factors of initial forms for two positive weights

Ramification reduces analytic coordinate divisibility to the corresponding
one-weight statement. Polynomial coefficient recovery descends the factor.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Analytic coordinate divisibility passes to the polynomial initial
form for any two positive integral source weights. -/
theorem secondVariable_pow_dvd_of_dvd_twoWeight_initial_form
    (a b D N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (f : Germ 2) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, b] D)
    (htail : f - coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal a b (D + 1))
    (hdiv : coordinate (1 : Fin 2) ^ N ∣ f) :
    MvPolynomial.X (1 : Fin 2) ^ N ∣ P :=
  OnLeConjecture.Polynomial.second_variable_pow_dvd_of_ramified_dvd b N hb P
    (second_power_dvd_ramified_twoWeight_initial_form a b D N ha hb f P hP htail hdiv)

end OnLeConjecture.Analytic.Germ
