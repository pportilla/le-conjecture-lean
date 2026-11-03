/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RamifiedIntersection
public import OnLeConjecture.Analytic.TwoWeightInitialFormExistence
public import OnLeConjecture.Analytic.WeightedInitialFormFactor

/-!
# Two-weight ideals under an actual coordinate ramification

Raising the second source coordinate to the power `b` carries weighted
order for `(a,b)` to weighted order for `(a,1)`, with the same threshold.
The same substitution acts on the polynomial initial forms.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Positive ramification converts the two-weight analytic order bound
into the corresponding one-weight bound. -/
theorem secondCoordinatePowerGerm_pullback_mem_weightedOrderIdeal
    (a b D : ℕ) (ha : 0 < a) (hb : 0 < b) (f : Germ 2)
    (hf : f ∈ twoWeightOrderIdeal a b D) :
    (secondCoordinatePowerGerm b hb).pullbackRingHom f ∈ weightedOrderIdeal a D := by
  obtain ⟨c, hc⟩ := (mem_twoWeightOrderIdeal_iff a b D f).mp hf
  rw [← hc, map_sum]
  apply Ideal.sum_mem
  intro k _
  rw [map_mul]
  apply Ideal.mul_mem_left
  rw [twoWeightOrderGenerator, map_mul, map_pow, map_pow,
    secondCoordinatePowerGerm_pullback_zero, secondCoordinatePowerGerm_pullback_one,
    ← pow_mul]
  exact monomial_mem_weightedOrderIdeal_of_threshold a D k.1.1 (b * k.1.2) ha k.2

/-- Polynomial substitution agrees with the actual analytic pullback. -/
theorem secondCoordinatePowerGerm_pullback_coordinatePolynomial
    (b : ℕ) (hb : 0 < b) (P : MvPolynomial (Fin 2) ℂ) :
    (secondCoordinatePowerGerm b hb).pullbackRingHom (coordinatePolynomialAlgHom 2 P) =
      coordinatePolynomialAlgHom 2
        (MvPolynomial.aeval
          (![MvPolynomial.X 0, MvPolynomial.X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [coordinatePolynomialAlgHom_C, MvPolynomial.aeval_C]
    change (secondCoordinatePowerGerm b hb).pullbackRingHom (constRingHom 2 c) =
      coordinatePolynomialAlgHom 2 (MvPolynomial.C c)
    rw [PointedMapGerm.pullback_constRingHom, coordinatePolynomialAlgHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, coordinatePolynomialAlgHom_X, MvPolynomial.aeval_X]
    congr 1
    fin_cases i
    · change (secondCoordinatePowerGerm b hb).pullbackRingHom (coordinate (0 : Fin 2)) =
        coordinatePolynomialAlgHom 2 (MvPolynomial.X (0 : Fin 2))
      rw [secondCoordinatePowerGerm_pullback_zero, coordinatePolynomialAlgHom_X]
    · change (secondCoordinatePowerGerm b hb).pullbackRingHom (coordinate (1 : Fin 2)) =
        coordinatePolynomialAlgHom 2 (MvPolynomial.X (1 : Fin 2) ^ b)
      rw [secondCoordinatePowerGerm_pullback_one, map_pow, coordinatePolynomialAlgHom_X]

/-- The polynomial initial form has the same degree after converting
the second source weight into a coordinate power. -/
theorem isWeightedHomogeneous_secondCoordinatePower_substitution
    (a b D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, b] D) :
    MvPolynomial.IsWeightedHomogeneous ![a, 1]
      (MvPolynomial.aeval
        (![MvPolynomial.X 0, MvPolynomial.X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) P) D := by
  change MvPolynomial.IsWeightedHomogeneous ![a, 1]
    (MvPolynomial.bind₁
      (![MvPolynomial.X 0, MvPolynomial.X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) P) D
  have hvars : ∀ i : Fin 2,
      MvPolynomial.IsWeightedHomogeneous ![a, 1]
        (![MvPolynomial.X 0, MvPolynomial.X 1 ^ b] i : MvPolynomial (Fin 2) ℂ)
          (1 * ![a, b] i) := by
    intro i
    fin_cases i
    · simpa using MvPolynomial.isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 0
    · simpa using (MvPolynomial.isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 1).pow b
  simpa only [one_mul] using
    OnLeConjecture.Analytic.MvPolynomial.IsWeightedHomogeneous.bind₁_scaled hP
    (![MvPolynomial.X 0, MvPolynomial.X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) hvars

/-- Both the analytic divisor and the strict initial-form tail pass
through ramification. -/
theorem second_power_dvd_ramified_twoWeight_initial_form
    (a b D N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (f : Germ 2) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, b] D)
    (htail : f - coordinatePolynomialAlgHom 2 P ∈ twoWeightOrderIdeal a b (D + 1))
    (hdiv : coordinate (1 : Fin 2) ^ N ∣ f) :
    MvPolynomial.X (1 : Fin 2) ^ (b * N) ∣
      MvPolynomial.aeval
        (![MvPolynomial.X 0, MvPolynomial.X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) P := by
  have htail' := secondCoordinatePowerGerm_pullback_mem_weightedOrderIdeal
    a b (D + 1) ha hb (f - coordinatePolynomialAlgHom 2 P) htail
  rw [map_sub, secondCoordinatePowerGerm_pullback_coordinatePolynomial] at htail'
  have hdiv' := map_dvd (secondCoordinatePowerGerm b hb).pullbackRingHom hdiv
  rw [map_pow, secondCoordinatePowerGerm_pullback_one, ← pow_mul] at hdiv'
  exact secondVariable_pow_dvd_of_dvd_weighted_initial_form
    a D (b * N) ((secondCoordinatePowerGerm b hb).pullbackRingHom f)
      (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1 ^ b] P)
      (isWeightedHomogeneous_secondCoordinatePower_substitution a b D P hP) htail' hdiv'

end OnLeConjecture.Analytic.Germ
