/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedIntersectionStrict
public import OnLeConjecture.Polynomial.WeightedChartInjectivity

/-!
# The initial form of a monic weighted Weierstrass polynomial

Coefficientwise scaling yields a monic polynomial over the one-variable
analytic germ ring. Its residue polynomial is the chart of the constructed
weighted initial form. Zero coefficients and coefficients attaining their
prescribed weighted order therefore determine the corresponding chart
coefficients.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- A specified initial form of a scaled monic polynomial has chart equal
to the residue of the scaled polynomial. -/
theorem weighted_initial_chart_eq_scaled_residue
    (r m : ℕ) (hr : 0 < r) (P A : Polynomial (Germ 1))
    (hAm : A.natDegree = m)
    (hscale : P = A.scaleRoots (coordinate (0 : Fin 1) ^ r))
    (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m))
    (htail : firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1)) :
    MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀ = A.map (valueRingHom 1) := by
  apply Polynomial.funext
  intro z
  have hlineTail := weightedLineMapGerm_pullback_mem_maximalIdeal_pow
    r (r * m + 1) hr ![z, 1] htail
  have hline : (weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
      (firstCoordinatePolynomialEvaluation P) =
        coordinate (0 : Fin 1) ^ (r * m) * A.eval (constRingHom 1 z) := by
    rw [weightedLineMapGerm_pullback_polynomial, hscale, Polynomial.scaleRoots_eval_mul,
      ← pow_mul, hAm]
  have hvalue := value_divided_coefficient_eq_of_initial_congruence
    ((weightedLineMapGerm r hr ![z, 1]).pullbackRingHom
      (firstCoordinatePolynomialEvaluation P))
    (A.eval (constRingHom 1 z)) (r * m) (MvPolynomial.eval ![z, 1] P₀) hline (by
      simpa only [map_sub, weightedLineMapGerm_pullback_coordinatePolynomial r (r * m) hr _ hP₀,
        mul_comm] using hlineTail)
  rw [OnLeConjecture.Polynomial.eval_weighted_chart]
  have heval := Polynomial.eval_map_apply (p := A) (valueRingHom 1) (constRingHom 1 z)
  simpa only [valueRingHom_const] using hvalue.symm.trans heval.symm

/-- The residue of a divided coefficient is nonzero whenever the original
coefficient attains exactly the extracted coordinate order. -/
theorem divided_coefficient_value_ne_zero_of_exact_order
    (b c : Germ 1) (d : ℕ) (hfactor : b = coordinate (0 : Fin 1) ^ d * c)
    (horder : vanishingOrder b = (d : ℕ∞)) :
    valueRingHom 1 c ≠ 0 := by
  intro hzero
  have hc : c ∈ maximalIdeal 1 := mem_maximalIdeal_iff.mpr hzero
  have hnext : b ∈ maximalIdeal 1 ^ (d + 1) := by
    rw [hfactor, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) d) hc
  have hbound := mem_maximalIdeal_one_pow_iff.mp hnext
  rw [horder] at hbound
  have hbad : d + 1 ≤ d := by exact_mod_cast hbound
  omega

/-- Weighted coefficient bounds construct a nonzero initial form whose
chart is monic of the Weierstrass degree. The chart retains zero
coefficients and detects every coefficient attaining its weighted bound. -/
theorem exists_monic_weierstrass_initial_form
    (r m : ℕ) (hr : 0 < r) (P : Polynomial (Germ 1))
    (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i))) :
    ∃ P₀ : MvPolynomial (Fin 2) ℂ,
      P₀ ≠ 0 ∧ P₀.IsWeightedHomogeneous ![r, 1] (r * m) ∧
      firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
        weightedOrderIdeal r (r * m + 1) ∧
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).Monic ∧
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).natDegree = m ∧
      (∀ i, P.coeff i = 0 →
        (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).coeff i = 0) ∧
      (∀ i, vanishingOrder (P.coeff i) = ((r * (m - i) : ℕ) : ℕ∞) →
        (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).coeff i ≠ 0) := by
  have hcoeffAll : ∀ i, P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)) := by
    intro i
    by_cases hi : i < m
    · exact hcoeff i hi
    · simp [Nat.sub_eq_zero_of_le (by omega : m ≤ i)]
  obtain ⟨A, hA, hAm, hscale, hfactor⟩ :=
    exists_monic_weighted_polynomial_scaling P m r hP hPm hcoeffAll
  have hweighted : firstCoordinatePolynomialEvaluation P ∈ weightedOrderIdeal r (r * m) :=
    firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal r (r * m) hr P
      (by intro i; simpa only [Nat.mul_sub_left_distrib] using hcoeffAll i)
  obtain ⟨P₀, hP₀, htail⟩ := exists_weightedHomogeneous_coordinatePolynomial_mod_succ
    r (r * m) hr (firstCoordinatePolynomialEvaluation P) hweighted
  have hchart := weighted_initial_chart_eq_scaled_residue r m hr P A hAm hscale P₀ hP₀ htail
  have hmonic : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).Monic := by
    rw [hchart]
    exact hA.map (valueRingHom 1)
  have hnonzero : P₀ ≠ 0 := by
    intro hzero
    apply hmonic.ne_zero
    simp [hzero]
  refine ⟨P₀, hnonzero, hP₀, htail, hmonic, ?_, ?_, ?_⟩
  · rw [hchart, hA.natDegree_map, hAm]
  · intro i hi
    have hAi : A.coeff i = 0 := by
      have hproduct := hfactor i
      rw [hi] at hproduct
      exact (mul_eq_zero.mp hproduct.symm).resolve_left
        (pow_ne_zero _ coordinate_zero_ne_zero)
    rw [hchart, coeff_map, hAi, map_zero]
  · intro i hi
    rw [hchart, coeff_map]
    exact divided_coefficient_value_ne_zero_of_exact_order
      (P.coeff i) (A.coeff i) (r * (m - i)) (hfactor i) hi

/-- A depressed Weierstrass polynomial with a coefficient attaining its
Newton bound has a depressed monic initial chart different from `X^m`. -/
theorem exists_depressed_nontrivial_monic_weierstrass_initial_form
    (r m : ℕ) (hr : 0 < r) (P : Polynomial (Germ 1))
    (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (hdepressed : P.coeff (m - 1) = 0)
    (hsharp : ∃ i, i < m ∧ vanishingOrder (P.coeff i) = ((r * (m - i) : ℕ) : ℕ∞)) :
    ∃ P₀ : MvPolynomial (Fin 2) ℂ,
      P₀ ≠ 0 ∧ P₀.IsWeightedHomogeneous ![r, 1] (r * m) ∧
      firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
        weightedOrderIdeal r (r * m + 1) ∧
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).Monic ∧
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).natDegree = m ∧
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀).coeff (m - 1) = 0 ∧
      MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀ ≠ X ^ m := by
  obtain ⟨P₀, hnonzero, hP₀, htail, hmonic, hdegree, hzero, hexact⟩ :=
    exists_monic_weierstrass_initial_form r m hr P hP hPm hcoeff
  refine ⟨P₀, hnonzero, hP₀, htail, hmonic, hdegree, hzero (m - 1) hdepressed, ?_⟩
  intro hpure
  obtain ⟨i, him, hi⟩ := hsharp
  have hnonzeroCoeff := hexact i hi
  rw [hpure, coeff_X_pow, if_neg (by omega : i ≠ m)] at hnonzeroCoeff
  exact hnonzeroCoeff rfl

end OnLeConjecture.Analytic.Germ
