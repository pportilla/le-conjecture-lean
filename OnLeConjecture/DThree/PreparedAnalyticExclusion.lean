/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.AnalyticThirdElimination

/-!
# Analytic exclusion for prepared cubic and quartic components

The cubic and quartic weighted initial forms are classified using their
analytic Jacobian divisor. Applying that classification to an auxiliary
third coordinate proves that the first pair has no injective representative.
Finite analytic elimination then excludes an injective triple without any
assumption on its third initial form. Finally, the initial scalar unit of a
prepared depressed cubic is removed by a constant target rescaling.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

private theorem e_coordinate_tail_exclusion
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (hzero : g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a 0 3) ∈ Germ.weightedOrderIdeal a (3 * a + 1))
    (hone : g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a 1 0 0 4 0) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (htwo : g.1.component 2 - Germ.coordinate (1 : Fin 2) ∈
      Germ.weightedOrderIdeal a 2) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨f, hf, hfzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply eWeightedOrderTails_not_hasInjectiveRepresentative a 1 1 ha one_pos one_ne_zero
    f hf hfzero
  intro i
  rw [hcomponents i]
  fin_cases i
  · simpa [eResiduePolynomialMap, residueWeightedDegrees, weightedCubicPolynomial]
      using hzero
  · have hpolynomial : eResiduePolynomialMap a 1 1 1 =
        weightedQuarticPolynomial a 1 0 0 4 0 := by
      simp [eResiduePolynomialMap, weightedQuarticPolynomial]
      ring
    simpa [hpolynomial, residueWeightedDegrees] using hone
  · simpa [eResiduePolynomialMap, residueWeightedDegrees] using htwo

private theorem h_coordinate_tail_exclusion
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (hzero : g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a 3 0) ∈ Germ.weightedOrderIdeal a (3 * a + 1))
    (hone : g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a 1 0 4 0 2) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (htwo : g.1.component 2 - Germ.coordinate (1 : Fin 2) ∈
      Germ.weightedOrderIdeal a 2) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨f, hf, hfzero, hg, hcomponents⟩ :=
    PointedMapGerm.exists_pairRepresentative_with_components g
  rw [hg]
  apply hWeightedOrderTails_not_hasInjectiveRepresentative a 1 1 ha one_pos one_ne_zero
    f hf hfzero
  intro i
  rw [hcomponents i]
  fin_cases i
  · have hpolynomial : hResiduePolynomialMap a 1 1 0 =
        weightedCubicPolynomial a 3 0 := by
      simp [hResiduePolynomialMap, weightedCubicPolynomial]
      ring
    simpa [hpolynomial, residueWeightedDegrees] using hzero
  · have hpolynomial : hResiduePolynomialMap a 1 1 1 =
        weightedQuarticPolynomial a 1 0 4 0 2 := by
      simp [hResiduePolynomialMap, weightedQuarticPolynomial]
      ring
    simpa [hpolynomial, residueWeightedDegrees] using hone
  · simpa [hResiduePolynomialMap, residueWeightedDegrees] using htwo

/-- The analytic Jacobian divisor classifies a nondegenerate cubic and
quartic pair and excludes every injective representative of that pair. -/
theorem classifiedWeightedPair_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 2) (a : ℕ) (ha : 0 < a)
    (A B c₄ c₃ c₂ c₁ c₀ : ℂ) (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (htailZero : g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a A B) ∈ Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne : g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1)) :
    ¬ g.HasInjectiveRepresentative := by
  intro hg
  obtain ⟨h, hInjective, hfirst, hsecond, hthird⟩ :=
    exists_injective_coordinate_augmentation g hg
  have hT : (formT : Form ℂ).IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  obtain ⟨s, k, _hs, _hequivalent, hInjectiveEquiv, _hT, hcase⟩ :=
    exists_rightLeft_weightedRescaling_to_E_or_H_of_analytic_initialForms
      h a 1 ha formT hT A B c₄ c₃ c₂ c₁ c₀ hAB hquartic
      (by simpa [hfirst] using htailZero)
      (by simpa [hsecond] using htailOne)
      (by simp [hthird, formT])
      (by simpa [hfirst, hsecond] using hdiv)
  have hscaled : rescaleForm s 1 formT = formT := by
    simp [rescaleForm_eq_C_mul_sourceRescaleFormAlgHom]
  rcases hcase with ⟨hzero, hone, htwo⟩ | ⟨hzero, hone, htwo⟩
  · rw [hscaled] at htwo
    exact e_coordinate_tail_exclusion k a ha hzero hone
      (by simpa [formT] using htwo) (hInjectiveEquiv.mpr hInjective)
  · rw [hscaled] at htwo
    exact h_coordinate_tail_exclusion k a ha hzero hone
      (by simpa [formT] using htwo) (hInjectiveEquiv.mpr hInjective)

/-- A finite cubic and quartic pair with the three analytic Jacobian
divisors excludes injectivity, with no prescribed third initial form. -/
theorem classifiedWeightedAnalyticTriple_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (hfinite : g.firstTwo.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a)
    (A B c₄ c₃ c₂ c₁ c₀ : ℂ) (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (htailZero : g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
      (weightedCubicPolynomial a A B) ∈ Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne : g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  apply classifiedWeightedAnalyticTriple_of_pair_noninjective
    g hfinite a ha A B c₄ c₃ c₂ c₁ c₀ hAB hquartic
    _ htailZero htailOne hdivZeroOne hdivZeroTwo hdivOneTwo
  exact classifiedWeightedPair_not_hasInjectiveRepresentative g.firstTwo a ha
    A B c₄ c₃ c₂ c₁ c₀ hAB hquartic
    (by simpa using htailZero) (by simpa using htailOne) (by simpa using hdivZeroOne)

/-- Scaling the first target coordinate by a nonzero constant preserves
finiteness of the first pair. -/
theorem firstTwo_monicFirstTargetRescaledMap_isFiniteAtOrigin
    (g : PointedMapGerm 2 3) (r : ℂ) (hr : r ≠ 0)
    (hfinite : g.firstTwo.IsFiniteAtOrigin) :
    (monicFirstTargetRescaledMap g r hr).firstTwo.IsFiniteAtOrigin := by
  let v : Fin 2 → ℂ := ![r⁻¹, 1]
  have hv : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i
    · exact inv_ne_zero hr
    · exact one_ne_zero
  let e := diagonalPointedEquiv v hv
  have heq : (monicFirstTargetRescaledMap g r hr).firstTwo =
      e.forward.comp g.firstTwo := by
    apply PointedMapGerm.ext_components
    intro i
    rw [PointedMapGerm.firstTwo_component, PointedMapGerm.component_comp_eq_pullback]
    change _ = g.firstTwo.pullbackRingHom
      ((diagonalPointedEquiv v hv).forward.1.component i)
    rw [diagonalPointedEquiv_component, map_mul,
      PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_coordinate]
    fin_cases i
    · simpa [v] using monicFirstTargetRescaledMap_component_zero g r hr
    · simpa [v] using monicFirstTargetRescaledMap_component_one g r hr
  rw [heq]
  exact (PointedMapGerm.isFiniteAtOrigin_targetEquiv_comp_iff g.firstTwo e).mpr hfinite

/-- Prepared depressed cubic and exact quartic components with a finite
first pair and the three analytic Jacobian divisors exclude injectivity.
No third weighted initial form or algebra exclusion is assumed. -/
theorem PointedMapGerm.preparedWeightedAnalyticTriple_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (hfinite : g.firstTwo.IsFiniteAtOrigin)
    (a : ℕ) (ha : 0 < a)
    (a₁ a₀ : Germ 1) (u : Germ 2)
    (hfirst : g.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
        Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) +
        Germ.planeCoefficientExtension a₀) * u)
    (hu : IsUnit u)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (hcubicExact : a₁ ∉ Germ.maximalIdeal 1 ^ (2 * a + 1) ∨
      a₀ ∉ Germ.maximalIdeal 1 ^ (3 * a + 1))
    (hquartic : g.1.component 1 ∈ Germ.weightedOrderIdeal a (4 * a))
    (hquarticExact : g.1.component 1 ∉ Germ.weightedOrderIdeal a (4 * a + 1))
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨A, B, c₄, c₃, c₂, c₁, c₀, hAB, hr, hQzero, hzeroRaw, honeRaw⟩ :=
    PointedMapGerm.exists_weightedCubicAndQuarticInitialForms_of_preparedComponents
      g a ha a₁ a₀ u hfirst hu ha₁ ha₀ hcubicExact hquartic hquarticExact
  let r := Germ.valueRingHom 2 u
  let P := weightedCubicPolynomial a A B
  let h := monicFirstTargetRescaledMap g r hr
  have hscalar : Germ.constRingHom 2 r⁻¹ * Germ.constRingHom 2 r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr, map_one]
  have hzero : h.1.component 0 - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (3 * a + 1) := by
    have heq : h.1.component 0 - Germ.coordinatePolynomialAlgHom 2 P =
        Germ.constRingHom 2 r⁻¹ *
          (g.1.component 0 - Germ.coordinatePolynomialAlgHom 2 (MvPolynomial.C r * P)) := by
      rw [monicFirstTargetRescaledMap_component_zero, map_mul,
        Germ.coordinatePolynomialAlgHom_C, mul_sub, ← mul_assoc, hscalar, one_mul]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hzeroRaw
  have hone : h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
      (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
      Germ.weightedOrderIdeal a (4 * a + 1) := by
    rw [monicFirstTargetRescaledMap_component_one]
    exact honeRaw
  have hnot := classifiedWeightedAnalyticTriple_not_hasInjectiveRepresentative
    h (firstTwo_monicFirstTargetRescaledMap_isFiniteAtOrigin g r hr hfinite)
    a ha A B c₄ c₃ c₂ c₁ c₀ hAB hQzero hzero hone
    (coordinate_pow_dvd_jacobian_monicFirstTarget_zero_one g r hr (6 * a - 1) hdivZeroOne)
    (coordinate_pow_dvd_jacobian_monicFirstTarget_zero_two g r hr (6 * a - 1) hdivZeroTwo)
    (coordinate_pow_dvd_jacobian_monicFirstTarget_one_two g r hr (6 * a - 1) hdivOneTwo)
  intro hg
  have hequivalent := rightLeftEquivalent_monicFirstTargetRescaledMap g r hr
  exact hnot (hequivalent.hasInjectiveRepresentative hg)

end OnLeConjecture.DThree
