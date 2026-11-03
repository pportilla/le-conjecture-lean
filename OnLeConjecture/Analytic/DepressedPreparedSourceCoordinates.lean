/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TransverseSmoothPreparation
public import OnLeConjecture.Analytic.OrderThreePreparation
public import OnLeConjecture.Analytic.PlaneElimination
public import OnLeConjecture.PlaneCurve.Tschirnhausen

/-!
# Depressed preparation relative to a smooth equation

For intersection order three or four, convergent preparation and a
parameter-preserving Tschirnhausen transformation construct a depressed
monic polynomial. The chosen smooth equation remains precisely the
second coordinate throughout the construction.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

private theorem preserves_second_of_preserves_coefficients
    (e : PointedEquivGerm 2)
    (he : ∀ q : Germ 1, e.pullbackAlgEquiv (planeCoefficientExtension q) =
      planeCoefficientExtension q) :
    e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 := by
  have h := he (coordinate (0 : Fin 1))
  simpa only [planeCoefficientExtension_apply, hyperplaneExtension_coordinate_plane,
    PointedEquivGerm.pullbackAlgEquiv_apply, PointedEquivGerm.pullbackRingEquiv_apply] using h

/-- The existing convergent cubic preparation produces an actual
distinguished polynomial with zero quadratic coefficient. -/
theorem exists_depressed_cubic_polynomial_preparation
    {f : Germ 2} (hregular : IsRegularInFirstCoordinateOfOrder f 3) :
    ∃ e : PointedEquivGerm 2, ∃ P : Polynomial (Germ 1), ∃ U : Germ 2,
      e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 ∧
      P.Monic ∧ P.natDegree = 3 ∧ P.coeff 2 = 0 ∧
      (∀ j, j < 3 → P.coeff j ∈ maximalIdeal 1) ∧ IsUnit U ∧
      e.forward.pullbackRingHom f = firstCoordinatePolynomialEvaluation P * U := by
  obtain ⟨e, a₁, a₀, U, ha₁, ha₀, hU, hfactor, hparameter⟩ :=
    exists_parameterPreserving_depressedCubicPreparation hregular
  refine ⟨e, cubicWeierstrassPolynomial 0 a₁ a₀, U,
    preserves_second_of_preserves_coefficients e hparameter,
    cubicWeierstrassPolynomial_monic _ _ _, cubicWeierstrassPolynomial_natDegree _ _ _,
    ?_, cubicWeierstrassPolynomial_coeff_mem_maximalIdeal (Ideal.zero_mem _) ha₁ ha₀, hU, ?_⟩
  · simp only [cubicWeierstrassPolynomial_coeff_of_lt _ _ _ 2 (by decide), if_true]
  · rw [firstCoordinatePolynomialEvaluation_cubicWeierstrassPolynomial]
    simpa only [monicCubic, map_zero, zero_mul, add_zero,
      PointedEquivGerm.pullbackAlgEquiv_apply,
      PointedEquivGerm.pullbackRingEquiv_apply] using hfactor

private theorem polynomialEvaluation_monic_quartic
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hdegree : P.natDegree = 4) :
    firstCoordinatePolynomialEvaluation P =
      monicQuartic (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0) := by
  have htop : P.coeff 4 = 1 := by rw [← hdegree, coeff_natDegree, hP]
  rw [firstCoordinatePolynomialEvaluation, eval₂_eq_sum_range, hdegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, htop,
    map_one, zero_add, one_mul, pow_zero, pow_one, mul_one,
    monicQuartic, planeCoefficientExtension_apply]
  ring

/-- Convergent quartic preparation and the analytic Tschirnhausen
change construct a distinguished polynomial with zero cubic coefficient. -/
theorem exists_depressed_quartic_polynomial_preparation
    {f : Germ 2} (hregular : IsRegularInFirstCoordinateOfOrder f 4) :
    ∃ e : PointedEquivGerm 2, ∃ P : Polynomial (Germ 1), ∃ U : Germ 2,
      e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 ∧
      P.Monic ∧ P.natDegree = 4 ∧ P.coeff 3 = 0 ∧
      (∀ j, j < 4 → P.coeff j ∈ maximalIdeal 1) ∧ IsUnit U ∧
      e.forward.pullbackRingHom f = firstCoordinatePolynomialEvaluation P * U := by
  obtain ⟨Q, V, hQ, hdegree, hcoeff, hV, hfactor⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_of_pos (by decide : 0 < 4) hregular
  obtain ⟨e, he, hparameter⟩ := exists_quartic_tschirnhausen
    (Q.coeff 3) (Q.coeff 2) (Q.coeff 1) (Q.coeff 0) (hcoeff 3 (by decide))
  let a₂ := depressedQuarticQuadratic (Q.coeff 3) (Q.coeff 2)
  let a₁ := depressedQuarticLinear (Q.coeff 3) (Q.coeff 2) (Q.coeff 1)
  let a₀ := depressedQuarticConstant (Q.coeff 3) (Q.coeff 2) (Q.coeff 1) (Q.coeff 0)
  let a : Fin 4 → Germ 1 := ![a₀, a₁, a₂, 0]
  let P := generalWeierstrassPolynomial 3 a
  have hvalues (j : ℕ) (hj : j < 4) : valueRingHom 1 (Q.coeff j) = 0 :=
    mem_maximalIdeal_iff.mp (hcoeff j hj)
  have ha : ∀ j, a j ∈ maximalIdeal 1 := by
    intro j
    fin_cases j <;> simp [a, a₀, a₁, a₂, mem_maximalIdeal_iff, Algebra.smul_def,
      depressedQuarticConstant, depressedQuarticLinear, depressedQuarticQuadratic,
      hvalues 0 (by decide), hvalues 1 (by decide), hvalues 2 (by decide), hvalues 3 (by decide)]
  have hPform : firstCoordinatePolynomialEvaluation P =
      coordinate (0 : Fin 2) ^ 4 + planeCoefficientExtension a₂ * coordinate (0 : Fin 2) ^ 2 +
        planeCoefficientExtension a₁ * coordinate (0 : Fin 2) + planeCoefficientExtension a₀ := by
    rw [firstCoordinatePolynomialEvaluation_generalWeierstrassPolynomial]
    simp only [a, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Nat.reduceAdd, Fin.val_zero, Fin.val_succ,
      map_zero, zero_mul, add_zero, pow_zero, pow_one, mul_one, planeCoefficientExtension_apply]
    ring
  refine ⟨e, P, e.pullbackAlgEquiv V,
    preserves_second_of_preserves_coefficients e hparameter,
    generalWeierstrassPolynomial_monic _ _, generalWeierstrassPolynomial_natDegree _ _,
    ?_, generalWeierstrassPolynomial_coeff_mem_maximalIdeal 3 ha, hV.map _, ?_⟩
  · exact generalWeierstrassPolynomial_coeff_of_lt 3 a 3 (by decide)
  · change e.pullbackAlgEquiv f = _
    rw [hfactor, map_mul, polynomialEvaluation_monic_quartic Q hQ hdegree, he, hPform]

/-- For multiplicity three or four, the monic depressed polynomial and
unit are constructed from a smooth equation and its actual intersection
with the first member. No polynomial preparation is an input. -/
theorem exists_smooth_second_coordinate_depressed_preparation
    (h f : Germ 2) (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h f) (m : ℕ) (hm : m = 3 ∨ m = 4)
    (hinter : PlaneCurve.intersectionMultiplicity h f hfinite = m) :
    ∃ e : PointedEquivGerm 2, ∃ P : Polynomial (Germ 1), ∃ U : Germ 2,
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) ∧
      P.Monic ∧ P.natDegree = m ∧ P.coeff (m - 1) = 0 ∧
      (∀ j, j < m → P.coeff j ∈ maximalIdeal 1) ∧ IsUnit U ∧
      e.forward.pullbackRingHom f = firstCoordinatePolynomialEvaluation P * U := by
  obtain ⟨a, ha, hregular⟩ := exists_smooth_second_coordinate_regular_first
    h f hh hdh hfinite m hinter
  have hprepare : ∃ e : PointedEquivGerm 2, ∃ P : Polynomial (Germ 1), ∃ U : Germ 2,
      e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 ∧
      P.Monic ∧ P.natDegree = m ∧ P.coeff (m - 1) = 0 ∧
      (∀ j, j < m → P.coeff j ∈ maximalIdeal 1) ∧ IsUnit U ∧
      e.forward.pullbackRingHom (a.forward.pullbackRingHom f) =
        firstCoordinatePolynomialEvaluation P * U := by
    rcases hm with rfl | rfl
    · exact exists_depressed_cubic_polynomial_preparation hregular
    · exact exists_depressed_quartic_polynomial_preparation hregular
  obtain ⟨b, P, U, hby, hP, hdegree, hdepressed, hcoeff, hU, hfactor⟩ := hprepare
  refine ⟨a.comp b, P, U, ?_, hP, hdegree, hdepressed, hcoeff, hU, ?_⟩
  · change (a.comp b).pullbackAlgEquiv h = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change b.forward.pullbackRingHom (a.forward.pullbackRingHom h) = _
    rw [ha, hby]
  · change (a.comp b).pullbackAlgEquiv f = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    exact hfactor

end OnLeConjecture.Analytic.Germ
