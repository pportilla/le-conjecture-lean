/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IrreducibleScaledPolynomial
public import OnLeConjecture.Analytic.WeightedParameterTranslation
public import OnLeConjecture.Analytic.FiniteExceptionalBasepoints
public import OnLeConjecture.PlaneCurve.BranchCountInvariance

/-!
# The unique strict-transform branch of an irreducible equation

For a first-axis regular irreducible analytic germ of ordinary order `m`,
convergent preparation and coefficientwise scaling construct the polynomial
in each blowup chart. It is irreducible and its residue has exactly one
root. The strict transform at that root is irreducible, all other finite
transforms are units, and the complementary transform is a unit.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- There is one finite exceptional point on an irreducible analytic
branch in transverse first-axis coordinates. The actual strict transform
at that point remains irreducible. -/
theorem exists_unique_irreducible_pointBlowupTransform_of_regular
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hirr : Irreducible f) (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    ∃ c : ℂ, Irreducible (pointBlowupTransform c m f hf) ∧
      (∀ ζ, ζ ≠ c → IsUnit (pointBlowupTransform ζ m f hf)) ∧
      IsUnit (pointBlowupTransform 0 m
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow hf)) := by
  obtain ⟨P, U, hP, hPm, hU, hfactor, hcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients 1 m hm f hregular
      (by simpa only [one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf)
  obtain ⟨A, hA, hAm, hscale, _hcoefficient⟩ :=
    exists_monic_weighted_polynomial_scaling P m 1 hP hPm hcoeff
  rw [pow_one] at hscale
  have hscaledIrr : Irreducible
      (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1)))) := by
    rw [← hscale]
    have hass : Associated f (firstCoordinatePolynomialEvaluation P) := by
      rw [hfactor]
      exact associated_mul_unit_left _ _ hU
    exact hass.irreducible hirr
  have hAirr := irreducible_of_irreducible_scaled_polynomialEvaluation A hA hscaledIrr
  obtain ⟨c, hresidue⟩ := exists_residue_eq_root_power_of_monic_irreducible A hA hAirr
  have htransform (ζ : ℂ) : pointBlowupTransform ζ m f hf =
      firstCoordinatePolynomialEvaluation (rootTranslation A ζ) *
        (pointBlowupChartGerm ζ).pullbackRingHom U := by
    apply pointBlowupTransform_unique ζ m f
      _ _ (pointBlowupTransform_factor ζ m f hf)
    rw [hfactor, hscale, map_mul, pointBlowupChart_pullback_scaled_polynomial, hAm, mul_assoc]
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [htransform]
    apply (associated_mul_unit_left _ _ (hU.map _)).symm.irreducible
    exact irreducible_polynomialEvaluation_rootTranslation_of_single_residue_root
      A hA hAirr c hresidue
  · intro ζ hζ
    rw [htransform]
    apply IsUnit.mul _ (hU.map _)
    apply isUnit_firstCoordinatePolynomialEvaluation_rootTranslation
    rw [hresidue, eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr hζ)
  · exact complementaryBlowupTransform_isUnit_of_regular m f _ hregular
      (pointBlowupTransform_factor 0 m _ _)

/-- A finite-chart strict transform of a regular irreducible branch is
nonunit at exactly one center. This is a uniqueness theorem about the
constructed analytic transforms, not an assumed tangent certificate. -/
theorem exists_unique_vanishing_pointBlowupTransform_of_irreducible
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hirr : Irreducible f) (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    ∃ c : ℂ, Irreducible (pointBlowupTransform c m f hf) ∧
      ∀ ζ, pointBlowupTransform ζ m f hf ∈ maximalIdeal 2 ↔ ζ = c := by
  obtain ⟨c, hc, hother, _⟩ :=
    exists_unique_irreducible_pointBlowupTransform_of_regular m hm f hf hirr hregular
  refine ⟨c, hc, ?_⟩
  intro ζ
  constructor
  · intro hmem
    by_contra hne
    exact (valueRingHom_ne_zero_of_isUnit (hother ζ hne)) (mem_maximalIdeal_iff.mp hmem)
  · rintro rfl
    rw [mem_maximalIdeal_iff]
    by_contra hvalue
    exact hc.not_isUnit (isUnit_of_valueRingHom_ne_zero hvalue)

/-- The one nonunit transform carries exactly one irreducible analytic
branch, and every other finite transform has branch count zero. -/
theorem exists_pointBlowupTransform_branchCounts_of_irreducible
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hirr : Irreducible f) (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    ∃ c : ℂ, PlaneCurve.irreducibleBranchCount (pointBlowupTransform c m f hf) = 1 ∧
      ∀ ζ, ζ ≠ c → PlaneCurve.irreducibleBranchCount (pointBlowupTransform ζ m f hf) = 0 := by
  obtain ⟨c, hc, hother, _⟩ :=
    exists_unique_irreducible_pointBlowupTransform_of_regular m hm f hf hirr hregular
  refine ⟨c, PlaneCurve.irreducibleBranchCount_eq_one_of_irreducible _ hc, ?_⟩
  intro ζ hζ
  rw [PlaneCurve.irreducibleBranchCount_eq_of_associated
    (associated_one_iff_isUnit.mpr (hother ζ hζ))]
  exact PlaneCurve.irreducibleBranchCount_one

end OnLeConjecture.Analytic.Germ
