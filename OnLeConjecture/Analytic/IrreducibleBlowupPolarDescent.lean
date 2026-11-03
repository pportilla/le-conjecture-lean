/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneFiniteColengthCriterion
public import OnLeConjecture.Analytic.IrreducibleBlowupBranch
public import OnLeConjecture.Analytic.PointBlowupPolarIntersection

/-!
# Polar decrease along an irreducible analytic branch

The first partial polar is finite in first-axis regular coordinates. The
blowup recurrence bounds the polar intersection at the unique branch
center by the original intersection minus `m * (m - 1)`.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

theorem exists_irreducible_transform_polar_bound
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (horder : f ∈ maximalIdeal 2 ^ m)
    (hirr : Irreducible f) (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (hfinite : PlaneCurve.HasFiniteIntersection f (partialDerivative 0 f)) :
    ∃ c : ℂ, Irreducible (pointBlowupTransform c m f horder) ∧
      ∃ hchild : PlaneCurve.HasFiniteIntersection (pointBlowupTransform c m f horder)
        (partialDerivative 0 (pointBlowupTransform c m f horder)),
        m * (m - 1) + PlaneCurve.intersectionMultiplicity
          (pointBlowupTransform c m f horder)
          (partialDerivative 0 (pointBlowupTransform c m f horder)) hchild ≤
            PlaneCurve.intersectionMultiplicity f (partialDerivative 0 f) hfinite := by
  classical
  obtain ⟨c, hc, _hother, _hcomplement⟩ :=
    exists_unique_irreducible_pointBlowupTransform_of_regular m hm f horder hirr hregular
  obtain ⟨P, U, hP, hPm, hU, hfactor, hcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients 1 m hm f hregular
      (by simpa only [one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using horder)
  have hmodel : f = U * firstCoordinatePolynomialEvaluation P := by
    rw [hfactor, mul_comm]
  have hmodelFinite : PlaneCurve.HasFiniteIntersection
      (U * firstCoordinatePolynomialEvaluation P)
      (partialDerivative 0 (U * firstCoordinatePolynomialEvaluation P)) := by
    simpa only [← hmodel] using hfinite
  obtain ⟨A, hA, _hAm, _hscale, htransform, _hderivative, hfA, hiA⟩ :=
    exists_pointBlowup_polar_intersection_recurrence m hm P hP hPm
      (by simpa only [one_mul] using hcoeff) U hU hmodelFinite
  let g := pointBlowupTransform c m f horder
  have hg : g = (pointBlowupChartGerm c).pullbackRingHom U *
      firstCoordinatePolynomialEvaluation (rootTranslation A c) := by
    apply pointBlowupTransform_unique c m f _ _
      (pointBlowupTransform_factor c m f horder)
    rw [hmodel]
    exact htransform c
  have hgzero : valueRingHom 2 g = 0 := by
    by_contra h
    exact hc.not_isUnit (isUnit_of_valueRingHom_ne_zero h)
  have hcroot : c ∈ (A.map (valueRingHom 1)).roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots (hA.map _).ne_zero).mpr
    rw [hg, map_mul, value_firstCoordinatePolynomialEvaluation_rootTranslation] at hgzero
    exact (mul_eq_zero.mp hgzero).resolve_left
      (valueRingHom_ne_zero_of_isUnit (hU.map _))
  let center : (A.map (valueRingHom 1)).roots.toFinset := ⟨c, hcroot⟩
  have hchild : PlaneCurve.HasFiniteIntersection g (partialDerivative 0 g) := by
    simpa only [hg] using hfA center
  refine ⟨c, hc, hchild, ?_⟩
  have hsum := Finset.single_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    Nat.zero_le (PlaneCurve.intersectionMultiplicity _ _ (hfA i)))
    (Finset.mem_univ center)
  have hterm : PlaneCurve.intersectionMultiplicity g (partialDerivative 0 g) hchild =
      PlaneCurve.intersectionMultiplicity
        ((pointBlowupChartGerm center).pullbackRingHom U *
          firstCoordinatePolynomialEvaluation (rootTranslation A center))
        (partialDerivative 0 ((pointBlowupChartGerm center).pullbackRingHom U *
          firstCoordinatePolynomialEvaluation (rootTranslation A center))) (hfA center) := by
    congr 1
    exact congrArg (partialDerivative 0) hg
  change m * (m - 1) + PlaneCurve.intersectionMultiplicity g (partialDerivative 0 g) hchild ≤ _
  rw [hterm]
  have hbound := Nat.add_le_add_left hsum (m * (m - 1))
  rw [← hiA] at hbound
  simpa only [← hmodel] using hbound

theorem exists_irreducible_transform_polar_lt
    (m : ℕ) (hm : 2 ≤ m) (f : Germ 2) (horder : f ∈ maximalIdeal 2 ^ m)
    (hirr : Irreducible f) (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    ∃ c : ℂ, Irreducible (pointBlowupTransform c m f horder) ∧
      ∃ hchild : PlaneCurve.HasFiniteIntersection (pointBlowupTransform c m f horder)
        (partialDerivative 0 (pointBlowupTransform c m f horder)),
        PlaneCurve.intersectionMultiplicity (pointBlowupTransform c m f horder)
          (partialDerivative 0 (pointBlowupTransform c m f horder)) hchild <
            PlaneCurve.intersectionMultiplicity f (partialDerivative 0 f)
              (PlaneCurve.finite_first_partial_polar_of_irreducible_regular f hirr m hregular) := by
  obtain ⟨c, hc, hchild, hbound⟩ := exists_irreducible_transform_polar_bound m
    (by omega) f horder hirr hregular
    (PlaneCurve.finite_first_partial_polar_of_irreducible_regular f hirr m hregular)
  refine ⟨c, hc, hchild, ?_⟩
  have hpos : 0 < m * (m - 1) := Nat.mul_pos (by omega) (by omega)
  omega

end OnLeConjecture.Analytic.Germ
