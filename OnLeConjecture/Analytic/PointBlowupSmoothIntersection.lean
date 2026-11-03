/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupChart
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization
public import OnLeConjecture.PlaneCurve.SmoothStraightening

/-!
# Intersection with a smooth branch after one blowup

In coordinates where the smooth branch is `x=0`, its strict transform
in the chart `(x,y) ↦ (xy,y)` is again `x=0`. Restriction to this branch
proves the exact intersection recurrence for arbitrary convergent germs.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The zero-centered blowup chart fixes the parametrized branch `x=0`. -/
theorem hyperplaneRestriction_pointBlowupChart_zero (f : Germ 2) :
    hyperplaneRestriction 1 ((pointBlowupChartGerm 0).pullbackRingHom f) =
      hyperplaneRestriction 1 f := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (ofFunction F hF) (pointBlowupChartGerm 0))
    (hyperplaneInclusionGerm 1) = compPointed (ofFunction F hF) (hyperplaneInclusionGerm 1)
  simp only [pointBlowupChartGerm, hyperplaneInclusionGerm, compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    change F (pointBlowupChart 0 (hyperplaneInclusion 1 z)) = F (hyperplaneInclusion 1 z)
    congr 1
    ext i
    fin_cases i <;> simp [pointBlowupChart, hyperplaneInclusion]

/-- Restricting an actual strict-transform identity subtracts the
exceptional multiplicity from the branch intersection. -/
theorem pointBlowup_coordinate_intersection_recurrence
    (m : ℕ) (f F : Germ 2)
    (htransform : (pointBlowupChartGerm 0).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F)
    (hfinite : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) f) :
    ∃ hfinite' : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) F,
      PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) f hfinite =
        m + PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) F hfinite' := by
  have hrestriction : hyperplaneRestriction 1 f =
      coordinate (0 : Fin 1) ^ m * hyperplaneRestriction 1 F := by
    have hr := congrArg (hyperplaneRestriction 1) htransform
    simpa only [hyperplaneRestriction_pointBlowupChart_zero, map_mul, map_pow,
      show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
      hyperplaneRestriction_coordinate_succ] using hr
  have hfne := PlaneCurve.restriction_ne_zero_of_hasFiniteIntersection_coordinate f hfinite
  have hFne : hyperplaneRestriction 1 F ≠ 0 := by
    intro hz
    exact hfne (by rw [hrestriction, hz, mul_zero])
  refine ⟨PlaneCurve.hasFiniteIntersection_coordinate_of_restriction_ne_zero F hFne, ?_⟩
  rw [PlaneCurve.intersectionMultiplicity_coordinate_eq_restrictionOrder f hfne,
    PlaneCurve.intersectionMultiplicity_coordinate_eq_restrictionOrder F hFne,
    hrestriction, vanishingOrder_mul, vanishingOrder_coordinate_pow,
    ENat.toNat_add (ENat.natCast_ne_top _) (vanishingOrder_eq_top_iff.not.mpr hFne),
    ENat.toNat_natCast]

/-- The transform and its intersection recurrence are constructed from
the original germ's order lower bound. -/
theorem exists_pointBlowup_coordinate_intersection_recurrence
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hfinite : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) f) :
    ∃ F : Germ 2,
      (pointBlowupChartGerm 0).pullbackRingHom f = coordinate (1 : Fin 2) ^ m * F ∧
      ∃ hfinite' : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) F,
        PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) f hfinite =
          m + PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) F hfinite' := by
  obtain ⟨F, hF⟩ := exists_pointBlowupChart_factor 0 m f hf
  exact ⟨F, hF, pointBlowup_coordinate_intersection_recurrence m f F hF hfinite⟩

private theorem restriction_vanishingOrder_eq_of_intersection
    (F : Germ 2) (hfinite : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) F)
    (n : ℕ) (hinter : PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) F hfinite = n) :
    vanishingOrder (hyperplaneRestriction 1 F) = n := by
  have hne := PlaneCurve.restriction_ne_zero_of_hasFiniteIntersection_coordinate F hfinite
  have horder : (vanishingOrder (hyperplaneRestriction 1 F)).toNat = n := by
    simpa only [PlaneCurve.intersectionMultiplicity_coordinate_eq_restrictionOrder F hne]
      using hinter
  exact (ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hne)).symm.trans
    (congrArg (fun k : ℕ ↦ (k : ℕ∞)) horder)

/-- Intersection one with a coordinate branch forces exact ordinary
order one for the other equation. -/
theorem mem_maximalIdeal_not_mem_sq_of_coordinate_intersection_one
    (F : Germ 2) (hfinite : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) F)
    (hinter : PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) F hfinite = 1) :
    F ∈ maximalIdeal 2 ∧ F ∉ maximalIdeal 2 ^ 2 := by
  have horder := restriction_vanishingOrder_eq_of_intersection F hfinite 1 hinter
  have hmem : hyperplaneRestriction 1 F ∈ maximalIdeal 1 := by
    rw [← pow_one (maximalIdeal 1), mem_maximalIdeal_one_pow_iff, horder]
  have hvalue : valueRingHom 1 (hyperplaneRestriction 1 F) = valueRingHom 2 F :=
    PointedMapGerm.valueRingHom_pullback (hyperplaneInclusionGerm 1) F
  refine ⟨mem_maximalIdeal_iff.mpr (hvalue ▸ mem_maximalIdeal_iff.mp hmem), ?_⟩
  intro hsquare
  have hrestriction := (hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal_pow hsquare
  change hyperplaneRestriction 1 F ∈ maximalIdeal 1 ^ 2 at hrestriction
  rw [mem_maximalIdeal_one_pow_iff, horder] at hrestriction
  norm_num at hrestriction

/-- If the original intersection exceeds the exceptional multiplicity
by one, the strict transform is a smooth irreducible branch. -/
theorem pointBlowupTransform_smooth_of_coordinate_intersection_succ
    (m : ℕ) (f F : Germ 2)
    (htransform : (pointBlowupChartGerm 0).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F)
    (hfinite : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) f)
    (hinter : PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) f hfinite = m + 1) :
    F ∈ maximalIdeal 2 ∧ F ∉ maximalIdeal 2 ^ 2 ∧ differential F ≠ 0 ∧ Irreducible F := by
  obtain ⟨hfinite', hrecurrence⟩ := pointBlowup_coordinate_intersection_recurrence
    m f F htransform hfinite
  have hlocal : PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) F hfinite' = 1 :=
    by omega
  obtain ⟨hmem, hnot⟩ :=
    mem_maximalIdeal_not_mem_sq_of_coordinate_intersection_one F hfinite' hlocal
  exact ⟨hmem, hnot, smooth_irreducible_of_mem_maximalIdeal_not_mem_sq F hmem hnot⟩

/-- Minimal intersection leaves no common point of the two strict
transforms in the branch chart. -/
theorem pointBlowupTransform_isUnit_of_coordinate_intersection_eq_order
    (m : ℕ) (f F : Germ 2)
    (htransform : (pointBlowupChartGerm 0).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F)
    (hfinite : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) f)
    (hinter : PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) f hfinite = m) :
    IsUnit F := by
  obtain ⟨hfinite', hrecurrence⟩ := pointBlowup_coordinate_intersection_recurrence
    m f F htransform hfinite
  have hlocal : PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) F hfinite' = 0 :=
    by omega
  have horder := restriction_vanishingOrder_eq_of_intersection F hfinite' 0 hlocal
  have hunit := vanishingOrder_eq_zero_iff_isUnit.mp horder
  have hvalue := valueRingHom_ne_zero_of_isUnit hunit
  rw [hyperplaneRestriction, PointedMapGerm.valueRingHom_pullback] at hvalue
  exact isUnit_of_valueRingHom_ne_zero hvalue

end OnLeConjecture.Analytic.Germ
