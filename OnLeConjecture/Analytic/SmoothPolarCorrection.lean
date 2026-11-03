/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableDerivativeOrder
public import OnLeConjecture.Analytic.FiniteParametricMorse
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import OnLeConjecture.Analytic.OrderOnePreparation
public import OnLeConjecture.PlaneCurve.SmoothBranch
public import OnLeConjecture.PlaneCurve.Milnor

/-!
# Polar correction at a smooth branch

A parameter need not be transverse to a smooth curve. Restricting it to
the curve and differentiating decreases its order by one. Consequently
the polar intersection is the parameter intersection minus one. The
proof transports both germs through an actual analytic coordinate
equivalence and uses the one-variable derivative order theorem.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Differentiation in the surviving coordinate commutes with restriction
to the first coordinate hyperplane. -/
theorem partialDerivative_hyperplaneRestriction_plane (f : Germ 2) :
    partialDerivative (0 : Fin 1) (hyperplaneRestriction 1 f) =
      hyperplaneRestriction 1 (partialDerivative (1 : Fin 2) f) := by
  change partialDerivative (0 : Fin 1) (compPointed f (hyperplaneInclusionGerm 1)) = _
  rw [partialDerivative_compPointed_sum, Fin.sum_univ_two,
    ← PointedMapGerm.pullback_coordinate, ← PointedMapGerm.pullback_coordinate]
  change hyperplaneRestriction 1 (partialDerivative (0 : Fin 2) f) *
      partialDerivative (0 : Fin 1) (hyperplaneRestriction 1 (coordinate (0 : Fin 2))) +
    hyperplaneRestriction 1 (partialDerivative (1 : Fin 2) f) *
      partialDerivative (0 : Fin 1) (hyperplaneRestriction 1 (coordinate (1 : Fin 2))) = _
  have hcoordinate : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) =
      coordinate (0 : Fin 1) := by
    simpa using hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1)
  rw [hyperplaneRestriction_coordinate_zero, hcoordinate]
  simp only [partialDerivative_zero, partialDerivative_coordinate_same,
    mul_zero, mul_one, zero_add]

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- The coordinate branch has polar intersection one less than its
intersection with any parameter vanishing at the origin. Tangency of
the parameter is allowed. -/
theorem exists_coordinate_polar_intersection_add_one
    (u : Germ 2) (hu : u ∈ Germ.maximalIdeal 2)
    (hfinite : HasFiniteIntersection (Germ.coordinate (0 : Fin 2)) u) :
    ∃ hpolar : HasFinitePolarIntersection (Germ.coordinate (0 : Fin 2)) u,
      polarIntersectionMultiplicity (Germ.coordinate (0 : Fin 2)) u hpolar + 1 =
        intersectionMultiplicity (Germ.coordinate (0 : Fin 2)) u hfinite := by
  have hne := restriction_ne_zero_of_hasFiniteIntersection_coordinate u hfinite
  have hmax : Germ.hyperplaneRestriction 1 u ∈ Germ.maximalIdeal 1 := by
    apply Germ.mem_maximalIdeal_iff.mpr
    change Germ.valueRingHom 1 ((Germ.hyperplaneInclusionGerm 1).pullbackRingHom u) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact Germ.mem_maximalIdeal_iff.mp hu
  obtain ⟨hderiv, horder⟩ := Germ.derivative_ne_zero_and_order_add_one
    (Germ.hyperplaneRestriction 1 u) hmax hne
  rw [Germ.partialDerivative_hyperplaneRestriction_plane] at hderiv horder
  have hf' := hasFiniteIntersection_coordinate_of_restriction_ne_zero
    (Germ.partialDerivative (1 : Fin 2) u) hderiv
  have hpolar : HasFinitePolarIntersection (Germ.coordinate (0 : Fin 2)) u := by
    rw [hasFinitePolarIntersection_iff_hasFiniteIntersection, jacobian_coordinate_zero_left]
    exact hf'
  refine ⟨hpolar, ?_⟩
  have hpolarEq : polarIntersectionMultiplicity (Germ.coordinate (0 : Fin 2)) u hpolar =
      intersectionMultiplicity (Germ.coordinate (0 : Fin 2))
        (Germ.partialDerivative (1 : Fin 2) u) hf' := by
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [polarIdeal, jacobian_coordinate_zero_left]
  rw [hpolarEq]
  rw [intersectionMultiplicity_coordinate_eq_restrictionOrder _ hderiv,
    intersectionMultiplicity_coordinate_eq_restrictionOrder _ hne]
  exact horder

/-- For a smooth curve with nonzero first directional derivative, every
parameter meeting the curve finitely has polar intersection one less
than its intersection with the curve. No transversality of the
parameter is assumed. -/
theorem exists_smooth_polar_intersection_add_one
    (f u : Germ 2) (hf : f ∈ Germ.maximalIdeal 2) (hu : u ∈ Germ.maximalIdeal 2)
    (hregular : Germ.differential f (Germ.firstCoordinateVector 1) ≠ 0)
    (hfinite : HasFiniteIntersection f u) :
    ∃ hpolar : HasFinitePolarIntersection f u,
      polarIntersectionMultiplicity f u hpolar + 1 = intersectionMultiplicity f u hfinite := by
  obtain ⟨e, he, _⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension f hf hregular
  let q := e.pullbackAlgEquiv.symm u
  have hcoordinate : e.symm.pullbackAlgEquiv f = Germ.coordinate (0 : Fin 2) := by
    change e.pullbackAlgEquiv.symm f = _
    rw [← he, AlgEquiv.symm_apply_apply]
  have hq : q ∈ Germ.maximalIdeal 2 := by
    apply Germ.mem_maximalIdeal_iff.mpr
    change Germ.valueRingHom 2 (e.inverse.pullbackRingHom u) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact Germ.mem_maximalIdeal_iff.mp hu
  have hqfinite : HasFiniteIntersection (Germ.coordinate (0 : Fin 2)) q := by
    have h := hfinite.pullback e.symm
    rw [hcoordinate] at h
    exact h
  obtain ⟨hqpolar, hqorder⟩ := exists_coordinate_polar_intersection_add_one q hq hqfinite
  have hpolar : HasFinitePolarIntersection f u := by
    have h := hqpolar.pullback e
    rw [he, show e.pullbackAlgEquiv q = u from e.pullbackAlgEquiv.apply_symm_apply u] at h
    exact h
  refine ⟨hpolar, ?_⟩
  have hpolarEq := polarIntersectionMultiplicity_pullback e.symm f u hpolar
  have hinterEq := intersectionMultiplicity_pullback e.symm hfinite
  change Module.finrank ℂ _ = Module.finrank ℂ _ at hpolarEq hinterEq
  rw [hcoordinate] at hpolarEq hinterEq
  change Module.finrank ℂ _ + 1 = Module.finrank ℂ _
  rw [hpolarEq, hinterEq]
  exact hqorder

/-- The correction formula for every order-one analytic curve germ,
without a chosen nonzero coordinate derivative. A transverse coordinate
is constructed before applying the smooth-branch theorem. -/
theorem exists_order_one_polar_intersection_add_one
    (f u : Germ 2) (hf : f ∈ Germ.maximalIdeal 2)
    (hnext : f ∉ Germ.maximalIdeal 2 ^ 2) (hu : u ∈ Germ.maximalIdeal 2)
    (hfinite : HasFiniteIntersection f u) :
    ∃ hpolar : HasFinitePolarIntersection f u,
      polarIntersectionMultiplicity f u hpolar + 1 = intersectionMultiplicity f u hfinite := by
  obtain ⟨e, hregular⟩ := Germ.exists_linear_equiv_regularInFirstCoordinateOfOrder
    (d := 1) (by simpa only [pow_one] using hf) hnext
  have hfirst := Germ.differential_firstCoordinateVector_ne_zero_of_regular_order_one hregular
  have hemax (v : Germ 2) (hv : v ∈ Germ.maximalIdeal 2) :
      e.pullbackAlgEquiv v ∈ Germ.maximalIdeal 2 := by
    apply Germ.mem_maximalIdeal_iff.mpr
    change Germ.valueRingHom 2 (e.forward.pullbackRingHom v) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact Germ.mem_maximalIdeal_iff.mp hv
  obtain ⟨hepolar, heq⟩ := exists_smooth_polar_intersection_add_one
    (e.pullbackAlgEquiv f) (e.pullbackAlgEquiv u) (hemax f hf) (hemax u hu)
      hfirst (hfinite.pullback e)
  have hpolar : HasFinitePolarIntersection f u :=
    (hasFinitePolarIntersection_pullback_iff e f u).mp hepolar
  refine ⟨hpolar, ?_⟩
  rw [polarIntersectionMultiplicity_pullback e f u hpolar,
    intersectionMultiplicity_pullback e hfinite]
  exact heq

end OnLeConjecture.PlaneCurve
