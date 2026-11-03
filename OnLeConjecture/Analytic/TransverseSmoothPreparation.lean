/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.SmoothStraightening
public import OnLeConjecture.Analytic.AllOrdersPreparation
public import OnLeConjecture.Analytic.CoordinatePermutation
public import OnLeConjecture.Analytic.AnalyticPointBasis
public import OnLeConjecture.Analytic.JacobianPullback

/-!
# Preparation transverse to a specified smooth branch

A smooth equation and its finite intersection with the first member
determine coordinates in which that equation is the second coordinate
and the member is Weierstrass regular of the intersection order.
Convergent preparation then constructs the monic polynomial and unit.
The polynomial is an output, not a hypothesis.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open Filter
open scoped Topology

theorem firstAxisRestriction_swap (f : Germ 2) :
    lineRestriction (firstCoordinateVector 1)
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) =
        hyperplaneRestriction 1 f := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (ofFunction F hF)
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward)
      (lineGerm (firstCoordinateVector 1)) =
        compPointed (ofFunction F hF) (hyperplaneInclusionGerm 1)
  simp only [coordinateSwapPointedEquiv, pointedEquivGermOfContinuousLinearEquiv,
    lineGerm, hyperplaneInclusionGerm, compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun z ↦ ?_
  change F (coordinateSwapEquiv (1 : Fin 2) (lineMap (firstCoordinateVector 1) z)) =
    F (hyperplaneInclusion 1 z)
  congr 1
  ext i
  fin_cases i
  · change coordinateSwapEquiv (1 : Fin 2) (lineMap (firstCoordinateVector 1) z) 0 = 0
    rw [coordinateSwapEquiv_apply_zero]
    change z 0 * 0 = 0
    exact mul_zero _
  · change z 0 * 1 = z 0
    exact mul_one _

/-- The specified smooth branch becomes `y=0`, and the first-axis
regular order is its actual intersection with the other equation. -/
theorem exists_smooth_second_coordinate_regular_first
    (h f : Germ 2) (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h f) (m : ℕ)
    (hinter : PlaneCurve.intersectionMultiplicity h f hfinite = m) :
    ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) ∧
      IsRegularInFirstCoordinateOfOrder (e.forward.pullbackRingHom f) m := by
  obtain ⟨a, ha, hne, horder⟩ :=
    PlaneCurve.exists_smoothBranch_intersection_formula h f hh hdh hfinite
  let s := coordinateSwapPointedEquiv (1 : Fin 2)
  refine ⟨a.comp s, ?_, ?_⟩
  · change (a.comp s).pullbackAlgEquiv h = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change s.forward.pullbackRingHom (a.forward.pullbackRingHom h) = _
    change a.forward.pullbackRingHom h = coordinate (0 : Fin 2) at ha
    rw [ha, PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  · change vanishingOrder (lineRestriction (firstCoordinateVector 1)
      ((a.comp s).pullbackAlgEquiv f)) = (m : ℕ∞)
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change vanishingOrder (lineRestriction (firstCoordinateVector 1)
      (s.forward.pullbackRingHom (a.forward.pullbackRingHom f))) = (m : ℕ∞)
    rw [firstAxisRestriction_swap]
    have heq := ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hne)
    rw [← horder, hinter] at heq
    exact heq.symm

/-- Convergent monic preparation in coordinates adapted to a specified
smooth branch is constructed from its finite intersection order. -/
theorem exists_smooth_second_coordinate_weierstrass
    (h f : Germ 2) (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h f) (m : ℕ) (hm : 0 < m)
    (hinter : PlaneCurve.intersectionMultiplicity h f hfinite = m) :
    ∃ e : PointedEquivGerm 2, ∃ P : _root_.Polynomial (Germ 1), ∃ U : Germ 2,
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) ∧
      P.Monic ∧ P.natDegree = m ∧
      (∀ j, j < m → P.coeff j ∈ maximalIdeal 1) ∧ IsUnit U ∧
      e.forward.pullbackRingHom f = firstCoordinatePolynomialEvaluation P * U := by
  obtain ⟨e, he, hregular⟩ := exists_smooth_second_coordinate_regular_first
    h f hh hdh hfinite m hinter
  obtain ⟨P, U, hP, hdegree, hcoeff, hU, hfactor⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_of_pos hm hregular
  exact ⟨e, P, U, he, hP, hdegree, hcoeff, hU, hfactor⟩

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.PointedEquivGerm

/-- Analytic coordinate equivalences preserve reduced equations. -/
theorem squarefree_pullback {n : ℕ} (e : PointedEquivGerm n) (f : Germ n)
    (hf : Squarefree f) : Squarefree (e.forward.pullbackRingHom f) := by
  intro q hq
  have h := map_dvd e.pullbackRingEquiv.symm.toRingHom hq
  change e.pullbackRingEquiv.symm (q * q) ∣
    e.pullbackRingEquiv.symm (e.pullbackRingEquiv f) at h
  rw [map_mul, RingEquiv.symm_apply_apply] at h
  have hu := (hf _ h).map e.pullbackRingEquiv.toRingHom
  change IsUnit (e.pullbackRingEquiv (e.pullbackRingEquiv.symm q)) at hu
  simpa only [RingEquiv.apply_symm_apply] using hu

/-- A divisor supported on the specified smooth branch becomes the
corresponding coordinate-power divisor of every transformed Jacobian. -/
theorem coordinate_pow_dvd_jacobian_of_pullback_equation
    (e : PointedEquivGerm 2) (h f g : Germ 2) (k : ℕ)
    (he : e.forward.pullbackRingHom h = Germ.coordinate (1 : Fin 2))
    (hdiv : h ^ k ∣ Germ.jacobian f g) :
    Germ.coordinate (1 : Fin 2) ^ k ∣
      Germ.jacobian (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g) := by
  have hpull := map_dvd e.forward.pullbackRingHom hdiv
  rw [map_pow, he] at hpull
  rw [show Germ.jacobian (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g) =
      e.forward.pullbackRingHom (Germ.jacobian f g) * Germ.coordinateJacobian e.forward from
        Germ.jacobian_compPointed f g e.forward]
  exact dvd_mul_of_dvd_left hpull _

end OnLeConjecture.Analytic.PointedEquivGerm
