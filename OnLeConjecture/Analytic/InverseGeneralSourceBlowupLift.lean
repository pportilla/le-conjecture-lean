/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralSourceBlowupLift

/-!
# Lifting a prescribed old finite center into new coordinates

The finite condition is imposed on the inverse source equivalence at
the old center. The general lift then constructs the new center, the
child coordinate equivalence, and its exceptional-coordinate unit.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_inverse_exceptional_unit
    (e : PointedEquivGerm 2) (U : Germ 2) (hU : IsUnit U)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U) :
    ∃ V : Germ 2, IsUnit V ∧
      e.inverse.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * V := by
  obtain ⟨W, hUW⟩ := hU.exists_right_inv
  have hW : IsUnit W := isUnit_iff_exists_inv.mpr ⟨U, by simpa only [mul_comm] using hUW⟩
  refine ⟨e.inverse.pullbackRingHom W, hW.map _, ?_⟩
  have h := congrArg e.inverse.pullbackRingHom hy
  change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (coordinate (1 : Fin 2))) = _ at h
  rw [RingEquiv.symm_apply_apply, map_mul] at h
  have hmul := congrArg (fun f : Germ 2 ↦ f * e.inverse.pullbackRingHom W) h
  rw [mul_assoc, ← map_mul, hUW, map_one, mul_one] at hmul
  exact hmul.symm

/-- A finite inverse tangent determines the new finite center and all
commuting coordinate data for a specified old chart. -/
theorem exists_inverse_finite_chart_lift
    (e : PointedEquivGerm 2) (c : ℂ)
    (hfinite : finiteTangentDenominator e.symm c ≠ 0) :
    ∃ E : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
      E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U ∧
      e.forward.comp (pointBlowupChartGerm (generalFiniteChartCenter e.symm c)) =
        (pointBlowupChartGerm c).comp E.forward := by
  obtain ⟨Q, V, L, hV, _hQ, _hVfactor, _hcenter, _hratio, hLy, hcomm, _hJac⟩ :=
    exists_pointBlowup_lift_of_finite_tangent e.symm c hfinite
  obtain ⟨U, hU, hUy⟩ := exists_inverse_exceptional_unit L V hV hLy
  refine ⟨L.symm, U, hU, hUy, ?_⟩
  have h := congrArg (fun B : PointedMapGerm 2 2 ↦ e.forward.comp B) hcomm
  change e.forward.comp (e.inverse.comp (pointBlowupChartGerm c)) =
    e.forward.comp ((pointBlowupChartGerm (generalFiniteChartCenter e.symm c)).comp L.forward) at h
  rw [← PointedMapGerm.comp_assoc, e.forward_inverse, PointedMapGerm.identity_comp] at h
  have hi := congrArg (fun B : PointedMapGerm 2 2 ↦ B.comp L.inverse) h
  rw [PointedMapGerm.comp_assoc, PointedMapGerm.comp_assoc, L.forward_inverse,
    PointedMapGerm.comp_identity] at hi
  exact hi.symm

end OnLeConjecture.Analytic.Germ

