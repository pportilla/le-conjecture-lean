/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SupportedFiniteBlowupLift
public import OnLeConjecture.Analytic.RightLeftRelation

/-!
# Lifts into the finite and complementary blowup charts

Every source equivalence lifts into one of the two projective charts.
The target chart and the exceptional unit are constructed. A strict
transform transports in the reverse direction with the corresponding
inverse-unit factor.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The parent coordinate map for a finite or complementary chart. -/
@[expose] noncomputable def projectiveChartSource : Option ℂ → PointedEquivGerm 2
  | some _ => PointedEquivGerm.identity 2
  | none => coordinateSwapPointedEquiv (1 : Fin 2)

/-- The center used by the finite chart formula after choosing the
parent coordinates. The complementary chart has center zero. -/
@[expose] def projectiveChartCenter : Option ℂ → ℂ
  | some c => c
  | none => 0

theorem finiteTangentDenominator_swap_comp (e : PointedEquivGerm 2) (ζ : ℂ) :
    finiteTangentDenominator ((coordinateSwapPointedEquiv (1 : Fin 2)).comp e) ζ =
      finiteChartCenter e ζ := by
  have hy : ((coordinateSwapPointedEquiv (1 : Fin 2)).comp e).forward.pullbackRingHom
      (coordinate (1 : Fin 2)) = e.forward.pullbackRingHom (coordinate 0) := by
    change ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.comp e.forward).pullbackRingHom
      (coordinate 1) = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
      coordinateSwapPointedEquiv_pullback_second]
  simp only [finiteTangentDenominator, hy, finiteChartCenter]

theorem finiteChartCenter_swap_comp (e : PointedEquivGerm 2) (ζ : ℂ) :
    finiteChartCenter ((coordinateSwapPointedEquiv (1 : Fin 2)).comp e) ζ =
      finiteTangentDenominator e ζ := by
  have hx : ((coordinateSwapPointedEquiv (1 : Fin 2)).comp e).forward.pullbackRingHom
      (coordinate (0 : Fin 2)) = e.forward.pullbackRingHom (coordinate 1) := by
    change ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.comp e.forward).pullbackRingHom
      (coordinate 0) = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
      PointedMapGerm.pullback_coordinate, coordinateSwapPointedEquiv_component_zero]
  simp only [finiteChartCenter, hx, finiteTangentDenominator]

/-- An arbitrary source equivalence has a constructed analytic lift
in one of the two projective charts, with no tangent hypothesis. -/
theorem exists_twoChart_blowup_lift (e : PointedEquivGerm 2) (ζ : ℂ) :
    ∃ (t : Option ℂ) (E : PointedEquivGerm 2) (U : Germ 2), IsUnit U ∧
      E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U ∧
      e.forward.comp (pointBlowupChartGerm ζ) =
        (projectiveChartSource t).forward.comp
          ((pointBlowupChartGerm (projectiveChartCenter t)).comp E.forward) := by
  by_cases hfinite : finiteTangentDenominator e ζ ≠ 0
  · obtain ⟨Q, U, E, hU, _hQ, _hUf, _hc, _hr, hEy, hcomm, _hJ⟩ :=
      exists_pointBlowup_lift_of_finite_tangent e ζ hfinite
    refine ⟨some (generalFiniteChartCenter e ζ), E, U, hU, hEy, ?_⟩
    simpa only [projectiveChartSource, projectiveChartCenter, PointedEquivGerm.identity_forward,
      PointedMapGerm.identity_comp] using hcomm
  · have hzero : finiteTangentDenominator e ζ = 0 := not_ne_iff.mp hfinite
    have hswapfinite : finiteTangentDenominator
        ((coordinateSwapPointedEquiv (1 : Fin 2)).comp e) ζ ≠ 0 := by
      rw [finiteTangentDenominator_swap_comp]
      exact finiteChartCenter_ne_zero_of_denominator_zero e ζ hzero
    obtain ⟨Q, U, E, hU, _hQ, _hUf, _hc, _hr, hEy, hcomm, _hJ⟩ :=
      exists_pointBlowup_lift_of_finite_tangent
        ((coordinateSwapPointedEquiv (1 : Fin 2)).comp e) ζ hswapfinite
    have hc : generalFiniteChartCenter ((coordinateSwapPointedEquiv (1 : Fin 2)).comp e) ζ = 0 := by
      rw [generalFiniteChartCenter, finiteChartCenter_swap_comp, hzero, zero_div]
    rw [hc] at hcomm
    refine ⟨none, E, U, hU, hEy, ?_⟩
    have h := congrArg (fun B : PointedMapGerm 2 2 ↦
      (coordinateSwapPointedEquiv (1 : Fin 2)).forward.comp B) hcomm
    change (coordinateSwapPointedEquiv (1 : Fin 2)).forward.comp
      (((coordinateSwapPointedEquiv (1 : Fin 2)).forward.comp e.forward).comp
        (pointBlowupChartGerm ζ)) = _ at h
    rw [← PointedMapGerm.comp_assoc, ← PointedMapGerm.comp_assoc,
      coordinateSwapPointedEquiv_forward_comp_self, PointedMapGerm.identity_comp] at h
    exact h

/-- A strict transform can be transported backwards through a commuting
chart square. The new unit is constructed from the inverse exceptional unit. -/
theorem exists_inverse_transform_of_unit_blowup
    (e old E : PointedEquivGerm 2) (ζ c : ℂ) (U : Germ 2) (hU : IsUnit U)
    (hEy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U)
    (hcomm : e.forward.comp (pointBlowupChartGerm ζ) =
      old.forward.comp ((pointBlowupChartGerm c).comp E.forward))
    (f g : Germ 2) (m : ℕ)
    (hfactor : (pointBlowupChartGerm ζ).pullbackRingHom (e.forward.pullbackRingHom f) =
      coordinate (1 : Fin 2) ^ m * g) :
    ∃ (F W : Germ 2), IsUnit W ∧ F = W * E.inverse.pullbackRingHom g ∧
      (pointBlowupChartGerm c).pullbackRingHom (old.forward.pullbackRingHom f) =
        coordinate (1 : Fin 2) ^ m * F := by
  obtain ⟨V, hV, hVy⟩ := exists_inverse_exceptional_unit E U hU hEy
  refine ⟨V ^ m * E.inverse.pullbackRingHom g, V ^ m, hV.pow m, rfl, ?_⟩
  have hcommf := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom f) hcomm
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at hcommf
  have h := congrArg E.inverse.pullbackRingHom (hcommf.symm.trans hfactor)
  change E.pullbackRingEquiv.symm (E.pullbackRingEquiv
    ((pointBlowupChartGerm c).pullbackRingHom (old.forward.pullbackRingHom f))) = _ at h
  rw [RingEquiv.symm_apply_apply, map_mul, map_pow, hVy, mul_pow, mul_assoc] at h
  exact h

end OnLeConjecture.Analytic.Germ
