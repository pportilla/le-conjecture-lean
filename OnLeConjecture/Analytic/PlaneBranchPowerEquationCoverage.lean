/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchClosedBraid
public import OnLeConjecture.Analytic.CurveImage

/-!
# The equation of a power-normalized analytic branch

Changing the source parameter preserves the exact equation ideal. The
power-normalized representative therefore covers the zero set of the given
equation near the origin, on a compact parameter disc on which it remains
injective. This connects the cylinder construction to the geometric branch.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

/-- An invertible change of the source parameter preserves the pullback kernel. -/
theorem PointedMapGerm.ker_pullback_comp_sourceEquiv
    (β : PointedMapGerm 1 2) (e : PointedEquivGerm 1) :
    RingHom.ker (β.comp e.inverse).pullbackRingHom = RingHom.ker β.pullbackRingHom := by
  rw [PointedMapGerm.pullbackRingHom_comp]
  exact RingHom.ker_comp_of_injective β.pullbackRingHom e.pullbackRingEquiv.symm.injective

/-- The actual power-normalized representative covers the nearby zero set of
the original equation, with injectivity and the power identity on the same
compact parameter disc. No change of target coordinates is made. -/
theorem PointedMapGerm.exists_injective_power_equation_coverage
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a)
    (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hker : RingHom.ker β.pullbackRingHom = Ideal.span {Germ.ofFunction W hW}) :
    ∃ (e : PointedEquivGerm 1) (G : Source 1 → Source 2)
      (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      β.comp e.inverse = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R : ℝ, 0 < R ∧
        let F : ℂ → EuclideanSpace ℂ (Fin 2) := fun z =>
          (EuclideanSpace.equiv (Fin 2) ℂ).symm (G (curveParameterEquiv.symm z))
        AnalyticAt ℂ F 0 ∧ F 0 = 0 ∧
        AnalyticOnNhd ℂ F (closedBall 0 R) ∧ InjOn F (closedBall 0 R) ∧
        (∀ z ∈ closedBall 0 R, F z i = z ^ a) ∧
        ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)),
          W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0 ↔
            y ∈ F '' closedBall 0 R := by
  obtain ⟨e, G, hG, hG0, hg, R₀, hR₀, _hFa, hFi, hp⟩ :=
    β.exists_injective_power_representative hi i ha ho
  let γ := PointedMapGerm.ofFunction G hG hG0
  have hγi : γ.HasInjectiveRepresentative := by
    dsimp only [γ]
    rw [← hg]
    exact β.comp_hasInjectiveRepresentative e.inverse hi e.inverse_hasInjectiveRepresentative
  have hγker : RingHom.ker γ.pullbackRingHom = Ideal.span {Germ.ofFunction W hW} := by
    dsimp only [γ]
    rw [← hg, β.ker_pullback_comp_sourceEquiv, hker]
  have hk : ∀ h, γ.pullbackRingHom h = 0 ↔ Germ.ofFunction W hW ∣ h := by
    intro h
    rw [← RingHom.mem_ker, hγker, Ideal.mem_span_singleton]
  let S : Set (Source 1) := curveParameterEquiv ⁻¹' ball 0 R₀
  have hS : S ∈ 𝓝 (0 : Source 1) := by
    have ht := curveParameterEquiv.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at ht
    exact ht.eventually (ball_mem_nhds (0 : ℂ) hR₀)
  have hGi : InjOn G S := by
    intro x hx y hy hxy
    apply curveParameterEquiv.injective
    apply hFi hx hy
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hxy
  obtain ⟨R, hR, hRS, hGa, _, _, hcoverage⟩ :=
    exists_curve_closedBall_image_eq_zero_set G hG hG0
      (γ.exists_nonzero_coordinate_pullback_of_injective_curve hγi) W hW hk S hS hGi
  let E := EuclideanSpace.equiv (Fin 2) ℂ
  let F : ℂ → EuclideanSpace ℂ (Fin 2) := fun z =>
    E.symm (G (curveParameterEquiv.symm z))
  have hF : AnalyticAt ℂ F 0 :=
    (E.symm.analyticAt _).comp
      (hG.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _))
  have hF0 : F 0 = 0 := by
    change E.symm (G (curveParameterEquiv.symm 0)) = 0
    rw [map_zero, hG0, map_zero]
  have hball (z : ℂ) : curveParameterEquiv.symm z ∈ closedBall 0 R ↔
      z ∈ closedBall 0 R := by
    simp only [mem_closedBall, dist_zero_right, curveParameterEquiv_symm_apply, pi_norm_const]
  have hFclosed : AnalyticOnNhd ℂ F (closedBall 0 R) := by
    intro z hz
    exact (E.symm.analyticAt _).comp
      ((hGa _ ((hball z).mpr hz)).comp (curveParameterEquiv.symm.analyticAt z))
  have hFinj : InjOn F (closedBall 0 R) := by
    intro z hz w hw hzw
    apply curveParameterEquiv.symm.injective
    exact hGi (hRS ((hball z).mpr hz)) (hRS ((hball w).mpr hw)) (E.symm.injective hzw)
  have hpower : ∀ z ∈ closedBall 0 R, F z i = z ^ a := by
    intro z hz
    apply hp
    have h := hRS ((hball z).mpr hz)
    simpa only [S, mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using h
  have ht : Tendsto E (𝓝 (0 : EuclideanSpace ℂ (Fin 2))) (𝓝 0) := by
    have ht := E.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at ht
    exact ht
  refine ⟨e, G, hG, hG0, hg, R, hR, hF, hF0, hFclosed, hFinj, hpower, ?_⟩
  filter_upwards [ht.eventually hcoverage] with y hy
  constructor
  · intro hWy
    obtain ⟨x, hx, hxy⟩ := hy.mp hWy
    refine ⟨curveParameterEquiv x, ?_, ?_⟩
    · exact (hball _).mp (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx)
    · change E.symm (G (curveParameterEquiv.symm (curveParameterEquiv x))) = y
      rw [ContinuousLinearEquiv.symm_apply_apply, hxy, ContinuousLinearEquiv.symm_apply_apply]
  · rintro ⟨z, hz, hzy⟩
    apply hy.mpr
    refine ⟨curveParameterEquiv.symm z, (hball z).mpr hz, ?_⟩
    have hv := congrArg E hzy
    simpa only [F, E, ContinuousLinearEquiv.apply_symm_apply] using hv

end OnLeConjecture.Analytic
