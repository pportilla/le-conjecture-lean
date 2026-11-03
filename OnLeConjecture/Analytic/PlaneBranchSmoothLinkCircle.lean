/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveSmoothEquationCircle

/-!
# Smoothness of the small-sphere link of an irreducible plane branch

The conclusion uses the Euclidean norm on the ambient complex plane.
The circle map is smooth with injective differential in the ambient
vector space. Its range is the entire intersection with the zero set
of the given representative equation. The parametrization and image
coverage are constructed from irreducibility.
-/

public noncomputable section

open Filter Set
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic.Germ

/-- The entire small-sphere zero set of an irreducible analytic plane
equation is a smooth circle with injective differential and a closed
embedding into the ambient sphere. -/
theorem exists_smooth_sphere_zero_set_circle_of_irreducible
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hirr : Irreducible (ofFunction H hH)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ L : Metric.sphere (0 : ℂ) 1 →
          Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) ε,
        Topology.IsClosedEmbedding L ∧
        ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
          (fun u => (L u : EuclideanSpace ℂ (Fin 2))) ∧
        (∀ u, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
          (fun v => (L v : EuclideanSpace ℂ (Fin 2))) u)) ∧
        Set.range (fun u => (L u : EuclideanSpace ℂ (Fin 2))) =
          Metric.sphere 0 ε ∩
            {y | H ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0} := by
  obtain ⟨γ, hinj, hn, hker⟩ :=
    exists_injective_parametrization_with_kernel_of_irreducible (ofFunction H hH) hirr
  obtain ⟨G, hG, hG0, rfl, S, hS, hGin⟩ := hinj
  obtain ⟨r, hr, hrS, hGr, _, _, himage⟩ :=
    exists_curve_closedBall_image_eq_zero_set G hG hG0 hn H hH hker S hS hGin
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let C : ℂ → EuclideanSpace ℂ (Fin 2) :=
    fun z => e.symm (G (curveParameterEquiv.symm z))
  have hC : AnalyticAt ℂ C 0 :=
    (e.symm.analyticAt _).comp
      (hG.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _))
  have hC0 : C 0 = 0 := by
    change e.symm (G (curveParameterEquiv.symm 0)) = 0
    rw [map_zero, hG0, map_zero]
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), C z = 0 := by
    intro hz
    have hcomponent : ∃ i, ((PointedMapGerm.ofFunction G hG hG0).1.component i) ≠ 0 := by
      simpa only [PointedMapGerm.pullback_coordinate] using hn
    apply curve_representative_not_eventually_zero G hG hG0 hcomponent
    filter_upwards [hz] with z h
    exact e.symm.injective (h.trans (map_zero _).symm)
  have hball (z : ℂ) : curveParameterEquiv.symm z ∈ Metric.closedBall 0 r ↔
      z ∈ Metric.closedBall 0 r := by
    simp only [Metric.mem_closedBall, dist_zero_right, curveParameterEquiv_symm_apply,
      pi_norm_const]
  have hcont : ContinuousOn C (Metric.closedBall 0 r) :=
    e.symm.continuous.comp_continuousOn
      (hGr.continuousOn.comp curveParameterEquiv.symm.continuous.continuousOn
        (fun z hz => (hball z).mpr hz))
  have hCin : InjOn C (Metric.closedBall 0 r) := by
    intro z hz w hw hzw
    apply curveParameterEquiv.symm.injective
    exact hGin (hrS ((hball z).mpr hz)) (hrS ((hball w).mpr hw))
      (e.symm.injective hzw)
  have he : Tendsto e (𝓝 (0 : EuclideanSpace ℂ (Fin 2))) (𝓝 0) := by
    have he := e.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at he
    exact he
  have himageC : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)),
      H (e y) = 0 ↔ y ∈ C '' Metric.closedBall 0 r := by
    filter_upwards [he.eventually himage] with y hy
    constructor
    · intro hHy
      obtain ⟨x, hx, hxy⟩ := hy.mp hHy
      refine ⟨curveParameterEquiv x, ?_, ?_⟩
      · exact (hball _).mp (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx)
      · change e.symm (G (curveParameterEquiv.symm (curveParameterEquiv x))) = y
        rw [ContinuousLinearEquiv.symm_apply_apply, hxy, ContinuousLinearEquiv.symm_apply_apply]
    · rintro ⟨z, hz, hzy⟩
      apply hy.mpr
      refine ⟨curveParameterEquiv.symm z, (hball z).mpr hz, ?_⟩
      have hv := congrArg e hzy
      simpa only [C, ContinuousLinearEquiv.apply_symm_apply] using hv
  exact exists_smooth_sphere_zero_set_circle_of_parametrization hr hC hC0 hne hcont hCin himageC

end OnLeConjecture.Analytic.Germ
