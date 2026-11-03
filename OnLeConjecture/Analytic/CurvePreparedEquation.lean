/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PreparedFiniteProjection
public import OnLeConjecture.Analytic.InjectiveCurveParametrization

/-!
# A prepared equation for the parameter of a nonconstant curve

Preparing a nonzero coordinate function minus its target coordinate gives
a monic equation for the curve parameter. Its coefficients are analytic
functions of the target point and vanish at the origin.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open LocalComplexGeometry ClassicalComplexWPT

/-- A nonzero pointed curve component gives a prepared polynomial equation
for the source parameter with analytic target coefficients. -/
theorem exists_curve_parameter_prepared_equation
    {m : ℕ} (G : Source 1 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (i : Fin m)
    (hne : (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom (Germ.coordinate i) ≠ 0) :
    ∃ (d : ℕ), 0 < d ∧ ∃ a : Fin d → Source m → ℂ,
      (∀ k, AnalyticAt ℂ (a k) 0) ∧ (∀ k, a k 0 = 0) ∧
      ∀ᶠ x in 𝓝 0, preparedValue a (G x) (x 0) = 0 := by
  let e : Source 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
  let c : ℂ → ℂ := fun t => G (e.symm t) i
  have hc : AnalyticAt ℂ c 0 := by
    have hcomp : AnalyticAt ℂ (fun t => G (e.symm t)) 0 := by
      apply hG.comp_of_eq (e.symm.analyticAt 0)
      exact map_zero _
    exact (analyticAt_pi_iff.mp hcomp) i
  have hc0 : c 0 = 0 := by simp only [c, map_zero, hG0, Pi.zero_apply]
  have hctop : ¬ ∀ᶠ t in 𝓝 (0 : ℂ), c t = 0 := by
    intro hzero
    apply hne
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    have he : Tendsto e (𝓝 (0 : Source 1)) (𝓝 0) := by
      have he0 : e (0 : Source 1) = 0 := map_zero e
      have heContinuous : ContinuousAt e (0 : Source 1) := e.continuous.continuousAt
      change Tendsto e (𝓝 0) (𝓝 (e 0)) at heContinuous
      rw [he0] at heContinuous
      exact heContinuous
    filter_upwards [he.eventually hzero] with x hx
    change G x i = 0
    simpa only [c, e.symm_apply_apply] using hx
  obtain ⟨d, v, hv, hv0, hfactor⟩ :=
    hc.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hctop
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    have h0 := hfactor.self_of_nhds
    rw [hd0, pow_zero, one_smul, hc0] at h0
    exact hv0 h0.symm
  let H : Ambient m → ℂ := fun z => c z.2 - z.1 i
  have hcs : AnalyticAt ℂ (fun z : Ambient m => c z.2) 0 := by
    apply hc.comp_of_eq ((ContinuousLinearMap.snd ℂ (Base m) ℂ).analyticAt 0)
    exact map_zero _
  have hH : AnalyticAt ℂ H 0 :=
    hcs.sub (((ContinuousLinearMap.proj (R := ℂ) i).comp
      (ContinuousLinearMap.fst ℂ (Base m) ℂ)).analyticAt 0)
  have hslice : lastSlice H = c := by
    funext t
    simp only [lastSlice, H, Pi.zero_apply, sub_zero]
  have horder : ExactOrderInLastVariable H d := by
    rw [exactOrderInLastVariable_iff_analyticOrderAt hH, hslice]
    exact hc.analyticOrderAt_eq_natCast.mpr ⟨v, hv, hv0, hfactor⟩
  obtain ⟨a, u, W, hprep, hW, hW0, hu, hfact⟩ :=
    exists_open_preparation_neighborhood m d H hH horder
  have hGt : Tendsto (fun x : Source 1 => (G x, e x)) (𝓝 0) (𝓝 0) := by
    have h := (hG.continuousAt.prodMk e.continuous.continuousAt).tendsto
    simpa only [hG0, map_zero, Prod.mk_zero_zero] using h
  refine ⟨d, hd, a, hprep.1, hprep.2.1, ?_⟩
  filter_upwards [hGt.eventually (hW.mem_nhds hW0)] with x hx
  have h := hfact (G x, e x) hx
  have hHzero : H (G x, e x) = 0 := by
    simp only [H, c, e.symm_apply_apply, sub_self]
  rw [hHzero] at h
  have hpoly := (mul_eq_zero.mp h.symm).resolve_left (hu _ hx)
  simpa only [preparedPolynomial, preparedValue, e,
    ContinuousLinearEquiv.piUnique_apply, Fin.default_eq_zero] using hpoly

end OnLeConjecture.Analytic
