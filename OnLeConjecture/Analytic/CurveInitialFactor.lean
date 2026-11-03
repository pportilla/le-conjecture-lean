/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveFinite
public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.CurveRadialTransversality
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Initial factors of nonconstant analytic curves

A nonconstant analytic curve centered at the origin admits a factorization
`F(z) = z^d • U(z)` near the origin, with positive exponent and nonzero
`U(0)`. The vector-valued analytic factorization theorem supplies this
factor directly. The conclusions below retain actual representatives,
an explicit neighborhood, and the Euclidean target norm needed for radial
transversality.
-/

public noncomputable section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

/-- A centered analytic curve that is not locally zero has a positive
initial exponent and a nonvanishing analytic vector factor. -/
theorem exists_positive_curve_initial_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∃ d : ℕ, 0 < d ∧ ∃ U : ℂ → E,
      AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
      F =ᶠ[𝓝 0] fun z => z ^ d • U z := by
  obtain ⟨d, U, hU, hU0, hfactor⟩ :=
    hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    have hzero := hfactor.self_of_nhds
    rw [hd0, pow_zero, one_smul, hF0] at hzero
    exact hU0 hzero.symm
  exact ⟨d, hd, U, hU, hU0, by simpa only [Filter.EventuallyEq, sub_zero] using hfactor⟩

/-- The initial vector factor is analytic and nonzero throughout a small
ball on which its factorization is an equality of actual functions. -/
theorem exists_positive_curve_initial_factor_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∃ d : ℕ, 0 < d ∧ ∃ U : ℂ → E, ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ U (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, U z ≠ 0) ∧
      ∀ z ∈ Metric.ball 0 r, F z = z ^ d • U z := by
  obtain ⟨d, hd, U, hU, hU0, hfactor⟩ :=
    exists_positive_curve_initial_factor hF hF0 hne
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hU.eventually_analyticAt.and
      ((hU.continuousAt.eventually_ne hU0).and hfactor))
  refine ⟨d, hd, U, r, hr, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball (by simpa only [Metric.mem_ball] using hz)).1
  · intro z hz
    exact (hball (by simpa only [Metric.mem_ball] using hz)).2.1
  · intro z hz
    exact (hball (by simpa only [Metric.mem_ball] using hz)).2.2

/-- Every centered nonconstant analytic curve in a complex inner product
space has positive radial derivative of its squared norm near the origin. -/
theorem eventually_nonconstant_curve_norm_radial_derivative_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z := by
  obtain ⟨d, hd, U, hU, hU0, hfactor⟩ :=
    exists_positive_curve_initial_factor hF hF0 hne
  exact eventually_curve_norm_radial_derivative_pos
    (hU.restrictScalars.contDiffAt) hU0 hd hfactor

/-- The squared norm of a centered nonconstant analytic curve has
surjective real differential on a sufficiently small punctured neighborhood. -/
theorem eventually_nonconstant_curve_norm_sq_fderiv_surjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      Function.Surjective (fderiv ℝ (fun w => ‖F w‖ ^ 2) z) := by
  obtain ⟨d, hd, U, hU, hU0, hfactor⟩ :=
    exists_positive_curve_initial_factor hF hF0 hne
  exact eventually_curve_norm_sq_fderiv_surjective
    (hU.restrictScalars.contDiffAt) hU0 hd hfactor

/-- The constant-coordinate parameter identifies `ℂ` with the
one-dimensional source space. -/
@[expose] def curveParameterEquiv : Source 1 ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)

@[simp] theorem curveParameterEquiv_apply (x : Source 1) :
    curveParameterEquiv x = x 0 := rfl

@[simp] theorem curveParameterEquiv_symm_apply (z : ℂ) :
    curveParameterEquiv.symm z = fun _ => z := rfl

/-- A nonzero component germ prevents a curve representative from being
locally zero after the scalar parameter identification. -/
theorem curve_representative_not_eventually_zero
    {n : ℕ} (G : Source 1 → Source n) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hne : ∃ i, ((PointedMapGerm.ofFunction G hG hG0).1.component i) ≠ 0) :
    ¬ ∀ᶠ z in 𝓝 (0 : ℂ), G (curveParameterEquiv.symm z) = 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := hne
  apply hi
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have he : Tendsto curveParameterEquiv (𝓝 (0 : Source 1)) (𝓝 0) := by
    have h := curveParameterEquiv.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at h
    exact h
  filter_upwards [he.eventually hzero] with x hx
  change G x i = 0
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Pi.zero_apply] using congrFun hx i

/-- The initial exponent is a lower bound for every component order and
is attained by a component whose factor is nonzero at the origin. -/
theorem component_orders_of_curve_initial_factor
    {n : ℕ} (G : Source 1 → Source n) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (U : ℂ → Source n) (hU : AnalyticAt ℂ U 0) (hU0 : U 0 ≠ 0) (d : ℕ)
    (hfactor : (fun z => G (curveParameterEquiv.symm z)) =ᶠ[𝓝 0]
      fun z => z ^ d • U z) :
    (∀ i, (d : ℕ∞) ≤ Germ.vanishingOrder
      ((PointedMapGerm.ofFunction G hG hG0).1.component i)) ∧
    ∃ i, Germ.vanishingOrder
      ((PointedMapGerm.ofFunction G hG hG0).1.component i) = d := by
  let H : Source 1 → Source n := fun x => U (curveParameterEquiv x)
  have hH : AnalyticAt ℂ H 0 :=
    hU.comp_of_eq (curveParameterEquiv.analyticAt 0) (map_zero _)
  let u : Fin n → Germ 1 := fun i =>
    Germ.ofFunction (fun x => H x i) ((analyticAt_pi_iff.mp hH) i)
  have he : Tendsto curveParameterEquiv (𝓝 (0 : Source 1)) (𝓝 0) := by
    have h := curveParameterEquiv.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at h
    exact h
  have hcomponent (i : Fin n) :
      (PointedMapGerm.ofFunction G hG hG0).1.component i = Germ.coordinate 0 ^ d * u i := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [he.eventually hfactor] with x hx
    change G x i = (x 0) ^ d * U (curveParameterEquiv x) i
    have hh : G x i = (curveParameterEquiv x) ^ d * U (curveParameterEquiv x) i := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun hx i
    simpa only [curveParameterEquiv_apply] using hh
  constructor
  · intro i
    rw [← Germ.vanishingOrder_coordinate_pow d, Germ.vanishingOrder_le_iff_dvd]
    exact ⟨u i, hcomponent i⟩
  · obtain ⟨i, hi⟩ : ∃ i, U 0 i ≠ 0 := by
      by_contra! h
      exact hU0 (funext h)
    refine ⟨i, Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit ?_ (hcomponent i)⟩
    apply Germ.isUnit_of_valueRingHom_ne_zero
    change U (curveParameterEquiv 0) i ≠ 0
    rw [map_zero]
    exact hi

namespace PointedMapGerm

/-- Every nonconstant pointed curve germ has an actual Euclidean-valued
representative with a positive initial parameter power and nonzero factor. -/
theorem exists_euclidean_curve_initial_factor
    {n : ℕ} (g : PointedMapGerm 1 n)
    (hne : ∃ i, g.1.component i ≠ 0) :
    ∃ G : Source 1 → Source n, ∃ hG : AnalyticAt ℂ G 0, ∃ hG0 : G 0 = 0,
      g = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ d : ℕ, 0 < d ∧ ∃ U : ℂ → EuclideanSpace ℂ (Fin n),
        AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
        (fun z => (EuclideanSpace.equiv (Fin n) ℂ).symm
          (G (curveParameterEquiv.symm z))) =ᶠ[𝓝 0] fun z => z ^ d • U z := by
  obtain ⟨G, hG, hG0, rfl⟩ := g.exists_ofFunction
  let F : ℂ → EuclideanSpace ℂ (Fin n) := fun z =>
    (EuclideanSpace.equiv (Fin n) ℂ).symm (G (curveParameterEquiv.symm z))
  have hF : AnalyticAt ℂ F 0 := by
    exact ((EuclideanSpace.equiv (Fin n) ℂ).symm.analyticAt _).comp
      (hG.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _))
  have hF0 : F 0 = 0 := by
    change (EuclideanSpace.equiv (Fin n) ℂ).symm
      (G (curveParameterEquiv.symm 0)) = 0
    rw [map_zero, hG0, map_zero]
  have hnF : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0 := by
    intro hz
    apply curve_representative_not_eventually_zero G hG hG0 hne
    filter_upwards [hz] with z h
    exact (EuclideanSpace.equiv (Fin n) ℂ).symm.injective (h.trans (map_zero _).symm)
  refine ⟨G, hG, hG0, rfl, ?_⟩
  exact exists_positive_curve_initial_factor hF hF0 hnF

/-- An injective curve germ has a Euclidean representative and an initial
factor on one ball where both maps are analytic, the representative is
injective, and the factor does not vanish. -/
theorem exists_injective_euclidean_curve_initial_factor_on_ball
    {n : ℕ} (g : PointedMapGerm 1 n) (hi : g.HasInjectiveRepresentative) :
    ∃ G : Source 1 → Source n, ∃ hG : AnalyticAt ℂ G 0, ∃ hG0 : G 0 = 0,
      g = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ d : ℕ, 0 < d ∧ ∃ U : ℂ → EuclideanSpace ℂ (Fin n),
      ∃ r : ℝ, 0 < r ∧
        let F : ℂ → EuclideanSpace ℂ (Fin n) := fun z =>
          (EuclideanSpace.equiv (Fin n) ℂ).symm (G (curveParameterEquiv.symm z))
        AnalyticOnNhd ℂ F (Metric.ball 0 r) ∧ Set.InjOn F (Metric.ball 0 r) ∧
        AnalyticOnNhd ℂ U (Metric.ball 0 r) ∧
        (∀ z ∈ Metric.ball 0 r, U z ≠ 0) ∧
        ∀ z ∈ Metric.ball 0 r, F z = z ^ d • U z := by
  have hne : ∃ i, g.1.component i ≠ 0 := by
    simpa only [pullback_coordinate] using
      g.exists_nonzero_coordinate_pullback_of_injective_curve hi
  obtain ⟨G, hG, hG0, rfl, S, hS, hGin⟩ := hi
  let F : ℂ → EuclideanSpace ℂ (Fin n) := fun z =>
    (EuclideanSpace.equiv (Fin n) ℂ).symm (G (curveParameterEquiv.symm z))
  have hF : AnalyticAt ℂ F 0 := by
    exact ((EuclideanSpace.equiv (Fin n) ℂ).symm.analyticAt _).comp
      (hG.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _))
  have hF0 : F 0 = 0 := by
    change (EuclideanSpace.equiv (Fin n) ℂ).symm
      (G (curveParameterEquiv.symm 0)) = 0
    rw [map_zero, hG0, map_zero]
  have hnF : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0 := by
    intro hz
    apply curve_representative_not_eventually_zero G hG hG0 hne
    filter_upwards [hz] with z h
    exact (EuclideanSpace.equiv (Fin n) ℂ).symm.injective (h.trans (map_zero _).symm)
  obtain ⟨d, hd, U, hU, hU0, hfactor⟩ :=
    exists_positive_curve_initial_factor hF hF0 hnF
  have hS' : ∀ᶠ z in 𝓝 (0 : ℂ), curveParameterEquiv.symm z ∈ S := by
    have he := curveParameterEquiv.symm.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at he
    exact he.eventually hS
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hF.eventually_analyticAt.and (hU.eventually_analyticAt.and
      (hS'.and ((hU.continuousAt.eventually_ne hU0).and hfactor))))
  have hb (z : ℂ) (hz : z ∈ Metric.ball 0 r) :=
    hball (by simpa only [Metric.mem_ball] using hz)
  refine ⟨G, hG, hG0, rfl, d, hd, U, r, hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hb z hz).1
  · intro z hz w hw hzw
    apply curveParameterEquiv.symm.injective
    apply hGin (hb z hz).2.2.1 (hb w hw).2.2.1
    exact (EuclideanSpace.equiv (Fin n) ℂ).symm.injective hzw
  · intro z hz
    exact (hb z hz).2.1
  · intro z hz
    exact (hb z hz).2.2.2.1
  · intro z hz
    exact (hb z hz).2.2.2.2

end PointedMapGerm

end OnLeConjecture.Analytic
