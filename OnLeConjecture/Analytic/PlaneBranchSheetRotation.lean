/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchClosedBraid
public import OnLeConjecture.Analytic.CurveRadialTransversality
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Angular variation of analytic branch sheets

For an injective analytic parametrization with one coordinate equal to `z^a`,
different roots of unity give distinct sheets in the complementary coordinate.
Their differences are nonzero analytic germs vanishing at the origin. The
logarithmic derivative, multiplied by the parameter, tends to the positive
vanishing order. Consequently its real part is positive on one punctured
neighborhood common to all nontrivial `a`th roots of unity.

This is a statement about the given analytic functions. It does not identify
a braid word, a grid diagram, or a knot Floer invariant.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology

namespace OnLeConjecture.Analytic

/-- The difference between two sheets of the power projection. -/
def planeBranchSheetDifference (F : ℂ → Source 2) (i : Fin 2) (ζ : ℂ) : ℂ → ℂ :=
  fun z => F (ζ * z) i.rev - F z i.rev

@[simp]
theorem planeBranchSheetDifference_zero (F : ℂ → Source 2) (i : Fin 2) (ζ : ℂ) :
    planeBranchSheetDifference F i ζ 0 = 0 := by
  simp [planeBranchSheetDifference]

/-- The sheet difference is analytic at the origin. -/
theorem planeBranchSheetDifference_analyticAt
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) (i : Fin 2) (ζ : ℂ) :
    AnalyticAt ℂ (planeBranchSheetDifference F i ζ) 0 := by
  have hf : AnalyticAt ℂ (fun z => F z i.rev) 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i.rev).analyticAt _).comp hF
  exact (hf.comp_of_eq (analyticAt_const.mul analyticAt_id) (mul_zero ζ)).sub hf

/-- Injectivity separates the sheets throughout the parameter ball. -/
theorem planeBranchSheetDifference_ne_zero
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ}
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {ζ : ℂ} (hζ : ζ ^ a = 1) (hζ1 : ζ ≠ 1)
    {z : ℂ} (hz : z ∈ ball 0 R) (hz0 : z ≠ 0) :
    planeBranchSheetDifference F i ζ z ≠ 0 := by
  have hnorm : ‖ζ‖ = 1 := (norm_pow_eq_one_iff ha ζ).mp (by rw [hζ, norm_one])
  have hrot : ζ * z ∈ ball 0 R := by
    simpa only [mem_ball, dist_zero_right, norm_mul, hnorm, one_mul] using hz
  intro hd
  have hother : F (ζ * z) i.rev = F z i.rev := sub_eq_zero.mp hd
  have heq : F (ζ * z) = F z := by
    ext j
    by_cases hji : j = i
    · subst j
      rw [hp _ hrot, hp _ hz, mul_pow, hζ, one_mul]
    · have hj : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
      simpa only [hj] using hother
  have he := hi hrot hz heq
  apply hζ1
  apply mul_right_cancel₀ hz0
  simpa only [one_mul] using he

/-- The actual sheet difference is not the zero germ. -/
theorem planeBranchSheetDifference_not_eventually_zero
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {ζ : ℂ} (hζ : ζ ^ a = 1) (hζ1 : ζ ≠ 1) :
    ¬ ∀ᶠ z in 𝓝 (0 : ℂ), planeBranchSheetDifference F i ζ z = 0 := by
  intro he
  have hball : ∀ᶠ z : ℂ in 𝓝 0, z ∈ ball 0 R := ball_mem_nhds (0 : ℂ) hR
  have hfalse : ∀ᶠ z in 𝓝[≠] (0 : ℂ), False := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      hball.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hzR hz0
    exact planeBranchSheetDifference_ne_zero ha hi hp hζ hζ1 hzR hz0 hz
  exact hfalse.exists.choose_spec

/-- The analytic germ represented by the sheet difference in the repository's
one-variable source coordinates. -/
def planeBranchSheetDifferenceGerm
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) (i : Fin 2) (ζ : ℂ) : Germ 1 :=
  Germ.ofFunction (fun z => planeBranchSheetDifference F i ζ (curveParameterEquiv z))
    ((planeBranchSheetDifference_analyticAt hF i ζ).comp_of_eq
      (curveParameterEquiv.analyticAt 0) (map_zero _))

theorem planeBranchSheetDifferenceGerm_mem_maximalIdeal
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) (i : Fin 2) (ζ : ℂ) :
    planeBranchSheetDifferenceGerm hF i ζ ∈ Germ.maximalIdeal 1 := by
  rw [Germ.mem_maximalIdeal_iff, planeBranchSheetDifferenceGerm,
    Germ.valueRingHom_ofFunction, map_zero, planeBranchSheetDifference_zero]

/-- The sheet difference defines a nonzero pointed analytic germ. -/
theorem planeBranchSheetDifferenceGerm_ne_zero
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) {i : Fin 2} {a : ℕ}
    (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {ζ : ℂ} (hζ : ζ ^ a = 1) (hζ1 : ζ ≠ 1) :
    planeBranchSheetDifferenceGerm hF i ζ ≠ 0 := by
  intro h
  have he : ∀ᶠ z : Source 1 in 𝓝 0,
      planeBranchSheetDifference F i ζ (curveParameterEquiv z) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 1 => q.1) h)
  have ht := curveParameterEquiv.symm.continuous.continuousAt.tendsto (x := 0)
  rw [map_zero] at ht
  apply planeBranchSheetDifference_not_eventually_zero ha hR hi hp hζ hζ1
  simpa only [curveParameterEquiv.apply_symm_apply] using ht.eventually he

set_option backward.isDefEq.respectTransparency false in
/-- The parameter times the logarithmic derivative tends to the exponent
of a nonvanishing analytic factorization. -/
theorem tendsto_mul_deriv_div_of_analytic_factor
    {f u : ℂ → ℂ} {d : ℕ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hf : f =ᶠ[𝓝 0] fun z => z ^ d * u z) :
    Tendsto (fun z => z * deriv f z / f z) (𝓝[≠] 0) (𝓝 (d : ℂ)) := by
  have hcont : ContinuousAt (logDeriv u) 0 :=
    hu.deriv.continuousAt.div hu.continuousAt hu0
  have ht : Tendsto (fun z : ℂ => (d : ℂ) + z * logDeriv u z)
      (𝓝[≠] 0) (𝓝 (d : ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ => (d : ℂ) + z * logDeriv u z) 0 :=
      continuousAt_const.add (continuousAt_id.mul hcont)
    simpa only [zero_mul, add_zero] using
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [(logDeriv_congr_nhds hf).filter_mono nhdsWithin_le_nhds,
    hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hu.continuousAt.eventually_ne hu0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z he hz huz hz0
  change z ∈ ({0} : Set ℂ)ᶜ at hz0
  have hzne : z ≠ 0 := hz0
  rw [show z * deriv f z / f z = z * logDeriv f z by rw [logDeriv_apply, mul_div_assoc], he,
    logDeriv_mul (f := fun w : ℂ => w ^ d) (g := u) z
      (pow_ne_zero _ hzne) huz (by fun_prop) hz.differentiableAt,
    logDeriv_pow, mul_add]
  field_simp

/-- A nonzero analytic germ vanishing at zero has positive actual order,
and that order is the logarithmic-derivative limit. -/
theorem exists_positive_order_tendsto_mul_deriv_div
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0) :
    ∃ d : ℕ, 0 < d ∧ analyticOrderAt f 0 = d ∧
      Tendsto (fun z => z * deriv f z / f z) (𝓝[≠] 0) (𝓝 (d : ℂ)) := by
  obtain ⟨d, u, hu, hu0, he⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hfactor : f =ᶠ[𝓝 0] fun z => z ^ d * u z := by
    filter_upwards [he] with z hz
    simpa only [sub_zero, smul_eq_mul] using hz
  have hd : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := by omega
    have h0 := hfactor.self_of_nhds
    simp only [hd0, pow_zero, one_mul, hf0] at h0
    exact hu0 h0.symm
  exact ⟨d, hd, hf.analyticOrderAt_eq_natCast.mpr ⟨u, hu, hu0, he⟩,
    tendsto_mul_deriv_div_of_analytic_factor hu hu0 hfactor⟩

/-- Positive order makes the angular logarithmic derivative positive near zero. -/
theorem eventually_re_mul_deriv_div_pos
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), 0 < (z * deriv f z / f z).re := by
  obtain ⟨d, hd, _, ht⟩ := exists_positive_order_tendsto_mul_deriv_div hf hf0 hne
  have hreal : Tendsto (fun z => (z * deriv f z / f z).re)
      (𝓝[≠] (0 : ℂ)) (𝓝 (d : ℝ)) := by
    simpa only [Function.comp_def, Complex.natCast_re] using
      Complex.continuous_re.continuousAt.tendsto.comp ht
  exact hreal.eventually (Ioi_mem_nhds (show (0 : ℝ) < d by exact_mod_cast hd))

/-- The function's finite analytic order is also the vanishing order of its
sheet-difference germ. -/
theorem planeBranchSheetDifferenceGerm_vanishingOrder
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) (i : Fin 2) (ζ : ℂ)
    {d : ℕ} (hd : analyticOrderAt (planeBranchSheetDifference F i ζ) 0 = d) :
    Germ.vanishingOrder (planeBranchSheetDifferenceGerm hF i ζ) = d := by
  obtain ⟨u, hu, hu0, he⟩ :=
    (planeBranchSheetDifference_analyticAt hF i ζ).analyticOrderAt_eq_natCast.mp hd
  let v : Germ 1 := Germ.ofFunction (fun z => u (curveParameterEquiv z))
    (hu.comp_of_eq (curveParameterEquiv.analyticAt 0) (map_zero _))
  have hv : IsUnit v := Germ.isUnit_of_valueRingHom_ne_zero (by
    rw [Germ.valueRingHom_ofFunction, map_zero]
    exact hu0)
  apply Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hv
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have ht := curveParameterEquiv.continuous.continuousAt.tendsto (x := 0)
  rw [map_zero] at ht
  filter_upwards [ht.eventually he] with z hz
  change planeBranchSheetDifference F i ζ (curveParameterEquiv z) =
    z 0 ^ d * u (curveParameterEquiv z)
  simpa only [sub_zero, smul_eq_mul, curveParameterEquiv_apply] using hz

/-- Each nontrivial root gives a positive finite vanishing order. The
angular logarithmic derivative tends to that actual order. -/
theorem planeBranchSheetDifference_exists_positive_order
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) {i : Fin 2} {a : ℕ}
    (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {ζ : ℂ} (hζ : ζ ^ a = 1) (hζ1 : ζ ≠ 1) :
    ∃ d : ℕ, 0 < d ∧
      analyticOrderAt (planeBranchSheetDifference F i ζ) 0 = d ∧
      Germ.vanishingOrder (planeBranchSheetDifferenceGerm hF i ζ) = d ∧
      Tendsto (fun z => z * deriv (planeBranchSheetDifference F i ζ) z /
        planeBranchSheetDifference F i ζ z) (𝓝[≠] 0) (𝓝 (d : ℂ)) := by
  obtain ⟨d, hd, ho, ht⟩ := exists_positive_order_tendsto_mul_deriv_div
    (planeBranchSheetDifference_analyticAt hF i ζ) (planeBranchSheetDifference_zero F i ζ)
    (planeBranchSheetDifference_not_eventually_zero ha hR hi hp hζ hζ1)
  exact ⟨d, hd, ho, planeBranchSheetDifferenceGerm_vanishingOrder hF i ζ ho, ht⟩

/-- Each sheet difference has strictly positive angular logarithmic
derivative on a punctured neighborhood of zero. -/
theorem planeBranchSheetDifference_eventually_re_pos
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) {i : Fin 2} {a : ℕ}
    (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {ζ : ℂ} (hζ : ζ ^ a = 1) (hζ1 : ζ ≠ 1) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
        planeBranchSheetDifference F i ζ z).re :=
  eventually_re_mul_deriv_div_pos (planeBranchSheetDifference_analyticAt hF i ζ)
    (planeBranchSheetDifference_zero F i ζ)
    (planeBranchSheetDifference_not_eventually_zero ha hR hi hp hζ hζ1)

/-- One positive radius works for every nontrivial `a`th root of unity. -/
theorem exists_radius_planeBranchSheetDifference_re_pos
    {F : ℂ → Source 2} (hF : AnalyticAt ℂ F 0) {i : Fin 2} {a : ℕ}
    (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 →
        ∀ z ∈ ball 0 ρ, z ≠ 0 →
          planeBranchSheetDifference F i ζ z ≠ 0 ∧
          0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
            planeBranchSheetDifference F i ζ z).re := by
  let : NeZero a := ⟨ha.ne'⟩
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ ζ : rootsOfUnity a ℂ,
      ((ζ.val : ℂ) ≠ 1) →
        0 < (z * deriv (planeBranchSheetDifference F i (ζ.val : ℂ)) z /
          planeBranchSheetDifference F i (ζ.val : ℂ) z).re := by
    apply eventually_all.mpr
    intro ζ
    by_cases hζ1 : (ζ.val : ℂ) = 1
    · exact Filter.Eventually.of_forall fun _ h => (h hζ1).elim
    · have hζ : (ζ.val : ℂ) ^ a = 1 :=
        congrArg (fun u : ℂˣ => (u : ℂ)) ζ.property
      exact (planeBranchSheetDifference_eventually_re_pos hF ha hR hi hp hζ hζ1).mono
        (fun _ hz _ => hz)
  have hall' : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → ∀ ζ : rootsOfUnity a ℂ,
      ((ζ.val : ℂ) ≠ 1) →
        0 < (z * deriv (planeBranchSheetDifference F i (ζ.val : ℂ)) z /
          planeBranchSheetDifference F i (ζ.val : ℂ) z).re := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hall
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hall'
  refine ⟨min R r, lt_min hR hr, min_le_left _ _, ?_⟩
  intro ζ hζ hζ1 z hz hz0
  have hzR : z ∈ ball 0 R := ball_subset_ball (min_le_left _ _) hz
  have hzr : z ∈ ball 0 r := ball_subset_ball (min_le_right _ _) hz
  have hζ0 : ζ ≠ 0 := by
    intro he
    simp only [he, zero_pow ha.ne'] at hζ
    exact zero_ne_one hζ
  let u : rootsOfUnity a ℂ := ⟨Units.mk0 ζ hζ0, by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using hζ⟩
  exact ⟨planeBranchSheetDifference_ne_zero ha hi hp hζ hζ1 hzR hz0,
    hb hzr hz0 u hζ1⟩

/-- Source normalization and one common radius give the angular positivity
for the actual injective representative of the given branch germ. -/
theorem PointedMapGerm.exists_injective_power_representative_sheetRotation
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a) :
    ∃ (e : PointedEquivGerm 1) (G : Source 1 → Source 2)
      (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      β.comp e.inverse = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R : ℝ, 0 < R ∧
        let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
        AnalyticOnNhd ℂ F (ball 0 R) ∧ InjOn F (ball 0 R) ∧
        (∀ z ∈ ball 0 R, F z i = z ^ a) ∧
        ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 →
          ∀ z ∈ ball 0 R, z ≠ 0 →
            planeBranchSheetDifference F i ζ z ≠ 0 ∧
            0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
              planeBranchSheetDifference F i ζ z).re := by
  obtain ⟨e, G, hG, hG0, hg, R, hR, hF, hinj, hp⟩ :=
    β.exists_injective_power_representative hi i ha ho
  obtain ⟨ρ, hρ, hρR, hrot⟩ := exists_radius_planeBranchSheetDifference_re_pos
    (hF 0 (mem_ball_self hR)) ha hR hinj hp
  have hsub : ball (0 : ℂ) ρ ⊆ ball 0 R := ball_subset_ball hρR
  exact ⟨e, G, hG, hG0, hg, ρ, hρ, hF.mono hsub, hinj.mono hsub,
    fun z hz => hp z (hsub hz), hrot⟩

end OnLeConjecture.Analytic
