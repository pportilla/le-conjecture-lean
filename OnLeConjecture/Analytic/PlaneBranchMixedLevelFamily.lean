/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchMixedLevels
public import OnLeConjecture.Analytic.PlaneBranchClosedBraid
public import OnLeConjecture.Analytic.CurveJointRadialRadius
public import OnLeConjecture.Analytic.PlaneBranchMixedRadialLevels

/-!
# A family of mixed cylinder and sphere levels on an analytic branch

The radius solves one fixed positive mixed quadratic level. Uniqueness on
each ray identifies the chosen radius with the parameter-dependent implicit
function. Smoothness on the closed time interval includes its endpoints.
Composing with a smooth time map into that interval gives an ambient smooth
family without extending the radius by zero across an endpoint.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

/-- The mixed level equation is smooth jointly in parameter and time. -/
theorem planeMixedRadiusSq_curve_contDiffAt
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} {z : ℂ} (hF : AnalyticAt ℂ F z)
    (i : Fin 2) (t : ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℂ × ℝ => planeMixedRadiusSq i p.2 (F p.1)) (z, t) := by
  have he : ContDiff ℝ ∞ (EuclideanSpace.equiv (Fin 2) ℂ) :=
    (EuclideanSpace.equiv (Fin 2) ℂ).contDiff.restrict_scalars ℝ
  have hcoord : ContDiffAt ℝ ∞ (fun w => F w i) z :=
    (contDiff_apply ℝ ℂ i).contDiffAt.comp z
      (he.contDiffAt.comp z hF.restrictScalars.contDiffAt)
  exact ((contDiffAt_const.sub contDiffAt_snd).mul
    ((hcoord.norm_sq (𝕜 := ℂ)).comp (z, t) contDiffAt_fst)).add
      (contDiffAt_snd.mul
        ((hF.restrictScalars.contDiffAt.norm_sq (𝕜 := ℂ)).comp (z, t) contDiffAt_fst))

/-- At a positive regular radial point, the fixed mixed level has a smooth
local radius depending on both direction and time. -/
theorem exists_smooth_mixed_level_radius
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} (i : Fin 2)
    {u : ℂ} {t r : ℝ} (hr : 0 < r) (hF : AnalyticAt ℂ F (r • u))
    (hpos : 0 < fderiv ℝ (fun z => planeMixedRadiusSq i t (F z)) (r • u) (r • u)) :
    ∃ ρ : ℂ × ℝ → ℝ, ContDiffAt ℝ ∞ ρ (u, t) ∧ ρ (u, t) = r ∧
      ∀ᶠ p in 𝓝 (u, t),
        planeMixedRadiusSq i p.2 (F (ρ p • p.1)) = planeMixedRadiusSq i t (F (r • u)) := by
  let H : (ℂ × ℝ) × ℝ → ℝ := fun p =>
    planeMixedRadiusSq i p.1.2 (F (p.2 • p.1.1))
  have hm := planeMixedRadiusSq_curve_contDiffAt hF i t
  have hH : ContDiffAt ℝ ∞ H ((u, t), r) :=
    hm.comp ((u, t), r)
      ((contDiffAt_snd.smul (contDiffAt_fst.fst)).prodMk contDiffAt_fst.snd)
  have hs : ContDiffAt ℝ ∞ (fun z => planeMixedRadiusSq i t (F z)) (r • u) :=
    hm.comp (r • u) (contDiffAt_id.prodMk contDiffAt_const)
  let d : ℝ := fderiv ℝ (fun z => planeMixedRadiusSq i t (F z)) (r • u) u
  have hdpos : 0 < d := by
    rw [map_smul, smul_eq_mul] at hpos
    exact (mul_pos_iff_of_pos_left hr).mp hpos
  have hd : HasDerivAt (fun q : ℝ => H ((u, t), q)) d r := by
    change HasDerivAt ((fun z => planeMixedRadiusSq i t (F z)) ∘
      (fun q : ℝ => q • u))
      (fderiv ℝ (fun z => planeMixedRadiusSq i t (F z)) (r • u) u) r
    exact (hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      (by simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const u)
  have hpartial : fderiv ℝ H ((u, t), r) ∘L .inr ℝ (ℂ × ℝ) ℝ =
      ContinuousLinearEquiv.unitsEquivAut ℝ (.mk0 d hdpos.ne') := by
    have hd' : HasFDerivAt (fun q : ℝ => H ((u, t), q))
        (fderiv ℝ H ((u, t), r) ∘L .inr ℝ (ℂ × ℝ) ℝ) r :=
      (hH.differentiableAt (by simp)).hasFDerivAt.comp r
        (hasFDerivAt_prodMk_right (u, t) r)
    ext
    simpa using hd'.hasDerivAt.unique hd
  have hi : (fderiv ℝ H ((u, t), r) ∘L .inr ℝ (ℂ × ℝ) ℝ).IsInvertible :=
    ⟨_, hpartial.symm⟩
  have hdH := hH.hasStrictFDerivAt (by simp)
  let c := planeMixedRadiusSq i t (F (r • u))
  let J : ℂ × ℝ → (ℂ × ℝ) × ℝ := fun p => (p, c)
  let ρ := hdH.jointImplicitFunctionOfProdDomain hi ∘ J
  have hJ : ContDiff ℝ ∞ J := contDiff_id.prodMk contDiff_const
  refine ⟨ρ, (hdH.contDiffAt_jointImplicitFunctionOfProdDomain hi hH).comp (u, t)
    hJ.contDiffAt, hdH.jointImplicitFunctionOfProdDomain_apply_self hi, ?_⟩
  exact hJ.continuous.continuousAt.tendsto.eventually
    (hdH.eventually_apply_jointImplicitFunctionOfProdDomain hi)

section Radius

variable {F : ℂ → EuclideanSpace ℂ (Fin 2)} {i : Fin 2} {R c : ℝ}
    (hlevels : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Circle,
      ∃! r : ℝ, r ∈ Ioo 0 R ∧ planeMixedRadiusSq i t (F (r • (u : ℂ))) = c)

/-- The unique mixed-level radius, used only on the closed time interval. -/
def planeMixedLevelRadius (p : Circle × ℝ) : ℝ :=
  if hp : p.2 ∈ Icc (0 : ℝ) 1 then Classical.choose (hlevels p.2 hp p.1) else 0

theorem planeMixedLevelRadius_spec (p : Circle × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    planeMixedLevelRadius hlevels p ∈ Ioo 0 R ∧
      planeMixedRadiusSq i p.2 (F (planeMixedLevelRadius hlevels p • (p.1 : ℂ))) = c := by
  simp only [planeMixedLevelRadius, dif_pos hp]
  exact (Classical.choose_spec (hlevels p.2 hp p.1)).1

theorem planeMixedLevelRadius_eq_of_spec
    (p : Circle × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr : r ∈ Ioo 0 R)
    (heq : planeMixedRadiusSq i p.2 (F (r • (p.1 : ℂ))) = c) :
    planeMixedLevelRadius hlevels p = r :=
  (hlevels p.2 hp p.1).unique (planeMixedLevelRadius_spec hlevels p hp) ⟨hr, heq⟩

/-- Joint smoothness holds within the closed time interval, including
both endpoints. It does not assert smoothness of the zero extension. -/
theorem planeMixedLevelRadius_contMDiffWithinAt
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    (p : Circle × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    ContMDiffWithinAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (planeMixedLevelRadius hlevels) {q : Circle × ℝ | q.2 ∈ Icc (0 : ℝ) 1} p := by
  let r := planeMixedLevelRadius hlevels
  have hr := planeMixedLevelRadius_spec hlevels p hp
  have hnorm : ‖r p • (p.1 : ℂ)‖ = r p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1.1, Circle.norm_coe, mul_one]
  have hball : r p • (p.1 : ℂ) ∈ ball 0 R := by
    simpa only [mem_ball, dist_zero_right, hnorm] using hr.1.2
  have hnz : r p • (p.1 : ℂ) ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact hr.1.1)
  obtain ⟨ρ, hρ, hρ0, hsolve⟩ :=
    exists_smooth_mixed_level_radius i hr.1.1 (hF _ hball) (hpos p.2 hp _ hball hnz)
  rw [hr.2] at hsolve
  let J : Circle × ℝ → ℂ × ℝ := fun q => ((q.1 : ℂ), q.2)
  have hJ : Continuous J := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hJt : Tendsto J (𝓝 p) (𝓝 ((p.1 : ℂ), p.2)) := hJ.continuousAt.tendsto
  have hrho : ∀ᶠ q in 𝓝 p, ρ (J q) ∈ Ioo 0 R := by
    apply (hρ.continuousAt.tendsto.comp hJt).eventually
    exact isOpen_Ioo.mem_nhds (by rw [hρ0]; exact hr.1)
  have hagree : r =ᶠ[𝓝[{q : Circle × ℝ | q.2 ∈ Icc (0 : ℝ) 1}] p] fun q => ρ (J q) := by
    filter_upwards [self_mem_nhdsWithin, hrho.filter_mono nhdsWithin_le_nhds,
      (hJt.eventually hsolve).filter_mono nhdsWithin_le_nhds] with q hq ht hsol
    exact (hlevels q.2 hq q.1).unique (planeMixedLevelRadius_spec hlevels q hq) ⟨ht, hsol⟩
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun v : Circle => (v : ℂ)) :=
    contMDiff_coe_sphere
  have hJsmooth : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ × ℝ) ∞ J p :=
    (hcoe.contMDiffAt.comp p contMDiffAt_fst).prodMk_space contMDiffAt_snd
  exact (hρ.contMDiffAt.comp p hJsmooth).contMDiffWithinAt.congr_of_eventuallyEq_of_mem
    hagree hp

/-- Smooth time reparametrization into `[0,1]` gives a genuinely smooth
radius on the entire real time axis. -/
theorem planeMixedLevelRadius_reparam_contMDiff
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun p : Circle × ℝ => planeMixedLevelRadius hlevels (p.1, σ p.2)) := by
  intro p
  have hJ : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞
      (fun q : Circle × ℝ => (q.1, σ q.2)) p :=
    contMDiffAt_fst.prodMk (hσ.contMDiff.contMDiffAt.comp p contMDiffAt_snd)
  apply contMDiffWithinAt_univ.mp
  exact (planeMixedLevelRadius_contMDiffWithinAt hlevels hF hpos
    (p.1, σ p.2) (hσmem p.2)).comp p hJ.contMDiffWithinAt (fun q _ => hσmem q.2)

/-- The point of the parameter disc chosen by the mixed level equation. -/
def planeMixedLevelParameter (p : Circle × ℝ) : ℂ :=
  planeMixedLevelRadius hlevels p • (p.1 : ℂ)

theorem planeMixedLevelParameter_norm (p : Circle × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    ‖planeMixedLevelParameter hlevels p‖ = planeMixedLevelRadius hlevels p := by
  rw [planeMixedLevelParameter, norm_smul, Real.norm_eq_abs,
    abs_of_pos (planeMixedLevelRadius_spec hlevels p hp).1.1, Circle.norm_coe, mul_one]

theorem planeMixedLevelParameter_mem_ball (p : Circle × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    planeMixedLevelParameter hlevels p ∈ ball 0 R := by
  simpa only [mem_ball, dist_zero_right, planeMixedLevelParameter_norm hlevels p hp] using
    (planeMixedLevelRadius_spec hlevels p hp).1.2

theorem planeMixedLevelParameter_slice_injective {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective (fun u : Circle => planeMixedLevelParameter hlevels (u, t)) := by
  intro u v huv
  have hr := congrArg norm huv
  rw [planeMixedLevelParameter_norm hlevels (u, t) ht,
    planeMixedLevelParameter_norm hlevels (v, t) ht] at hr
  apply Circle.ext
  change planeMixedLevelRadius hlevels (u, t) • (u : ℂ) =
    planeMixedLevelRadius hlevels (v, t) • (v : ℂ) at huv
  rw [hr] at huv
  exact smul_right_injective ℂ (planeMixedLevelRadius_spec hlevels (v, t) ht).1.1.ne' huv

/-- The mixed-level circle normalized onto the ambient unit sphere. -/
def planeMixedLevelFamily (σ : ℝ → ℝ) (p : Circle × ℝ) : EuclideanSpace ℂ (Fin 2) :=
  planeRadialNormalization (F (planeMixedLevelParameter hlevels (p.1, σ p.2)))

theorem planeMixedLevel_curve_ne_zero (hc : c ≠ 0)
    (p : Circle × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) :
    F (planeMixedLevelParameter hlevels p) ≠ 0 := by
  intro hzero
  have hl := (planeMixedLevelRadius_spec hlevels p hp).2
  change planeMixedRadiusSq i p.2 (F (planeMixedLevelParameter hlevels p)) = c at hl
  exact hc (hl.symm.trans (by rw [hzero, planeMixedRadiusSq_zero]))

theorem planeMixedLevelFamily_norm (hc : c ≠ 0) {σ : ℝ → ℝ}
    (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) (p : Circle × ℝ) :
    ‖planeMixedLevelFamily hlevels σ p‖ = 1 :=
  norm_planeRadialNormalization (planeMixedLevel_curve_ne_zero hlevels hc _ (hσmem p.2))

/-- The normalized circles are jointly smooth after a smooth time change
with values in the closed interpolation interval. -/
theorem planeMixedLevelFamily_contMDiff
    (hc : c ≠ 0) (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (planeMixedLevelFamily hlevels σ) := by
  have hr := planeMixedLevelRadius_reparam_contMDiff hlevels hF hpos hσ hσmem
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun v : Circle => (v : ℂ)) :=
    contMDiff_coe_sphere
  have hparam : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × ℝ => planeMixedLevelParameter hlevels (p.1, σ p.2)) :=
    hr.smul (hcoe.comp contMDiff_fst)
  intro p
  have hcurve := ((hF _ (planeMixedLevelParameter_mem_ball hlevels (p.1, σ p.2)
    (hσmem p.2))).restrictScalars.contDiffAt.contMDiffAt).comp p hparam.contMDiffAt
  have hne := planeMixedLevel_curve_ne_zero hlevels hc (p.1, σ p.2) (hσmem p.2)
  have hn := (contDiffAt_norm ℂ hne).contMDiffAt.comp p hcurve
  exact (hn.inv₀ (norm_ne_zero_iff.mpr hne)).smul hcurve

/-- Every normalized mixed-level slice remains a closed embedding. -/
theorem planeMixedLevelFamily_slice_isClosedEmbedding
    (hc : c ≠ 0) (hF : AnalyticOnNhd ℂ F (ball 0 R)) (hinj : InjOn F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Topology.IsClosedEmbedding (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t)) := by
  have hs := (planeMixedLevelFamily_contMDiff hlevels hc hF hpos hσ hσmem).comp
    (contMDiff_id.prodMk (contMDiff_const (c := t)))
  apply hs.continuous.isClosedEmbedding
  intro u v huv
  apply planeMixedLevelParameter_slice_injective hlevels (hσmem t)
  apply hinj (planeMixedLevelParameter_mem_ball hlevels _ (hσmem t))
    (planeMixedLevelParameter_mem_ball hlevels _ (hσmem t))
  apply planeRadialNormalization_injOn_mixedLevel i (σ t) c hc
    (planeMixedLevelRadius_spec hlevels (u, σ t) (hσmem t)).2
    (planeMixedLevelRadius_spec hlevels (v, σ t) (hσmem t)).2 huv

/-- The cylinder endpoint has the constant positive power radius. -/
theorem planeMixedLevelRadius_zero
    {a : ℕ} (ha : 0 < a) (hpower : ∀ z ∈ ball 0 R, F z i = z ^ a) (u : Circle) :
    planeMixedLevelRadius hlevels (u, 0) = c ^ ((2 * a : ℕ) : ℝ)⁻¹ := by
  have ht : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hr := planeMixedLevelRadius_spec hlevels (u, 0) ht
  have hpow := hpower _ (planeMixedLevelParameter_mem_ball hlevels (u, 0) ht)
  have hc : (planeMixedLevelRadius hlevels (u, 0)) ^ (2 * a) = c := by
    have hl := hr.2
    change (1 - (0 : ℝ)) * ‖F (planeMixedLevelParameter hlevels (u, 0)) i‖ ^ 2 +
      0 * ‖F (planeMixedLevelParameter hlevels (u, 0))‖ ^ 2 = c at hl
    rw [hpow, norm_pow, planeMixedLevelParameter_norm hlevels _ ht] at hl
    simpa only [sub_zero, one_mul, zero_mul, add_zero, ← pow_mul, Nat.mul_comm a 2] using hl
  calc
    planeMixedLevelRadius hlevels (u, 0) =
        (planeMixedLevelRadius hlevels (u, 0) ^ (2 * a)) ^ ((2 * a : ℕ) : ℝ)⁻¹ :=
      (Real.pow_rpow_inv_natCast hr.1.1.le (by omega : 2 * a ≠ 0)).symm
    _ = c ^ ((2 * a : ℕ) : ℝ)⁻¹ := congrArg (fun x : ℝ => x ^ ((2 * a : ℕ) : ℝ)⁻¹) hc

/-- The selected coordinate of the normalized family is a positive real
multiple of the same angular power throughout the interpolation. -/
theorem planeMixedLevelFamily_coordinate
    (hc : c ≠ 0) {a : ℕ} (hpower : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {σ : ℝ → ℝ} (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) (p : Circle × ℝ) :
    ∃ b : ℝ, 0 < b ∧ planeMixedLevelFamily hlevels σ p i = b • (p.1 : ℂ) ^ a := by
  let q : Circle × ℝ := (p.1, σ p.2)
  let r := planeMixedLevelRadius hlevels q
  let y := F (planeMixedLevelParameter hlevels q)
  have hr : 0 < r := (planeMixedLevelRadius_spec hlevels q (hσmem p.2)).1.1
  have hy : y ≠ 0 := planeMixedLevel_curve_ne_zero hlevels hc q (hσmem p.2)
  refine ⟨‖y‖⁻¹ * r ^ a, mul_pos (inv_pos.mpr (norm_pos_iff.mpr hy)) (pow_pos hr _), ?_⟩
  change (‖y‖⁻¹ : ℝ) • y i = _
  have hcoord : y i = (r ^ a : ℝ) • (p.1 : ℂ) ^ a := by
    rw [show y i = (planeMixedLevelParameter hlevels q) ^ a from
      hpower _ (planeMixedLevelParameter_mem_ball hlevels q (hσmem p.2))]
    change (r • (p.1 : ℂ)) ^ a = _
    exact smul_pow r (p.1 : ℂ) a
  rw [hcoord, smul_smul]

/-- The phase of the selected coordinate is exactly the power covering. -/
theorem planeMixedLevelFamily_phase
    (hc : c ≠ 0) {a : ℕ} (hpower : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {σ : ℝ → ℝ} (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) (p : Circle × ℝ) :
    ‖planeMixedLevelFamily hlevels σ p i‖⁻¹ • planeMixedLevelFamily hlevels σ p i =
      (p.1 : ℂ) ^ a := by
  obtain ⟨b, hb, heq⟩ := planeMixedLevelFamily_coordinate hlevels hc hpower hσmem p
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hb, norm_pow, Circle.norm_coe,
    one_pow, mul_one, inv_smul_smul₀ hb.ne']

/-- The family never meets the axis of its covering coordinate. -/
theorem planeMixedLevelFamily_coordinate_ne_zero
    (hc : c ≠ 0) {a : ℕ} (hpower : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {σ : ℝ → ℝ} (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) (p : Circle × ℝ) :
    planeMixedLevelFamily hlevels σ p i ≠ 0 := by
  obtain ⟨b, hb, heq⟩ := planeMixedLevelFamily_coordinate hlevels hc hpower hσmem p
  rw [heq]
  exact smul_ne_zero hb.ne' (pow_ne_zero _ p.1.coe_ne_zero)

/-- At the cylinder endpoint the radius is independent of direction. -/
theorem planeMixedLevelFamily_at_zero
    {a : ℕ} (ha : 0 < a) (hpower : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {σ : ℝ → ℝ} {t : ℝ} (ht : σ t = 0) (u : Circle) :
    planeMixedLevelFamily hlevels σ (u, t) =
      planeRadialNormalization (F ((c ^ ((2 * a : ℕ) : ℝ)⁻¹) • (u : ℂ))) := by
  simp only [planeMixedLevelFamily, ht, planeMixedLevelParameter,
    planeMixedLevelRadius_zero hlevels ha hpower]

/-- At the sphere endpoint the unnormalized circle lies on the actual
Euclidean sphere of radius `sqrt c`. -/
theorem planeMixedLevelParameter_at_one_norm
    (u : Circle) :
    ‖F (planeMixedLevelParameter hlevels (u, 1))‖ = Real.sqrt c := by
  have hl := (planeMixedLevelRadius_spec hlevels (u, 1) ⟨zero_le_one, le_rfl⟩).2
  change (1 - (1 : ℝ)) * _ + 1 * ‖F (planeMixedLevelParameter hlevels (u, 1))‖ ^ 2 = c at hl
  simp only [sub_self, zero_mul, one_mul, zero_add] at hl
  exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hl)

/-- The sphere endpoint is the constant radial scaling of its actual
sphere-level points. -/
theorem planeMixedLevelFamily_at_one
    {σ : ℝ → ℝ} {t : ℝ} (ht : σ t = 1) (u : Circle) :
    planeMixedLevelFamily hlevels σ (u, t) =
      (Real.sqrt c)⁻¹ • F (planeMixedLevelParameter hlevels (u, 1)) := by
  simp only [planeMixedLevelFamily, ht, planeRadialNormalization,
    planeMixedLevelParameter_at_one_norm hlevels]

set_option backward.isDefEq.respectTransparency false in
/-- The phase identity makes the normalized mixed-level circles immersed. -/
theorem planeMixedLevelFamily_slice_mfderiv_injective
    (hc : c ≠ 0) (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    {a : ℕ} (ha : 0 < a) (hpower : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1)
    (t : ℝ) (u : Circle) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      (fun v : Circle => planeMixedLevelFamily hlevels σ (v, t)) u) := by
  let K : Circle → EuclideanSpace ℂ (Fin 2) := fun v => planeMixedLevelFamily hlevels σ (v, t)
  let P : EuclideanSpace ℂ (Fin 2) → ℂ := fun y => ‖y i‖⁻¹ • y i
  have hK : ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K :=
    (planeMixedLevelFamily_contMDiff hlevels hc hF hpos hσ hσmem).comp
      (contMDiff_id.prodMk (contMDiff_const (c := t)))
  have hi : K u i ≠ 0 := planeMixedLevelFamily_coordinate_ne_zero hlevels hc hpower hσmem (u, t)
  have hP : ContDiffAt ℝ ∞ P (K u) := by
    have hcoord : ContDiff ℝ ∞ (fun y : EuclideanSpace ℂ (Fin 2) => y i) :=
      (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) i).contDiff.restrict_scalars ℝ
    exact ((hcoord.contDiffAt.norm ℂ hi).inv (norm_ne_zero_iff.mpr hi)).smul hcoord.contDiffAt
  have heq : P ∘ K = fun v : Circle => (v : ℂ) ^ a :=
    funext (fun v => planeMixedLevelFamily_phase hlevels hc hpower hσmem (v, t))
  have hchain := mfderiv_comp u (hP.differentiableAt (by simp)).mdifferentiableAt
    (hK.mdifferentiableAt (by simp))
  have hdEq := mfderiv_congr (I := 𝓡 1) (I' := 𝓘(ℝ, ℂ)) (x := u) heq
  have hd : mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun v : Circle => (v : ℂ) ^ a) u =
      (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) 𝓘(ℝ, ℂ) P (K u)).comp
        (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) K u) := hdEq.symm.trans hchain
  intro v w hvw
  apply circle_pow_coe_mfderiv_injective ha u
  exact (congrArg (fun L => L v) hd).trans
    ((congrArg (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) 𝓘(ℝ, ℂ) P (K u)) hvw).trans
      (congrArg (fun L => L w) hd).symm)

/-- Each slice of the joint family is a native smooth embedding. -/
theorem planeMixedLevelFamily_slice_isSmoothEmbedding
    (hc : c ≠ 0) (hF : AnalyticOnNhd ℂ F (ball 0 R)) (hinj : InjOn F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    {a : ℕ} (ha : 0 < a) (hpower : ∀ z ∈ ball 0 R, F z i = z ^ a)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t)) := by
  have hs := (planeMixedLevelFamily_contMDiff hlevels hc hF hpos hσ hσmem).comp
    (contMDiff_id.prodMk (contMDiff_const (c := t)))
  exact hs.isSmoothEmbedding_of_injective_mfderiv (by simp)
    (planeMixedLevelFamily_slice_mfderiv_injective hlevels hc hF hpos ha hpower hσ hσmem t)
    (planeMixedLevelFamily_slice_isClosedEmbedding hlevels hc hF hinj hpos hσ hσmem t).isEmbedding

/-- The unnormalized sphere endpoint covers the entire sphere
intersection with the image of the open parameter disc. -/
theorem planeMixedLevelParameter_at_one_range
    (hc : 0 < c) (hF0 : F 0 = 0) :
    Set.range (fun u : Circle => F (planeMixedLevelParameter hlevels (u, 1))) =
      sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt c) ∩ F '' ball 0 R := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨mem_sphere_zero_iff_norm.mpr (planeMixedLevelParameter_at_one_norm hlevels u),
      planeMixedLevelParameter hlevels (u, 1),
      planeMixedLevelParameter_mem_ball hlevels (u, 1) ⟨zero_le_one, le_rfl⟩, rfl⟩
  · rintro ⟨hy, z, hz, rfl⟩
    have hz0 : z ≠ 0 := by
      intro h
      have hh := mem_sphere_zero_iff_norm.mp hy
      rw [h, hF0, norm_zero] at hh
      exact (Real.sqrt_pos.mpr hc).ne' hh.symm
    let u : Circle := ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)])⟩
    have hrecover : ‖z‖ • (u : ℂ) = z := by
      exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hz0) z
    have hr : ‖z‖ ∈ Ioo 0 R := ⟨norm_pos_iff.mpr hz0, by simpa [mem_ball] using hz⟩
    have hlevel : planeMixedRadiusSq i 1 (F (‖z‖ • (u : ℂ))) = c := by
      rw [hrecover]
      have hn := mem_sphere_zero_iff_norm.mp hy
      simp only [planeMixedRadiusSq, sub_self, zero_mul, one_mul, zero_add, hn,
        Real.sq_sqrt hc.le]
    have hradius := planeMixedLevelRadius_eq_of_spec hlevels (u, 1)
      ⟨zero_le_one, le_rfl⟩ hr hlevel
    refine ⟨u, ?_⟩
    simp only [planeMixedLevelParameter, hradius, hrecover]

/-- The final normalized image is precisely the actual sphere-level
image scaled by the constant `1 / sqrt c`. -/
theorem planeMixedLevelFamily_at_one_range
    (hc : 0 < c) (hF0 : F 0 = 0) {σ : ℝ → ℝ} {t : ℝ} (ht : σ t = 1) :
    Set.range (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t)) =
      (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ''
        (sphere 0 (Real.sqrt c) ∩ F '' ball 0 R) := by
  rw [show (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t)) =
    (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ∘
      (fun u : Circle => F (planeMixedLevelParameter hlevels (u, 1))) from
        funext (planeMixedLevelFamily_at_one hlevels ht)]
  rw [Set.range_comp, planeMixedLevelParameter_at_one_range hlevels hc hF0]

end Radius

/-- The given analytic branch determines a smooth family from a constant
parameter cylinder to its actual sphere level. The radius and level are
constructed inside any prescribed injective parameter neighborhood. -/
theorem exists_plane_branch_mixed_level_families
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (i : Fin 2) (a : ℕ) (ha : 0 < a)
    (hpower : ∀ᶠ z in 𝓝 (0 : ℂ), F z i = z ^ a)
    {S : Set ℂ} (hS : S ∈ 𝓝 0) (hinj : InjOn F S)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ closedBall (0 : ℂ) R ⊆ S ∧
      ∀ c : ℝ, 0 < c → c < R ^ (2 * a) →
      ∃ hlevels : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Circle,
          ∃! r : ℝ, r ∈ Ioo 0 R ∧ planeMixedRadiusSq i t (F (r • (u : ℂ))) = c,
        ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
          (planeMixedLevelFamily hlevels σ) ∧
        (∀ p, ‖planeMixedLevelFamily hlevels σ p‖ = 1) ∧
        (∀ t, Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
          (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t))) ∧
        (∀ p, ‖planeMixedLevelFamily hlevels σ p i‖⁻¹ • planeMixedLevelFamily hlevels σ p i =
          (p.1 : ℂ) ^ a) ∧
        (∀ t, σ t = 0 → ∀ u : Circle,
          planeMixedLevelFamily hlevels σ (u, t) =
            planeRadialNormalization (F ((c ^ ((2 * a : ℕ) : ℝ)⁻¹) • (u : ℂ)))) ∧
        ∀ t, σ t = 1 →
          Set.range (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t)) =
            (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ''
              (sphere 0 (Real.sqrt c) ∩ F '' ball 0 R) := by
  obtain ⟨R, hR, hRS, hAF, hp, hreg, hlevels⟩ :=
    exists_plane_mixed_radial_levels hF hF0 i a ha hpower hS
  refine ⟨R, hR, hRS, ?_⟩
  intro c hc hcR
  let hl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Circle,
      ∃! r : ℝ, r ∈ Ioo 0 R ∧ planeMixedRadiusSq i t (F (r • (u : ℂ))) = c :=
    fun t ht u => hlevels t ht u u.norm_coe c hc hcR
  have hFb : AnalyticOnNhd ℂ F (ball 0 R) := hAF.mono ball_subset_closedBall
  have hip : InjOn F (ball 0 R) := hinj.mono (ball_subset_closedBall.trans hRS)
  have hpb : ∀ z ∈ ball 0 R, F z i = z ^ a := fun z hz => hp z (ball_subset_closedBall hz)
  have hpos := fun t ht => (hreg t ht).2.2
  refine ⟨hl,
    planeMixedLevelFamily_contMDiff hl hc.ne' hFb hpos hσ hσmem,
    planeMixedLevelFamily_norm hl hc.ne' hσmem,
    planeMixedLevelFamily_slice_isSmoothEmbedding hl hc.ne' hFb hip hpos ha hpb hσ hσmem,
    planeMixedLevelFamily_phase hl hc.ne' hpb hσmem, ?_, ?_⟩
  · intro t ht u
    exact planeMixedLevelFamily_at_zero hl ha hpb ht u
  · intro t ht
    exact planeMixedLevelFamily_at_one_range hl hc hF0 ht

end OnLeConjecture.Analytic
