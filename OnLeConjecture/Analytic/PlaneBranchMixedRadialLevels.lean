/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchMixedLevels
public import OnLeConjecture.Analytic.CurveAnalyticRadialLevels

/-!
# Uniform radial levels between a branch cylinder and a sphere

A selected coordinate equal to z^a gives the same positive boundary lower
bound for every mixed level. The existing analytic radial derivative theorem
for the scalar coordinate and the full curve supplies their common parameter ball.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open Filter Metric Set
open scoped Topology ContDiff

/-- A common ball and level interval work for every interpolated cylinder/sphere equation. -/
theorem exists_plane_mixed_radial_levels
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (i : Fin 2) (a : ℕ) (ha : 0 < a)
    (hpower : ∀ᶠ z in 𝓝 (0 : ℂ), F z i = z ^ a)
    {S : Set ℂ} (hS : S ∈ 𝓝 0) :
    ∃ R : ℝ, 0 < R ∧ closedBall (0 : ℂ) R ⊆ S ∧
      AnalyticOnNhd ℂ F (closedBall 0 R) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, F z i = z ^ a) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        ContinuousOn (fun z => planeMixedRadiusSq i t (F z)) (closedBall 0 R) ∧
        (∀ z ∈ ball (0 : ℂ) R,
          ContDiffAt ℝ ∞ (fun w => planeMixedRadiusSq i t (F w)) z) ∧
        (∀ z ∈ ball (0 : ℂ) R, z ≠ 0 →
          0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℂ, ‖u‖ = 1 → ∀ c : ℝ, 0 < c → c < R ^ (2 * a) →
        ∃! r : ℝ, r ∈ Ioo 0 R ∧ planeMixedRadiusSq i t (F (r • u)) = c := by
  have hFi : AnalyticAt ℂ (fun z => F z i) 0 :=
    ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) i).analyticAt (F 0)).comp hF
  have hFi0 : F 0 i = 0 := by rw [hF0]; rfl
  have hni : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z i = 0 := by
    intro hzero
    have hz : ∀ᶠ z in 𝓝 (0 : ℂ), z = 0 := by
      filter_upwards [hzero, hpower] with z h0 hp
      exact (pow_eq_zero_iff ha.ne').mp (hp.symm.trans h0)
    obtain ⟨z, hz0, hzne⟩ := ((hz.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0)).exists
    exact hzne hz0
  have hnF : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0 := by
    intro hzero
    apply hni
    filter_upwards [hzero] with z hz
    rw [hz]
    rfl
  obtain ⟨R₁, hR₁, hsub, hAF, hCF, hDF, hPF⟩ :=
    exists_analytic_curve_radial_ball_subset hF hF0 hnF (inter_mem hS hpower)
  obtain ⟨R₂, hR₂, hAi, hCi, hDi, hPi⟩ :=
    exists_analytic_curve_radial_ball hFi hFi0 hni
  let R := min R₁ R₂
  have hR : 0 < R := lt_min hR₁ hR₂
  have hcl₁ : closedBall (0 : ℂ) R ⊆ closedBall 0 R₁ :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hcl₂ : closedBall (0 : ℂ) R ⊆ closedBall 0 R₂ :=
    closedBall_subset_closedBall (min_le_right _ _)
  have hbl₁ : ball (0 : ℂ) R ⊆ ball 0 R₁ := ball_subset_ball (min_le_left _ _)
  have hbl₂ : ball (0 : ℂ) R ⊆ ball 0 R₂ := ball_subset_ball (min_le_right _ _)
  have hpow (z : ℂ) (hz : z ∈ closedBall 0 R) : F z i = z ^ a := (hsub (hcl₁ hz)).2
  have hcont (t : ℝ) :
      ContinuousOn (fun z => planeMixedRadiusSq i t (F z)) (closedBall 0 R) :=
    ((hCi.mono hcl₂).const_mul (1 - t)).add ((hCF.mono hcl₁).const_mul t)
  have hsmooth (t : ℝ) (z : ℂ) (hz : z ∈ ball 0 R) :
      ContDiffAt ℝ ∞ (fun w => planeMixedRadiusSq i t (F w)) z := by
    have hsF : ContDiffAt ℝ ∞ F z :=
      (hAF z (hcl₁ (ball_subset_closedBall hz))).restrictScalars.contDiffAt
    have hsi : ContDiffAt ℝ ∞ (fun w => F w i) z :=
      (hAi z (hcl₂ (ball_subset_closedBall hz))).restrictScalars.contDiffAt
    change ContDiffAt ℝ ∞ (fun w => (1 - t) * ‖F w i‖ ^ 2 + t * ‖F w‖ ^ 2) z
    exact (contDiffAt_const.mul (hsi.norm_sq (𝕜 := ℂ))).add
      (contDiffAt_const.mul (hsF.norm_sq (𝕜 := ℂ)))
  have hpos (t : ℝ) (ht : t ∈ Icc 0 1) (z : ℂ) (hz : z ∈ ball 0 R) (hz0 : z ≠ 0) :
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z := by
    have hd := ((hDi z (hbl₂ hz) hz0).hasFDerivAt.const_smul (1 - t)).add
      ((hDF z (hbl₁ hz) hz0).hasFDerivAt.const_smul t)
    change HasFDerivAt (fun w => planeMixedRadiusSq i t (F w)) _ z at hd
    rw [hd.fderiv]
    change 0 < (1 - t) * fderiv ℝ (fun w => ‖F w i‖ ^ 2) z z +
      t * fderiv ℝ (fun w => ‖F w‖ ^ 2) z z
    have hi := hPi z (hbl₂ hz) hz0
    have hf := hPF z (hbl₁ hz) hz0
    by_cases ht0 : t = 0
    · simpa only [ht0, sub_zero, one_mul, zero_mul, add_zero] using hi
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hi.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hf)
  refine ⟨R, hR, fun z hz => (hsub (hcl₁ hz)).1, hAF.mono hcl₁, hpow,
    fun t ht => ⟨hcont t, hsmooth t, hpos t ht⟩, ?_⟩
  intro t ht u hu c hc hcR
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖r • u‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu, mul_one]
  have hboundary : R ^ (2 * a) ≤ planeMixedRadiusSq i t (F (R • u)) := by
    have hRu : R • u ∈ closedBall (0 : ℂ) R := by
      simp only [mem_closedBall, dist_zero_right, hnorm R hR.le, le_refl]
    have hi : ‖F (R • u) i‖ ^ 2 = R ^ (2 * a) := by
      rw [hpow _ hRu, norm_pow, hnorm R hR.le, ← pow_mul, Nat.mul_comm a 2]
    have hle : ‖F (R • u) i‖ ^ 2 ≤ ‖F (R • u)‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (PiLp.norm_apply_le _ i)
    unfold planeMixedRadiusSq
    have := mul_nonneg ht.1 (sub_nonneg.mpr hle)
    nlinarith [hi]
  have hray (r : ℝ) (hr : r ∈ Ioo 0 R) : r • u ∈ ball (0 : ℂ) R ∧ r • u ≠ 0 := by
    refine ⟨?_, norm_pos_iff.mp (by rw [hnorm r hr.1.le]; exact hr.1)⟩
    simpa only [mem_ball, dist_zero_right, hnorm r hr.1.le] using hr.2
  apply existsUnique_ray_level_of_radial_derivative_pos hR
    ((hcont t).comp (continuous_id.smul continuous_const).continuousOn (by
      intro r hr
      change r • u ∈ closedBall (0 : ℂ) R
      simpa only [mem_closedBall, dist_zero_right, hnorm r hr.1] using hr.2))
    (fun r hr => (hsmooth t _ (hray r hr).1).differentiableAt (by simp))
    (fun r hr => hpos t ht _ (hray r hr).1 (hray r hr).2)
  · simpa only [hF0, planeMixedRadiusSq_zero] using hc
  · exact hcR.trans_le hboundary

end OnLeConjecture.Analytic
