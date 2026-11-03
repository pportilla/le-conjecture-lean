/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCrossingOrder
public import OnLeConjecture.Analytic.PlaneBranchPositiveBraidLinkData
public import OnLeConjecture.Analytic.PlaneBranchBraidMonodromy

/-!
# Braid events on the same disc as the geometric link

The branch-link construction retains one disc on which all sheet
differences rotate positively. The lemmas here use that disc directly,
without making another independent choice of a smaller radius.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology

namespace OnLeConjecture.Analytic

/-- Rotation on a specified parameter disc gives the actual positive
logarithmic derivative of every distinct labelled pair on every smaller
circle. This uses the same circle radius, without further shrinking. -/
theorem planeBranchBraidPairDifference_im_pos_of_sheetRotation
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hrot : ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 → ∀ z ∈ ball 0 R, z ≠ 0 →
      planeBranchSheetDifference F i ζ z ≠ 0 ∧
      0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
        planeBranchSheetDifference F i ζ z).re)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) (k l : Fin a) (hkl : k ≠ l) (θ : ℝ) :
    planeBranchBraidPairDifference F i a r k l θ ≠ 0 ∧
    DifferentiableAt ℝ (planeBranchBraidPairDifference F i a r k l) θ ∧
    0 < (deriv (planeBranchBraidPairDifference F i a r k l) θ /
      planeBranchBraidPairDifference F i a r k l θ).im := by
  let ζ := planeBranchBraidRoot a k / planeBranchBraidRoot a l
  have hζ : ζ ^ a = 1 := by
    rw [div_pow, planeBranchBraidRoot_pow ha, planeBranchBraidRoot_pow ha,
      div_self one_ne_zero]
  have hζ1 : ζ ≠ 1 := by
    intro h
    exact hkl (planeBranchBraidRoot_injective ha
      ((div_eq_one_iff_eq (planeBranchBraidRoot_ne_zero a l)).mp h))
  let η := θ + 2 * Real.pi * l.val
  let z := planeBranchAngularParameter a r η
  have hz : z ∈ ball 0 R := by
    simpa only [z, mem_ball, dist_zero_right, planeBranchAngularParameter_norm,
      abs_of_pos hr] using hrR
  have hz0 : z ≠ 0 := by
    apply norm_pos_iff.mp
    simpa only [z, planeBranchAngularParameter_norm, abs_of_pos hr] using hr
  have hd := (planeBranchSheetDifference_analyticAt_of_mem_ball hF i ha hζ hz).differentiableAt
  obtain ⟨hne, hpos⟩ := hrot ζ hζ hζ1 z hz hz0
  let D := planeBranchAngularDifference F i ζ a r
  have hD := hd.hasDerivAt.comp η (planeBranchAngularParameter_hasDerivAt a r η)
  have hDpos : 0 < (deriv D η / D η).im := by
    change 0 < (deriv (fun t : ℝ => planeBranchSheetDifference F i ζ
      (planeBranchAngularParameter a r t)) η /
      planeBranchSheetDifference F i ζ (planeBranchAngularParameter a r η)).im
    rw [im_logDeriv_comp_planeBranchAngularParameter a r η hd]
    exact div_pos hpos (by exact_mod_cast ha)
  have heq : planeBranchBraidPairDifference F i a r k l =
      fun t => D (t + 2 * Real.pi * l.val) :=
    funext (planeBranchBraidPairDifference_eq_angularDifference F i a r k l)
  have hDa : DifferentiableAt ℝ D η := hD.differentiableAt
  have hdt := hDa.hasDerivAt.scomp θ ((hasDerivAt_id θ).add_const (2 * Real.pi * l.val))
  have hder : deriv (fun t => D (t + 2 * Real.pi * l.val)) θ = deriv D η := by
    simpa only [η, Function.comp_def, id_eq, one_smul] using hdt.deriv
  rw [heq]
  exact ⟨hne, hdt.differentiableAt, by rwa [hder]⟩

/-- On the retained rotation disc, projected crossing times are finite
on every compact base-angle interval. All pairs, including simultaneous
crossings, retain their positive determinant and transverse derivative. -/
theorem planeBranchProjectedCrossingTimes_finite_of_sheetRotation
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hrot : ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 → ∀ z ∈ ball 0 R, z ≠ 0 →
      planeBranchSheetDifference F i ζ z ≠ 0 ∧
      0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
        planeBranchSheetDifference F i ζ z).re)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℂ} (hc : c ≠ 0) (u v : ℝ) :
    (planeBranchProjectedCrossingTimes F i a r c u v).Finite ∧
    ∀ k l : Fin a, k ≠ l → ∀ θ : ℝ,
      (c * planeBranchBraidPairDifference F i a r k l θ).re = 0 →
      0 < -deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ *
        (c * planeBranchBraidPairDifference F i a r k l θ).im ∧
      deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ ≠ 0 := by
  have hcross (k l : Fin a) (hkl : k ≠ l) (θ : ℝ)
      (hproj : (c * planeBranchBraidPairDifference F i a r k l θ).re = 0) :=
    let H := planeBranchBraidPairDifference_im_pos_of_sheetRotation ha hF hrot hr hrR k l hkl θ
    projected_crossing_determinant_pos H.2.1 H.1 H.2.2 hc hproj
  refine ⟨?_, hcross⟩
  have hpair (k l : Fin a) :
      {θ ∈ Icc u v | k ≠ l ∧
        (c * planeBranchBraidPairDifference F i a r k l θ).re = 0}.Finite := by
    by_cases hkl : k = l
    · simp [hkl]
    · have hcont : Continuous
          (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) := by
        apply continuous_iff_continuousAt.mpr
        intro θ
        have hd := (planeBranchBraidPairDifference_im_pos_of_sheetRotation
          ha hF hrot hr hrR k l hkl θ).2.1
        exact Complex.continuous_re.continuousAt.comp (hd.const_mul c).continuousAt
      have hfin := finite_regular_zeros_Icc hcont u v
        (fun θ _ hproj => (hcross k l hkl θ hproj).2)
      simpa [hkl] using hfin
  have hfin := Set.finite_iUnion fun k : Fin a =>
    Set.finite_iUnion fun l : Fin a => hpair k l
  apply hfin.subset
  rintro θ ⟨hθ, k, l, hkl, hproj⟩
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨l, hθ, hkl, hproj⟩⟩

/-- A regular period and its endpoint sorting permutations are available
for the same circle radius retained by the branch-link isotopy. No
generic choice of a projection direction or endpoint is assumed. -/
theorem exists_planeBranch_regular_sorted_period_of_sheetRotation
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hrot : ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 → ∀ z ∈ ball 0 R, z ≠ 0 →
      planeBranchSheetDifference F i ζ z ≠ 0 ∧
      0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
        planeBranchSheetDifference F i ζ z).re)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℂ} (hc : c ≠ 0) :
    ∃ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), ∃ E : Finset ℝ,
      (∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r c
        θ (θ + 2 * Real.pi)) ∧
      θ ∉ E ∧ θ + 2 * Real.pi ∉ E ∧
      ∃ σ₀ σ₁ : Equiv.Perm (Fin a),
        StrictMono (fun j => planeBranchBraidProjection F i a r c θ (σ₀ j)) ∧
        StrictMono (fun j =>
          planeBranchBraidProjection F i a r c (θ + 2 * Real.pi) (σ₁ j)) ∧
        σ₁.trans (finRotate a) = σ₀ := by
  have hfin := (planeBranchProjectedCrossingTimes_finite_of_sheetRotation
    ha hF hrot hr hrR hc 0 (4 * Real.pi)).1
  obtain ⟨θ, hθ, E, hE, hθE, hθ'E, h₀, h₁⟩ :=
    exists_planeBranch_regular_period_of_finite F i ha r c hfin
  obtain ⟨σ₀, hσ₀, _⟩ := exists_unique_sortingPerm
    (planeBranchBraidProjection F i a r c θ) h₀
  obtain ⟨σ₁, hσ₁, _⟩ := exists_unique_sortingPerm
    (planeBranchBraidProjection F i a r c (θ + 2 * Real.pi)) h₁
  exact ⟨θ, hθ, E, hE, hθE, hθ'E, σ₀, σ₁, hσ₀, hσ₁,
    planeBranchBraid_endpoint_sortingPerm F i ha r c θ h₀ hσ₀ hσ₁⟩

end OnLeConjecture.Analytic
