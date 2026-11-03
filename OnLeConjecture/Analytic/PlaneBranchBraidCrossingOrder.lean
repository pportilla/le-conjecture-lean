/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCrossingFinite
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Local strand orders at positive braid crossings

The positive crossing determinant determines the real strand order on
both sides of the crossing. At a simultaneous crossing, the argument is
applied to every coincident pair, with one common neighborhood. No
assumption that projected crossings occur at distinct times is needed.
-/

@[expose] public noncomputable section

open Filter Set Metric SignType
open scoped Topology

namespace OnLeConjecture.Analytic

/-- A simple increasing zero changes sign from negative to positive. -/
theorem eventually_lt_zero_iff_of_deriv_pos {f : ℝ → ℝ} {θ : ℝ}
    (hd : 0 < deriv f θ) (hzero : f θ = 0) :
    ∀ᶠ t in 𝓝 θ, f t < 0 ↔ t < θ := by
  filter_upwards [eventually_nhdsWithin_sign_eq_of_deriv_pos hd hzero] with t ht
  rw [← sign_eq_neg_one_iff, ht, sign_eq_neg_one_iff, sub_neg]

/-- A simple decreasing zero changes sign from positive to negative. -/
theorem eventually_lt_zero_iff_of_deriv_neg {f : ℝ → ℝ} {θ : ℝ}
    (hd : deriv f θ < 0) (hzero : f θ = 0) :
    ∀ᶠ t in 𝓝 θ, f t < 0 ↔ θ < t := by
  filter_upwards [eventually_nhdsWithin_sign_eq_of_deriv_neg hd hzero] with t ht
  rw [← sign_eq_neg_one_iff, ht, sign_eq_neg_one_iff, sub_neg]

/-- The positive determinant fixes both local real orders, including when
other strand pairs cross at the same time. The height is evaluated at
the crossing itself. -/
theorem eventually_real_order_of_positive_crossing {f : ℝ → ℂ} {θ : ℝ}
    (hzero : (f θ).re = 0)
    (hdet : 0 < -deriv (fun t => (f t).re) θ * (f θ).im) :
    ∀ᶠ t in 𝓝 θ,
      ((f t).re < 0 ↔
        (t < θ ∧ (f θ).im < 0) ∨ (θ < t ∧ 0 < (f θ).im)) := by
  rcases mul_pos_iff.mp hdet with h | h
  · have hd : deriv (fun t => (f t).re) θ < 0 := by linarith [h.1]
    filter_upwards [eventually_lt_zero_iff_of_deriv_neg hd hzero] with t ht
    simpa only [not_lt_of_ge h.2.le, h.2, and_false, and_true, false_or] using ht
  · have hd : 0 < deriv (fun t => (f t).re) θ := by linarith [h.1]
    filter_upwards [eventually_lt_zero_iff_of_deriv_pos hd hzero] with t ht
    simpa only [h.2, not_lt_of_ge h.2.le, and_false, and_true, or_false] using ht

/-- A continuous nonzero real difference keeps its strict order locally. -/
theorem eventually_lt_zero_iff_of_continuousAt_ne_zero {f : ℝ → ℝ} {θ : ℝ}
    (hf : ContinuousAt f θ) (hne : f θ ≠ 0) :
    ∀ᶠ t in 𝓝 θ, f t < 0 ↔ f θ < 0 := by
  rcases hne.lt_or_gt with h | h
  · filter_upwards [hf.tendsto.eventually (eventually_lt_nhds h)] with t ht
    exact iff_of_true ht h
  · filter_upwards [hf.tendsto.eventually (eventually_gt_nhds h)] with t ht
    exact iff_of_false (not_lt_of_ge ht.le) (not_lt_of_ge h.le)

/-- On a finite collection of complex strands, every positive coincident
pair reverses its order according to its distinct imaginary heights.
Every noncoincident pair keeps its projected order. All conclusions hold
on one common neighborhood of the event time. -/
theorem eventually_strand_orders_of_positive_crossings
    {ι : Type*} [Finite ι] {K : ι → ℝ → ℂ} {θ : ℝ}
    (hcont : ∀ k, ContinuousAt (K k) θ)
    (hpos : ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im) :
    ∀ᶠ t in 𝓝 θ, ∀ k l, k ≠ l →
      ((K k θ).re ≠ (K l θ).re →
        ((K k t).re < (K l t).re ↔ (K k θ).re < (K l θ).re)) ∧
      ((K k θ).re = (K l θ).re →
        ((K k t).re < (K l t).re ↔
          (t < θ ∧ (K k θ).im < (K l θ).im) ∨
            (θ < t ∧ (K l θ).im < (K k θ).im))) := by
  apply Filter.eventually_all.mpr
  intro k
  apply Filter.eventually_all.mpr
  intro l
  by_cases hkl : k = l
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hkl))
  by_cases heq : (K k θ).re = (K l θ).re
  · have hz : (K k θ - K l θ).re = 0 := by simp only [Complex.sub_re, heq, sub_self]
    filter_upwards [eventually_real_order_of_positive_crossing hz (hpos k l hkl heq)]
      with t ht
    refine fun _ => ⟨fun h => False.elim (h heq), fun _ => ?_⟩
    simpa only [Complex.sub_re, Complex.sub_im, sub_neg, sub_pos] using ht
  · have hc : ContinuousAt (fun t => (K k t - K l t).re) θ :=
      Complex.continuous_re.continuousAt.comp ((hcont k).sub (hcont l))
    have hn : (K k θ - K l θ).re ≠ 0 := by
      simpa only [Complex.sub_re, sub_ne_zero] using heq
    filter_upwards [eventually_lt_zero_iff_of_continuousAt_ne_zero hc hn] with t ht
    refine fun _ => ⟨fun _ => ?_, fun h => False.elim (heq h)⟩
    simpa only [Complex.sub_re, sub_neg] using ht

/-- For the actual analytic branch there is one source radius such that
every projected event has a neighborhood with the preceding pairwise
order descriptions. Every coincident cluster is ordered by its imaginary
heights before the event and in the reverse order afterwards. -/
theorem exists_radius_planeBranchBraid_local_orders
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ c : ℂ, c ≠ 0 → ∀ θ : ℝ,
        let K : Fin a → ℝ → ℂ := fun k t => c * planeBranchBraidSheet F i a r k t
        (∀ k l, k ≠ l → (K k θ).re = (K l θ).re → (K k θ).im ≠ (K l θ).im) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ ball θ ε, ∀ k l, k ≠ l →
          ((K k θ).re ≠ (K l θ).re →
            ((K k t).re < (K l t).re ↔ (K k θ).re < (K l θ).re)) ∧
          ((K k θ).re = (K l θ).re →
            ((K k t).re < (K l t).re ↔
              (t < θ ∧ (K k θ).im < (K l θ).im) ∨
                (θ < t ∧ (K l θ).im < (K k θ).im))) := by
  obtain ⟨ρ, hρ, hρR, hrot⟩ :=
    exists_radius_planeBranchBraidPairDifference_im_pos ha hR hF hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ c hc θ
  let K : Fin a → ℝ → ℂ := fun k t => c * planeBranchBraidSheet F i a r k t
  have hcont (k : Fin a) : ContinuousAt (K k) θ := by
    have hparam : Continuous (planeBranchBraidParameter a r k) := by
      unfold planeBranchBraidParameter planeBranchAngularParameter
      fun_prop
    have hmem : planeBranchBraidParameter a r k θ ∈ ball 0 R := by
      simpa only [mem_ball, dist_zero_right, planeBranchBraidParameter_norm,
        abs_of_pos hr] using hrρ.trans_le hρR
    exact continuousAt_const.mul ((continuous_apply i.rev).continuousAt.comp
      ((hF _ hmem).continuousAt.comp hparam.continuousAt))
  have hpos (k l : Fin a) (hkl : k ≠ l) (heq : (K k θ).re = (K l θ).re) :
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im := by
    obtain ⟨hne, hd, hpos⟩ := hrot r hr hrρ k l hkl θ
    have hz : (c * planeBranchBraidPairDifference F i a r k l θ).re = 0 := by
      simpa only [K, planeBranchBraidPairDifference, mul_sub, Complex.sub_re,
        sub_eq_zero] using heq
    simpa only [K, planeBranchBraidPairDifference, mul_sub] using
      (projected_crossing_determinant_pos hd hne hpos hc hz).1
  refine ⟨?_, Metric.eventually_nhds_iff.mp
    (eventually_strand_orders_of_positive_crossings hcont hpos)⟩
  intro k l hkl heq him
  change (K k θ).im = (K l θ).im at him
  have h := hpos k l hkl heq
  simp only [Complex.sub_im, him, sub_self, mul_zero, lt_self_iff_false] at h

end OnLeConjecture.Analytic
