/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Hadamard
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The domain property for complex analytic germs

This file proves that the ring of complex analytic function germs at the
origin is an integral domain.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Set
open scoped Topology

namespace Germ

/-- A product of two complex analytic germs is zero only if one of the germs
is zero. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero {n : ℕ} {f g : Germ n}
    (hfg : f * g = 0) : f = 0 ∨ g = 0 := by
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  change IsAnalyticGerm f at hf
  change IsAnalyticGerm g at hg
  induction f using Filter.Germ.inductionOn with
  | _ f =>
    induction g using Filter.Germ.inductionOn with
    | _ g =>
      have hfAnalytic : AnalyticAt ℂ f 0 :=
        (isAnalyticGerm_ofFun f).mp hf
      have hgAnalytic : AnalyticAt ℂ g 0 :=
        (isAnalyticGerm_ofFun g).mp hg
      have hfgGerm := congrArg Subtype.val hfg
      change (f : FunctionGerm n) * (g : FunctionGerm n) = 0 at hfgGerm
      have hproduct : ∀ᶠ z in 𝓝 (0 : Source n), f z * g z = 0 := by
        apply Filter.Germ.coe_eq.mp
        calc
          ((fun z : Source n ↦ f z * g z) : FunctionGerm n) =
              (f : FunctionGerm n) * (g : FunctionGerm n) :=
            Filter.Germ.coe_mul f g
          _ = 0 := hfgGerm
      by_cases hfzero : ∀ᶠ z in 𝓝 (0 : Source n), f z = 0
      · left
        apply Subtype.ext
        exact Filter.Germ.coe_eq.mpr hfzero
      · right
        rcases hfAnalytic.exists_ball_analyticOnNhd with ⟨rf, hrf, hfan⟩
        rcases hgAnalytic.exists_ball_analyticOnNhd with ⟨rg, hrg, hgan⟩
        rcases Metric.eventually_nhds_iff.mp hproduct with
          ⟨rp, hrp, hproductBall⟩
        let r := min (min rf rg) rp
        have hr : 0 < r := by
          exact lt_min (lt_min hrf hrg) hrp
        have hr_rf : r ≤ rf := by
          dsimp [r]
          exact (min_le_left (min rf rg) rp).trans (min_le_left rf rg)
        have hr_rg : r ≤ rg := by
          dsimp [r]
          exact (min_le_left (min rf rg) rp).trans (min_le_right rf rg)
        have hr_rp : r ≤ rp := by
          dsimp [r]
          exact min_le_right (min rf rg) rp
        have hfan' : AnalyticOnNhd ℂ f (Metric.ball 0 r) :=
          hfan.mono (Metric.ball_subset_ball hr_rf)
        have hgan' : AnalyticOnNhd ℂ g (Metric.ball 0 r) :=
          hgan.mono (Metric.ball_subset_ball hr_rg)
        have hproduct' {z : Source n} (hz : z ∈ Metric.ball 0 r) :
            f z * g z = 0 :=
          hproductBall ((Metric.ball_subset_ball hr_rp) hz)
        obtain ⟨z, hz, hfz⟩ :
            ∃ z ∈ Metric.ball (0 : Source n) r, f z ≠ 0 := by
          by_contra h
          apply hfzero
          apply Filter.Eventually.mono
            (show ∀ᶠ z : Source n in 𝓝 0, z ∈ Metric.ball 0 r from
              Metric.ball_mem_nhds 0 hr)
          intro z hz
          by_contra hfz
          exact h ⟨z, hz, hfz⟩
        have hgzeroAtZ : g =ᶠ[𝓝 z] 0 := by
          filter_upwards [
            (hfan' z hz).continuousAt.eventually_ne hfz,
            Metric.isOpen_ball.mem_nhds hz] with w hfw hw
          exact (mul_eq_zero.mp (hproduct' hw)).resolve_left hfw
        have hgzeroOnBall : EqOn g 0 (Metric.ball (0 : Source n) r) :=
          hgan'.eqOn_zero_of_preconnected_of_eventuallyEq_zero
            (convex_ball 0 r).isPreconnected hz hgzeroAtZ
        apply Subtype.ext
        apply Filter.Germ.coe_eq.mpr
        apply Filter.Eventually.mono
          (show ∀ᶠ w : Source n in 𝓝 0, w ∈ Metric.ball 0 r from
            Metric.ball_mem_nhds 0 hr)
        exact fun w hw ↦ hgzeroOnBall hw

/-- The ring of complex analytic function germs at the origin has no zero
divisors. -/
noncomputable instance instNoZeroDivisors (n : ℕ) :
    NoZeroDivisors (Germ n) where
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero

/-- The ring of complex analytic function germs at the origin is an integral
domain. -/
noncomputable instance instIsDomain (n : ℕ) : IsDomain (Germ n) :=
  NoZeroDivisors.to_isDomain (Germ n)

end Germ

end OnLeConjecture.Analytic
