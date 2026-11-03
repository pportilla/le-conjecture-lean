/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Ring.Fin
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Smooth descent of cyclically labelled braid heights

A smooth periodic real lift defines a smooth function on the native complex circle.
Cyclic relabelling of smooth strand heights supplies such a lift, with the exact
sheet formula. These statements concern functions, not a geometric word realization.
-/

@[expose] public noncomputable section

open Set Filter Manifold Fin.NatCast
open scoped Topology ContDiff Manifold

namespace OnLeConjecture.Analytic

attribute [local instance] finrank_real_complex_fact'

/-- Descent of a real function using the principal argument. Periodicity is used
in the evaluation and smoothness theorems, so the definition does not contain choices. -/
def circleHeightOfPeriodic (f : ℝ → ℂ) (u : Circle) : ℂ := f (Complex.arg (u : ℂ))

theorem circleHeightOfPeriodic_exp {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi)) (t : ℝ) :
    circleHeightOfPeriodic f (Circle.exp t) = f t := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Circle.exp_arg (Circle.exp t))
  unfold circleHeightOfPeriodic
  rw [hm]
  exact hp.int_mul m t

/-- The argument of the quotient by a fixed point is smooth at that point.
The complex logarithm proves this locally at the quotient value `1`. -/
theorem contMDiffAt_circle_relative_arg (u : Circle) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun v : Circle => Complex.arg ((v : ℂ) / (u : ℂ))) u := by
  have hq : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun v : Circle => (v : ℂ) / (u : ℂ)) := by
    exact (show ContDiff ℝ ∞ (fun z : ℂ => z / (u : ℂ)) from
      contDiff_id.div_const _).contMDiff.comp contMDiff_coe_sphere
  have hs : (u : ℂ) / (u : ℂ) ∈ Complex.slitPlane := by
    simp [Complex.mem_slitPlane_iff]
  have hl := (Complex.contDiffAt_log hs (n := ∞)).restrict_scalars ℝ
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  simpa only [Function.comp_def, Complex.log_im] using
    hi.contDiffAt.comp_contMDiffAt
      (hl.comp_contMDiffAt (f := fun v : Circle => (v : ℂ) / (u : ℂ)) hq.contMDiffAt)

/-- A smooth periodic real lift descends smoothly across the argument cut. -/
theorem circleHeightOfPeriodic_contMDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (circleHeightOfPeriodic f) := by
  intro u
  let α : Circle → ℝ := fun v => Complex.arg (u : ℂ) + Complex.arg ((v : ℂ) / (u : ℂ))
  have ha : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ α u :=
    contMDiffAt_const.add (contMDiffAt_circle_relative_arg u)
  have he (v : Circle) : Circle.exp (α v) = v := by
    change Circle.exp (Complex.arg (u : ℂ) + Complex.arg ((v : ℂ) / (u : ℂ))) = v
    rw [Circle.exp_add, Circle.exp_arg]
    have hv : Complex.arg ((v : ℂ) / (u : ℂ)) = Complex.arg ((v / u : Circle) : ℂ) := rfl
    rw [hv, Circle.exp_arg]
    simp [div_eq_mul_inv]
  have hcomp := hf.contDiffAt.comp_contMDiffAt ha
  apply hcomp.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun v => by
    change circleHeightOfPeriodic f v = f (α v)
    calc
      circleHeightOfPeriodic f v = circleHeightOfPeriodic f (Circle.exp (α v)) :=
        congrArg _ (he v).symm
      _ = f (α v) := circleHeightOfPeriodic_exp hp _

/-- A cyclically relabelled height family after an arbitrary number of base turns. -/
theorem cyclicBraidHeights_add_nat_period {a : ℕ} [NeZero a]
    {K : Fin a → ℝ → ℂ}
    (hcyc : ∀ k θ, K k (θ + 2 * Real.pi) = K (finRotate a k) θ)
    (m : ℕ) (k : Fin a) (θ : ℝ) :
    K k (θ + 2 * Real.pi * m) = K (k + (m : Fin a)) θ := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [show θ + 2 * Real.pi * (m + 1 : ℕ) =
      (θ + 2 * Real.pi * m) + 2 * Real.pi by push_cast; ring,
      hcyc, ih, finRotate_apply]
    congr 1
    push_cast
    abel

/-- Exact smooth descent for a globally cyclically relabelled family of heights.
The labels advance by `finRotate` during one positive base turn. -/
theorem exists_circle_height_of_cyclic_heights {a : ℕ} (ha : 0 < a)
    (K : Fin a → ℝ → ℂ) (hK : ∀ k, ContDiff ℝ ∞ (K k))
    (hcyc : ∀ k θ, K k (θ + 2 * Real.pi) = K (finRotate a k) θ) :
    ∃ w : Circle → ℂ, ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w ∧
      ∀ (k : Fin a) (θ : ℝ),
        w (Circle.exp ((θ + 2 * Real.pi * k.val) / a)) = K k θ := by
  let : NeZero a := ⟨ha.ne'⟩
  let f : ℝ → ℂ := fun t => K 0 (a * t)
  have hf : ContDiff ℝ ∞ f := (hK 0).comp (contDiff_const.mul contDiff_id)
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro t
    change K 0 (a * (t + 2 * Real.pi)) = K 0 (a * t)
    rw [show (a : ℝ) * (t + 2 * Real.pi) =
      (a : ℝ) * t + 2 * Real.pi * a by ring,
      cyclicBraidHeights_add_nat_period hcyc a]
    simp
  refine ⟨circleHeightOfPeriodic f, circleHeightOfPeriodic_contMDiff hf hp, ?_⟩
  intro k θ
  rw [circleHeightOfPeriodic_exp hp]
  change K 0 ((a : ℝ) * ((θ + 2 * Real.pi * k.val) / a)) = K k θ
  rw [mul_div_cancel₀ _ (by exact_mod_cast ha.ne'),
    cyclicBraidHeights_add_nat_period hcyc k.val]
  simp

/-- Extension of one base period with cyclic relabelling. The integer quotient
counts base turns, including negative turns. -/
def cyclicBraidHeightExtension {a : ℕ} (K : Fin a → ℝ → ℂ) (b : ℝ)
    (k : Fin a) (θ : ℝ) : ℂ :=
  K (((finRotate a) ^ toIcoDiv (by positivity : 0 < 2 * Real.pi) b θ) k)
    (toIcoMod (by positivity : 0 < 2 * Real.pi) b θ)

theorem cyclicBraidHeightExtension_cyclic {a : ℕ} (K : Fin a → ℝ → ℂ) (b : ℝ)
    (k : Fin a) (θ : ℝ) :
    cyclicBraidHeightExtension K b k (θ + 2 * Real.pi) =
      cyclicBraidHeightExtension K b (finRotate a k) θ := by
  unfold cyclicBraidHeightExtension
  rw [toIcoDiv_add_right, toIcoMod_add_right, zpow_add_one, Equiv.Perm.mul_apply]

theorem cyclicBraidHeightExtension_eq {a : ℕ} (K : Fin a → ℝ → ℂ) (b : ℝ)
    (hmatch : ∀ k, K k (b + 2 * Real.pi) = K (finRotate a k) b)
    (k : Fin a) {θ : ℝ} (hθ : θ ∈ Icc b (b + 2 * Real.pi)) :
    cyclicBraidHeightExtension K b k θ = K k θ := by
  have hp : 0 < 2 * Real.pi := by positivity
  by_cases he : θ = b + 2 * Real.pi
  · subst θ
    unfold cyclicBraidHeightExtension
    rw [toIcoMod_apply_right, toIcoDiv_add_right]
    have hb : toIcoDiv hp b b = 0 := by
      apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
      simp only [zero_zsmul, sub_zero, left_mem_Ico]
      linarith
    rw [hb, zero_add, zpow_one, ← hmatch]
  · have hmem : θ ∈ Ico b (b + 2 * Real.pi) := ⟨hθ.1, lt_of_le_of_ne hθ.2 he⟩
    unfold cyclicBraidHeightExtension
    rw [(toIcoMod_eq_self hp).mpr hmem]
    have hn : toIcoDiv hp b θ = 0 := by
      apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
      simpa only [zero_zsmul, sub_zero] using hmem
    rw [hn, zpow_zero, Equiv.Perm.one_apply]

/-- The cyclic extension is smooth when the paths are constant near both
endpoints and their endpoint values obey the sheet rotation. -/
theorem cyclicBraidHeightExtension_contDiff {a : ℕ} (K : Fin a → ℝ → ℂ) (b : ℝ)
    (hK : ∀ k, ContDiff ℝ ∞ (K k))
    (hleft : ∀ k, K k =ᶠ[𝓝 b] fun _ => K k b)
    (hright : ∀ k, K k =ᶠ[𝓝 (b + 2 * Real.pi)] fun _ => K k (b + 2 * Real.pi))
    (hmatch : ∀ k, K k (b + 2 * Real.pi) = K (finRotate a k) b) (k : Fin a) :
    ContDiff ℝ ∞ (cyclicBraidHeightExtension K b k) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  let hp : 0 < 2 * Real.pi := by positivity
  let n := toIcoDiv hp b θ
  by_cases hθ : θ ≡ b [PMOD (2 * Real.pi)]
  · have hθ' : b ≡ θ [PMOD (2 * Real.pi)] := hθ.symm
    have hmod : toIcoMod hp b θ = b := hθ'.toIcoMod_eq_left hp
    have hval : θ - n • (2 * Real.pi) = b := hmod
    let m := toIocDiv hp b θ
    have hnm : n = m + 1 := (AddCommGroup.modEq_iff_toIcoDiv_eq_toIocDiv_add_one hp).mp hθ'
    have hmval : θ - m • (2 * Real.pi) = b + 2 * Real.pi := by
      rw [hnm, add_zsmul, one_zsmul] at hval
      linarith
    have hrot : finRotate a (((finRotate a) ^ m) k) = ((finRotate a) ^ n) k := by
      rw [hnm, show m + 1 = 1 + m by omega, zpow_add, zpow_one]
      rfl
    have hR : ∀ᶠ t in 𝓝 θ,
        K (((finRotate a) ^ n) k) (t - n • (2 * Real.pi)) =
          K (((finRotate a) ^ n) k) b := by
      exact (hleft _).comp_tendsto (by
        simpa only [id_eq, hval] using (continuousAt_id.sub_const (n • (2 * Real.pi)) :
          ContinuousAt (fun t : ℝ => t - n • (2 * Real.pi)) θ))
    have hL : ∀ᶠ t in 𝓝 θ,
        K (((finRotate a) ^ m) k) (t - m • (2 * Real.pi)) =
          K (((finRotate a) ^ n) k) b := by
      have hc := (hright (((finRotate a) ^ m) k)).comp_tendsto (show
        Tendsto (fun t : ℝ => t - m • (2 * Real.pi)) (𝓝 θ) (𝓝 (b + 2 * Real.pi)) by
          simpa only [id_eq, hmval] using (continuousAt_id.sub_const (m • (2 * Real.pi)) :
            ContinuousAt (fun t : ℝ => t - m • (2 * Real.pi)) θ))
      simpa only [Filter.EventuallyEq, Function.comp_def, hmatch, hrot] using hc
    have he : cyclicBraidHeightExtension K b k =ᶠ[𝓝 θ]
        fun _ => K (((finRotate a) ^ n) k) b := by
      rw [← nhdsLT_sup_nhdsGE, Filter.EventuallyEq, Filter.eventually_sup]
      constructor
      · filter_upwards [eventuallyEq_toIcoDiv_nhdsLT hp b θ, hL.filter_mono nhdsWithin_le_nhds]
          with t ht hLt
        simpa only [cyclicBraidHeightExtension, toIcoMod, ht] using hLt
      · filter_upwards [eventuallyEq_toIcoDiv_nhdsGE hp b θ, hR.filter_mono nhdsWithin_le_nhds]
          with t ht hRt
        simpa only [cyclicBraidHeightExtension, toIcoMod, ht] using hRt
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have he : cyclicBraidHeightExtension K b k =ᶠ[𝓝 θ]
        fun t => K (((finRotate a) ^ n) k) (t - n • (2 * Real.pi)) := by
      filter_upwards [eventuallyEq_toIcoDiv_nhds hp b hθ] with t ht
      simp only [cyclicBraidHeightExtension, toIcoMod, ht]
      rfl
    exact ((hK _).comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq he

/-- Smooth gluing of one period of labelled heights to the source circle.
The endpoints of the period are included, and the upper endpoint uses exactly
the prescribed cyclic relabelling. -/
theorem exists_circle_height_of_period_collars {a : ℕ} (ha : 0 < a)
    (K : Fin a → ℝ → ℂ) (b : ℝ) (hK : ∀ k, ContDiff ℝ ∞ (K k))
    (hleft : ∀ k, K k =ᶠ[𝓝 b] fun _ => K k b)
    (hright : ∀ k, K k =ᶠ[𝓝 (b + 2 * Real.pi)] fun _ => K k (b + 2 * Real.pi))
    (hmatch : ∀ k, K k (b + 2 * Real.pi) = K (finRotate a k) b) :
    ∃ w : Circle → ℂ, ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w ∧
      ∀ (k : Fin a) (θ : ℝ), θ ∈ Icc b (b + 2 * Real.pi) →
        w (Circle.exp ((θ + 2 * Real.pi * k.val) / a)) = K k θ := by
  obtain ⟨w, hw, he⟩ := exists_circle_height_of_cyclic_heights ha
    (cyclicBraidHeightExtension K b)
    (cyclicBraidHeightExtension_contDiff K b hK hleft hright hmatch)
    (cyclicBraidHeightExtension_cyclic K b)
  refine ⟨w, hw, fun k θ hθ => ?_⟩
  rw [he, cyclicBraidHeightExtension_eq K b hmatch k hθ]

end OnLeConjecture.Analytic
