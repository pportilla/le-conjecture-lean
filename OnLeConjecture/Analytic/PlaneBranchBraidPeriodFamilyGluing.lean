/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidPeriodGluing

/-! # Smooth periodic gluing with a deformation parameter

Uniform constant collars allow the explicit cyclic extension to remain jointly
smooth in the deformation and angle parameters. The resulting native circle
function retains the exact labelled sheet formula. This is a gluing statement,
not a knot or grid identification.
-/

@[expose] public noncomputable section

open Set Filter Manifold Fin.NatCast
open scoped Topology ContDiff Manifold

namespace OnLeConjecture.Analytic

attribute [local instance] finrank_real_complex_fact'

/-- The explicit periodic descent, with the deformation parameter retained. -/
def circleHeightFamilyOfPeriodic (f : ℝ × ℝ → ℂ) (p : Circle × ℝ) : ℂ :=
  circleHeightOfPeriodic (fun θ => f (p.2, θ)) p.1

/-- Exact evaluation of the descended family on any real angle. -/
theorem circleHeightFamilyOfPeriodic_exp {f : ℝ × ℝ → ℂ}
    (hp : ∀ s, Function.Periodic (fun θ => f (s, θ)) (2 * Real.pi)) (s θ : ℝ) :
    circleHeightFamilyOfPeriodic f (Circle.exp θ, s) = f (s, θ) :=
  circleHeightOfPeriodic_exp (hp s) θ

/-- Joint smoothness survives the argument cut by the same relative-argument chart
used for the unparameterized descent. -/
theorem circleHeightFamilyOfPeriodic_contMDiff {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hp : ∀ s, Function.Periodic (fun θ => f (s, θ)) (2 * Real.pi)) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ (circleHeightFamilyOfPeriodic f) := by
  intro p
  let α : Circle × ℝ → ℝ := fun q =>
    Complex.arg (p.1 : ℂ) + Complex.arg ((q.1 : ℂ) / (p.1 : ℂ))
  have ha : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ α p :=
    contMDiffAt_const.add
      ((contMDiffAt_circle_relative_arg p.1).comp p contMDiffAt_fst)
  have he (q : Circle × ℝ) : Circle.exp (α q) = q.1 := by
    change Circle.exp (Complex.arg (p.1 : ℂ) + Complex.arg ((q.1 : ℂ) / (p.1 : ℂ))) = q.1
    rw [Circle.exp_add, Circle.exp_arg]
    have hq : Complex.arg ((q.1 : ℂ) / (p.1 : ℂ)) =
        Complex.arg ((q.1 / p.1 : Circle) : ℂ) := rfl
    rw [hq, Circle.exp_arg]
    simp [div_eq_mul_inv]
  have hcomp := hf.contDiffAt.comp_contMDiffAt (contMDiffAt_snd.prodMk_space ha)
  apply hcomp.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun q => by
    change circleHeightFamilyOfPeriodic f q = f (q.2, α q)
    calc
      circleHeightFamilyOfPeriodic f q =
          circleHeightFamilyOfPeriodic f (Circle.exp (α q), q.2) := by rw [he]
      _ = f (q.2, α q) := circleHeightFamilyOfPeriodic_exp hp _ _

/-- The same explicit cyclic extension, applied separately at each deformation time. -/
def cyclicBraidHeightFamilyExtension {a : ℕ} (K : Fin a → ℝ × ℝ → ℂ) (b : ℝ)
    (k : Fin a) (p : ℝ × ℝ) : ℂ :=
  cyclicBraidHeightExtension (fun j θ => K j (p.1, θ)) b k p.2

/-- Uniform collars determine the endpoint values at every deformation time. -/
theorem braidHeightFamily_endpoint_values {a : ℕ} (K : Fin a → ℝ × ℝ → ℂ)
    (b : ℝ) (C₀ C₁ : Fin a → ℂ)
    (hleft : ∀ k, ∀ᶠ θ in 𝓝 b, ∀ s, K k (s, θ) = C₀ k)
    (hright : ∀ k, ∀ᶠ θ in 𝓝 (b + 2 * Real.pi), ∀ s, K k (s, θ) = C₁ k)
    (hmatch : ∀ k, C₁ k = C₀ (finRotate a k)) (s : ℝ) (k : Fin a) :
    K k (s, b + 2 * Real.pi) = K (finRotate a k) (s, b) := by
  rw [(hright k).self_of_nhds s, (hleft (finRotate a k)).self_of_nhds s, hmatch]

/-- Joint smoothness of the cyclic extension follows from the uniform collars,
including at every period seam. -/
theorem cyclicBraidHeightFamilyExtension_contDiff {a : ℕ}
    (K : Fin a → ℝ × ℝ → ℂ) (b : ℝ) (C₀ C₁ : Fin a → ℂ)
    (hK : ∀ k, ContDiff ℝ ∞ (K k))
    (hleft : ∀ k, ∀ᶠ θ in 𝓝 b, ∀ s, K k (s, θ) = C₀ k)
    (hright : ∀ k, ∀ᶠ θ in 𝓝 (b + 2 * Real.pi), ∀ s, K k (s, θ) = C₁ k)
    (hmatch : ∀ k, C₁ k = C₀ (finRotate a k)) (k : Fin a) :
    ContDiff ℝ ∞ (cyclicBraidHeightFamilyExtension K b k) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let hp : 0 < 2 * Real.pi := by positivity
  let n := toIcoDiv hp b p.2
  by_cases hθ : p.2 ≡ b [PMOD (2 * Real.pi)]
  · have hθ' : b ≡ p.2 [PMOD (2 * Real.pi)] := hθ.symm
    have hmod : toIcoMod hp b p.2 = b := hθ'.toIcoMod_eq_left hp
    have hval : p.2 - n • (2 * Real.pi) = b := hmod
    let m := toIocDiv hp b p.2
    have hnm : n = m + 1 := (AddCommGroup.modEq_iff_toIcoDiv_eq_toIocDiv_add_one hp).mp hθ'
    have hmval : p.2 - m • (2 * Real.pi) = b + 2 * Real.pi := by
      rw [hnm, add_zsmul, one_zsmul] at hval
      linarith
    have hrot : finRotate a (((finRotate a) ^ m) k) = ((finRotate a) ^ n) k := by
      rw [hnm, show m + 1 = 1 + m by omega, zpow_add, zpow_one]
      rfl
    have hR : ∀ᶠ θ in 𝓝 p.2, ∀ s,
        K (((finRotate a) ^ n) k) (s, θ - n • (2 * Real.pi)) = C₀ (((finRotate a) ^ n) k) := by
      apply Filter.Tendsto.eventually _ (hleft _)
      show Tendsto (fun θ : ℝ => θ - n • (2 * Real.pi)) (𝓝 p.2) (𝓝 b)
      exact (by
        simpa only [id_eq, hval] using
          (continuousAt_id.sub_const (n • (2 * Real.pi)) :
            ContinuousAt (fun θ : ℝ => θ - n • (2 * Real.pi)) p.2))
    have hL : ∀ᶠ θ in 𝓝 p.2, ∀ s,
        K (((finRotate a) ^ m) k) (s, θ - m • (2 * Real.pi)) = C₀ (((finRotate a) ^ n) k) := by
      have hc := Filter.Tendsto.eventually (show
        Tendsto (fun θ : ℝ => θ - m • (2 * Real.pi)) (𝓝 p.2) (𝓝 (b + 2 * Real.pi)) by
          simpa only [id_eq, hmval] using
            (continuousAt_id.sub_const (m • (2 * Real.pi)) :
              ContinuousAt (fun θ : ℝ => θ - m • (2 * Real.pi)) p.2))
        (hright (((finRotate a) ^ m) k))
      simpa only [hmatch, hrot] using hc
    have he : ∀ᶠ θ in 𝓝 p.2, ∀ s,
        cyclicBraidHeightExtension (fun j η => K j (s, η)) b k θ = C₀ (((finRotate a) ^ n) k) := by
      rw [← nhdsLT_sup_nhdsGE, Filter.eventually_sup]
      constructor
      · filter_upwards [eventuallyEq_toIcoDiv_nhdsLT hp b p.2,
          hL.filter_mono nhdsWithin_le_nhds] with θ hθ hLθ
        intro s
        simpa only [cyclicBraidHeightExtension, toIcoMod, hθ] using hLθ s
      · filter_upwards [eventuallyEq_toIcoDiv_nhdsGE hp b p.2,
          hR.filter_mono nhdsWithin_le_nhds] with θ hθ hRθ
        intro s
        simpa only [cyclicBraidHeightExtension, toIcoMod, hθ] using hRθ s
    apply (contDiffAt_const (c := C₀ (((finRotate a) ^ n) k))).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.tendsto.eventually he] with q hq
    exact hq q.1
  · have he : cyclicBraidHeightFamilyExtension K b k =ᶠ[𝓝 p]
        fun q => K (((finRotate a) ^ n) k) (q.1, q.2 - n • (2 * Real.pi)) := by
      filter_upwards [(eventuallyEq_toIcoDiv_nhds hp b hθ).comp_tendsto
        continuousAt_snd.tendsto] with q hq
      change toIcoDiv hp b q.2 = n at hq
      simp only [cyclicBraidHeightFamilyExtension, cyclicBraidHeightExtension, toIcoMod, hq]
    exact ((hK _).comp
      (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))).contDiffAt.congr_of_eventuallyEq he

/-- Jointly smooth descent of one period of labelled heights with uniform collars.
The formula includes both endpoints and uses exactly the specified cyclic labels. -/
theorem exists_circle_height_family_of_period_collars {a : ℕ} (ha : 0 < a)
    (K : Fin a → ℝ × ℝ → ℂ) (b : ℝ) (C₀ C₁ : Fin a → ℂ)
    (hK : ∀ k, ContDiff ℝ ∞ (K k))
    (hleft : ∀ k, ∀ᶠ θ in 𝓝 b, ∀ s, K k (s, θ) = C₀ k)
    (hright : ∀ k, ∀ᶠ θ in 𝓝 (b + 2 * Real.pi), ∀ s, K k (s, θ) = C₁ k)
    (hmatch : ∀ k, C₁ k = C₀ (finRotate a k)) :
    ∃ W : Circle × ℝ → ℂ, ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ W ∧
      ∀ (k : Fin a) (θ s : ℝ), θ ∈ Icc b (b + 2 * Real.pi) →
        W (Circle.exp ((θ + 2 * Real.pi * k.val) / a), s) = K k (s, θ) := by
  let : NeZero a := ⟨ha.ne'⟩
  let f : ℝ × ℝ → ℂ := fun p => cyclicBraidHeightFamilyExtension K b 0 (p.1, a * p.2)
  have hf : ContDiff ℝ ∞ f :=
    (cyclicBraidHeightFamilyExtension_contDiff K b C₀ C₁ hK hleft hright hmatch 0).comp
      (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))
  have hp : ∀ s, Function.Periodic (fun θ => f (s, θ)) (2 * Real.pi) := by
    intro s θ
    change cyclicBraidHeightExtension (fun j η => K j (s, η)) b 0 (a * (θ + 2 * Real.pi)) =
      cyclicBraidHeightExtension (fun j η => K j (s, η)) b 0 (a * θ)
    rw [show (a : ℝ) * (θ + 2 * Real.pi) =
      (a : ℝ) * θ + 2 * Real.pi * a by ring,
      cyclicBraidHeights_add_nat_period
        (cyclicBraidHeightExtension_cyclic (fun j η => K j (s, η)) b) a]
    simp
  refine ⟨circleHeightFamilyOfPeriodic f, circleHeightFamilyOfPeriodic_contMDiff hf hp, ?_⟩
  intro k θ s hθ
  rw [circleHeightFamilyOfPeriodic_exp hp]
  change cyclicBraidHeightExtension (fun j η => K j (s, η)) b 0
    (a * ((θ + 2 * Real.pi * k.val) / a)) = K k (s, θ)
  rw [mul_div_cancel₀ _ (by exact_mod_cast ha.ne'),
    cyclicBraidHeights_add_nat_period
      (cyclicBraidHeightExtension_cyclic (fun j η => K j (s, η)) b) k.val]
  simp only [Fin.zero_add]
  have hk : (k.val : Fin a) = k := by apply Fin.ext; simp
  rw [hk]
  exact cyclicBraidHeightExtension_eq (fun j η => K j (s, η)) b
    (braidHeightFamily_endpoint_values K b C₀ C₁ hleft hright hmatch s) k hθ

end OnLeConjecture.Analytic
