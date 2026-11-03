/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Injectivity
import Mathlib.Tactic.FinCases

/-!
# Separation of the scaled sources in the cyclic chart

Two chart points whose limiting second coordinates are `1` and `zeta ≠ 1`
give distinct scaled source points whenever the scaling parameter is
nonzero. Local injectivity therefore excludes equal images uniformly near
the chart origin.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

@[expose] noncomputable def cyclicScaledFirstSource (k p : ℕ) (q : Source 3) : Source 2 :=
  ![q 2 ^ k * q 0, q 2 ^ p]

@[expose] noncomputable def cyclicScaledSecondSource
    (k p : ℕ) (b : Source 3 → ℂ) (q : Source 3) : Source 2 :=
  ![q 2 ^ k * q 1, q 2 ^ p * b q]

theorem cyclicScaledFirstSource_analyticAt (k p : ℕ) :
    AnalyticAt ℂ (cyclicScaledFirstSource k p) 0 := by
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact ((hq 2).pow k).mul (hq 0)
  · exact (hq 2).pow p

theorem cyclicScaledSecondSource_analyticAt
    (k p : ℕ) (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) :
    AnalyticAt ℂ (cyclicScaledSecondSource k p b) 0 := by
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact ((hq 2).pow k).mul (hq 1)
  · exact ((hq 2).pow p).mul hb

/-- Local injectivity forbids collisions away from the scaling-parameter
axis, uniformly in the two source chart coordinates. -/
theorem eventually_cyclic_scaled_equal_images_implies_parameter_zero
    {m : ℕ} (G : Source 2 → Source m)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) (hb0 : b 0 ≠ 1) :
    ∀ᶠ q in 𝓝 (0 : Source 3),
      G (cyclicScaledFirstSource k p q) = G (cyclicScaledSecondSource k p b q) →
        q 2 = 0 := by
  obtain ⟨s, hs, hG⟩ := hinjective
  have hvec : (![0, 0] : Source 2) = 0 := by
    ext i
    fin_cases i <;> rfl
  have hfirst : Tendsto (cyclicScaledFirstSource k p)
      (𝓝 (0 : Source 3)) (𝓝 (0 : Source 2)) := by
    simpa only [ContinuousAt, cyclicScaledFirstSource, Pi.zero_apply,
      zero_pow hk.ne', zero_pow hp.ne', zero_mul, hvec] using
      (cyclicScaledFirstSource_analyticAt k p).continuousAt
  have hsecond : Tendsto (cyclicScaledSecondSource k p b)
      (𝓝 (0 : Source 3)) (𝓝 (0 : Source 2)) := by
    simpa only [ContinuousAt, cyclicScaledSecondSource, Pi.zero_apply,
      zero_pow hk.ne', zero_pow hp.ne', zero_mul, hvec] using
      (cyclicScaledSecondSource_analyticAt k p b hb).continuousAt
  have hne : ∀ᶠ q in 𝓝 (0 : Source 3), b q ≠ 1 := hb.continuousAt.eventually_ne hb0
  filter_upwards [hfirst.eventually hs, hsecond.eventually hs, hne] with q hq1 hq2 hqb hsame
  by_contra hparameter
  have hsource := hG hq1 hq2 hsame
  have heq := congrFun hsource (1 : Fin 2)
  change q 2 ^ p = q 2 ^ p * b q at heq
  have hbq : b q = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero p hparameter)
    simpa only [mul_one] using heq.symm
  exact hqb hbq

/-- On an analytic cover where the first two rescaled differences vanish
and the parameter is the product of the cover coordinates, the third
difference has no zeros off the coordinate axes. -/
theorem eventually_cyclic_rescaled_third_zero_implies_axes
    (G : Source 2 → Source 3)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) (hb0 : b 0 ≠ 1)
    (degrees : Fin 3 → ℕ) (R : Source 3 → Source 3)
    (hscale : ∀ᶠ q in 𝓝 (0 : Source 3), ∀ i,
      G (cyclicScaledFirstSource k p q) i - G (cyclicScaledSecondSource k p b q) i =
        q 2 ^ degrees i * R q i)
    (Φ : Source 2 → Source 3) (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0 = 0)
    (hparameter : ∀ᶠ z in 𝓝 (0 : Source 2), Φ z 2 = z 0 * z 1)
    (hplane : ∀ᶠ z in 𝓝 (0 : Source 2), R (Φ z) 0 = 0 ∧ R (Φ z) 1 = 0) :
    ∀ᶠ z in 𝓝 (0 : Source 2), R (Φ z) 2 = 0 → z 0 = 0 ∨ z 1 = 0 := by
  have ht : Tendsto Φ (𝓝 (0 : Source 2)) (𝓝 (0 : Source 3)) := by
    simpa only [ContinuousAt, hΦ0] using hΦ.continuousAt
  have hseparation := eventually_cyclic_scaled_equal_images_implies_parameter_zero
    G hinjective k p hk hp b hb hb0
  filter_upwards [ht.eventually hseparation, ht.eventually hscale,
    hparameter, hplane] with z hsep hsc hparam hpl hthird
  have hR : R (Φ z) = 0 := by
    ext i
    fin_cases i
    · exact hpl.1
    · exact hpl.2
    · exact hthird
  have hG : G (cyclicScaledFirstSource k p (Φ z)) =
      G (cyclicScaledSecondSource k p b (Φ z)) := by
    ext i
    apply sub_eq_zero.mp
    rw [hsc i, hR]
    simp
  have hz := hsep hG
  rw [hparam] at hz
  exact mul_eq_zero.mp hz

end OnLeConjecture.Analytic
