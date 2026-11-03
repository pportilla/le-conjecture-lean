/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightRadialExpansion

/-!
# The analytic third-coordinate difference in the cyclic chart

The strict weighted tail supplies a convergent rescaled third difference.
Its restriction to the parameter-zero hyperplane is exactly `s^N-S^N`.
No formal division by the scaling parameter is used.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

@[expose] noncomputable def cyclicFirstRadialChart (q : Source 3) : ℂ × (ℂ × ℂ) :=
  (q 2, (q 0, 1))

@[expose] noncomputable def cyclicSecondRadialChart (b : Source 3 → ℂ)
    (q : Source 3) : ℂ × (ℂ × ℂ) :=
  (q 2, (q 1, b q))

theorem cyclicFirstRadialChart_analyticAt : AnalyticAt ℂ cyclicFirstRadialChart 0 := by
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  exact (hq 2).prod ((hq 0).prod analyticAt_const)

theorem cyclicSecondRadialChart_analyticAt
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) :
    AnalyticAt ℂ (cyclicSecondRadialChart b) 0 := by
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  exact (hq 2).prod ((hq 1).prod hb)

@[expose] noncomputable def cyclicThirdRemainder
    (remainder : ℂ × (ℂ × ℂ) → Source 3) (b : Source 3 → ℂ) (q : Source 3) : ℂ :=
  remainder (cyclicFirstRadialChart q) 2 - remainder (cyclicSecondRadialChart b q) 2

theorem cyclicThirdRemainder_analyticAt
    (remainder : ℂ × (ℂ × ℂ) → Source 3)
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ)
    (hfirst : AnalyticAt ℂ remainder (0, (0, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (0, ζ))) :
    AnalyticAt ℂ (cyclicThirdRemainder remainder b) 0 := by
  have h1 : AnalyticAt ℂ (fun q : Source 3 => remainder (cyclicFirstRadialChart q)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 3)) _ cyclicFirstRadialChart_analyticAt
    simpa only [cyclicFirstRadialChart, Pi.zero_apply] using hfirst
  have h2 : AnalyticAt ℂ (fun q : Source 3 => remainder (cyclicSecondRadialChart b q)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 3)) _ (cyclicSecondRadialChart_analyticAt b hb)
    simpa only [cyclicSecondRadialChart, Pi.zero_apply, hb0] using hsecond
  exact (analyticAt_pi_iff.mp h1 2).sub (analyticAt_pi_iff.mp h2 2)

@[expose] noncomputable def cyclicThirdDifferenceFunction
    (N : ℕ) (remainder : ℂ × (ℂ × ℂ) → Source 3) (b : Source 3 → ℂ)
    (q : Source 3) : ℂ :=
  q 0 ^ N - q 1 ^ N + q 2 * cyclicThirdRemainder remainder b q

/-- The genuine analytic family, its scaling identity, and its special
parameter restriction, constructed from radial expansions. -/
theorem cyclicThirdDifference_analytic_and_scaling
    (k p N : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Source 3)
    (remainder : ℂ × (ℂ × ℂ) → Source 3)
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ)
    (hfirst : HasTwoWeightRadialExpansionAt k p degrees initialMap representative remainder (0, 1))
    (hsecond : HasTwoWeightRadialExpansionAt k p degrees initialMap representative remainder (0, ζ))
    (hinitial : ∀ z : ℂ × ℂ, initialMap z 2 = z.1 ^ N) :
    ∃ hD : AnalyticAt ℂ (cyclicThirdDifferenceFunction N remainder b) 0,
      (∀ᶠ q in 𝓝 (0 : Source 3),
        representative (twoWeightRadialSource k p (q 2) (q 0, 1)) 2 -
          representative (twoWeightRadialSource k p (q 2) (q 1, b q)) 2 =
            q 2 ^ degrees 2 * cyclicThirdDifferenceFunction N remainder b q) ∧
      Germ.coordinate (2 : Fin 3) ∣
        Germ.ofFunction (cyclicThirdDifferenceFunction N remainder b) hD -
          (Germ.coordinate (0 : Fin 3) ^ N - Germ.coordinate (1 : Fin 3) ^ N) := by
  have hT := cyclicThirdRemainder_analyticAt remainder b hb ζ hb0
    hfirst.remainder_analyticAt hsecond.remainder_analyticAt
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  have hD : AnalyticAt ℂ (cyclicThirdDifferenceFunction N remainder b) 0 :=
    (((hq 0).pow N).sub ((hq 1).pow N)).add ((hq 2).mul hT)
  refine ⟨hD, ?_, ?_⟩
  · have ht1 : Tendsto cyclicFirstRadialChart (𝓝 (0 : Source 3)) (𝓝 (0, (0, 1))) := by
      simpa only [ContinuousAt, cyclicFirstRadialChart, Pi.zero_apply] using
        cyclicFirstRadialChart_analyticAt.continuousAt
    have ht2 : Tendsto (cyclicSecondRadialChart b) (𝓝 (0 : Source 3)) (𝓝 (0, (0, ζ))) := by
      simpa only [ContinuousAt, cyclicSecondRadialChart, Pi.zero_apply, hb0] using
        (cyclicSecondRadialChart_analyticAt b hb).continuousAt
    filter_upwards [ht1.eventually hfirst.expansion, ht2.eventually hsecond.expansion] with q h1 h2
    change representative (twoWeightRadialSource k p (cyclicFirstRadialChart q).1
      (cyclicFirstRadialChart q).2) 2 -
      representative (twoWeightRadialSource k p (cyclicSecondRadialChart b q).1
        (cyclicSecondRadialChart b q).2) 2 = _
    rw [h1 2, h2 2, hinitial, hinitial]
    simp only [cyclicFirstRadialChart, cyclicSecondRadialChart,
      cyclicThirdDifferenceFunction, cyclicThirdRemainder]
    ring
  · refine ⟨Germ.ofFunction (cyclicThirdRemainder remainder b) hT, ?_⟩
    apply Subtype.ext
    change ((fun q : Source 3 => cyclicThirdDifferenceFunction N remainder b q -
      (q 0 ^ N - q 1 ^ N)) : FunctionGerm 3) =
      ((fun q : Source 3 => q 2 * cyclicThirdRemainder remainder b q) : FunctionGerm 3)
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun q => by
      simp [cyclicThirdDifferenceFunction]

end OnLeConjecture.Analytic
