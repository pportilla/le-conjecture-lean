/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedArcInitialComparison

/-!
# Target subtraction preserves differences on weighted fiber arcs

A function of the first two target coordinates has identical values at
the two points of a plane fiber. This identity applies to analytic
representatives along the weighted arcs used in the limiting comparison.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

theorem weightedSourceArc_tendsto_zero
    (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (A B : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) :
    Tendsto (weightedSourceArc a b p A B) (𝓝 (0 : Source 1)) (𝓝 (0 : Source 2)) := by
  have ht : Tendsto (fun q : Source 1 => q 0) (𝓝 0) (𝓝 (0 : ℂ)) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).continuous.tendsto 0
  have hpow : Tendsto (fun q : Source 1 => q 0 ^ p) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa only [zero_pow hp.ne'] using ht.pow p
  have hchart : Tendsto (fun q : Source 1 => (q 0 ^ p, (A (q 0), B (q 0))))
      (𝓝 0) (𝓝 (0, (A 0, B 0))) := by
    simpa only [nhds_prod_eq, Function.comp_def] using
      hpow.prodMk ((hA.continuousAt.tendsto.comp ht).prodMk (hB.continuousAt.tendsto.comp ht))
  have hsource := (analyticAt_twoWeightRadialSourceVector a b (A 0, B 0)).continuousAt.tendsto
  rw [twoWeightRadialSourceVector_zero a b ha hb] at hsource
  exact hsource.comp hchart

theorem weightedArc_difference_after_target_subtraction
    (G : Source 2 → Source 3) (F : Source 2 → ℂ) (Ψ : Source 2 → ℂ)
    (hF : ∀ᶠ q in 𝓝 (0 : Source 2), F q = G q 2 - Ψ (![G q 0, G q 1]))
    (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (A₁ B₁ A₂ B₂ : ℂ → ℂ)
    (hA₁ : AnalyticAt ℂ A₁ 0) (hB₁ : AnalyticAt ℂ B₁ 0)
    (hA₂ : AnalyticAt ℂ A₂ 0) (hB₂ : AnalyticAt ℂ B₂ 0)
    (hplane : ∀ᶠ q in 𝓝 (0 : Source 1),
      G (weightedSourceArc a b p A₁ B₁ q) 0 = G (weightedSourceArc a b p A₂ B₂ q) 0 ∧
      G (weightedSourceArc a b p A₁ B₁ q) 1 = G (weightedSourceArc a b p A₂ B₂ q) 1) :
    ∀ᶠ q in 𝓝 (0 : Source 1),
      F (weightedSourceArc a b p A₁ B₁ q) - F (weightedSourceArc a b p A₂ B₂ q) =
        G (weightedSourceArc a b p A₁ B₁ q) 2 - G (weightedSourceArc a b p A₂ B₂ q) 2 := by
  have ht1 := weightedSourceArc_tendsto_zero a b p ha hb hp A₁ B₁ hA₁ hB₁
  have ht2 := weightedSourceArc_tendsto_zero a b p ha hb hp A₂ B₂ hA₂ hB₂
  filter_upwards [ht1.eventually hF, ht2.eventually hF, hplane] with q h1 h2 hpl
  rw [h1, h2, hpl.1, hpl.2]
  ring

end OnLeConjecture.Analytic
