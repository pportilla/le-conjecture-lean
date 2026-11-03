/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedArcImageDifference
public import OnLeConjecture.DTwo.CyclicPreparedHypersurfaceFactorization

/-!
# Weighted limiting arcs in the actual plane fiber product

The lifted first-plane equation and the implicit second equation imply
equality of the original first two target coordinates along the two
weighted arcs. Target subtraction can therefore be used on these arcs.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclicWeightedArc_plane_images_agree
    (G : Source 2 → Source 3) (k p r L : ℕ)
    (hk : 0 < k) (hp : 3 ≤ p) (hr : 0 < r) (hdegree : 2 * k + r = p * L)
    (β : ℂ → ℂ)
    (hP : ∀ᶠ q in 𝓝 (0 : Source 2), G q 0 = q 0 ^ 2 + q 1 ^ k)
    (hQ : ∀ᶠ q in 𝓝 (0 : Source 2), G q 1 = q 0 ^ p + q 1 ^ k * β (q 1))
    (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0)
    (hsol : ∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
      q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0)
    (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0)
    (hH : (cyclicWeightedArc r hr s B hB).pullbackRingHom
      (cyclicFirstPlaneGerm k p z hz) = 0) :
    ∀ᶠ q in 𝓝 (0 : Source 1),
      G (weightedSourceArc L 2 p (fun _ => s) (fun _ => 1) q) 0 =
        G (weightedSourceArc L 2 p B
          (cyclicPowerDifferenceBranch p z ∘ cyclicWeightedArcFunction r s B) q) 0 ∧
      G (weightedSourceArc L 2 p (fun _ => s) (fun _ => 1) q) 1 =
        G (weightedSourceArc L 2 p B
          (cyclicPowerDifferenceBranch p z ∘ cyclicWeightedArcFunction r s B) q) 1 := by
  let b := cyclicPowerDifferenceBranch p z
  have hb := cyclicPowerDifferenceBranch_analyticAt p z hz
  let D := fun q : Source 3 =>
    G (cyclicScaledFirstSource k p q) 2 - G (cyclicScaledSecondSource k p b q) 2
  have hthird : ∀ᶠ q in 𝓝 (0 : Source 3),
      G (cyclicScaledFirstSource k p q) 2 - G (cyclicScaledSecondSource k p b q) 2 =
        q 2 ^ 0 * D q := Filter.Eventually.of_forall fun q => by simp [D]
  have hscale := eventually_cyclicRescaledImageDifference_scaling
    G k p 0 hk (by omega) β b D hb hP hQ hthird
  have hγ := cyclicWeightedArcFunction_analyticAt r s B hB
  have hγ0 := cyclicWeightedArcFunction_zero r hr s B
  have ht : Tendsto (fun q : Source 1 => cyclicWeightedArcFunction r s B (q 0))
      (𝓝 0) (𝓝 (0 : Source 3)) := by
    have htγ : Tendsto (cyclicWeightedArcFunction r s B) (𝓝 (0 : ℂ)) (𝓝 (0 : Source 3)) := by
      simpa only [ContinuousAt, hγ0] using hγ.continuousAt
    exact htγ.comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).continuous.tendsto 0)
  have hHfun : ∀ᶠ q in 𝓝 (0 : Source 1),
      cyclicRescaledImageDifference k p β b D (cyclicWeightedArcFunction r s B (q 0)) 0 = 0 :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hH)
  have hQfun := cyclicPowerDifferenceBranch_solves k p β z hsol
  filter_upwards [ht.eventually hscale, hHfun, ht.eventually hQfun] with q hsc hHzero hQzero
  have hfirst : G (cyclicScaledFirstSource k p (cyclicWeightedArcFunction r s B (q 0))) 0 =
      G (cyclicScaledSecondSource k p b (cyclicWeightedArcFunction r s B (q 0))) 0 := by
    apply sub_eq_zero.mp
    rw [hsc 0, hHzero, mul_zero]
  have hsecond : G (cyclicScaledFirstSource k p (cyclicWeightedArcFunction r s B (q 0))) 1 =
      G (cyclicScaledSecondSource k p b (cyclicWeightedArcFunction r s B (q 0))) 1 := by
    apply sub_eq_zero.mp
    rw [hsc 1]
    change _ * ((cyclicWeightedArcFunction r s B (q 0)) 0 ^ p -
      (cyclicWeightedArcFunction r s B (q 0)) 1 ^ p +
      β ((cyclicWeightedArcFunction r s B (q 0)) 2 ^ p) -
      b (cyclicWeightedArcFunction r s B (q 0)) ^ k *
        β ((cyclicWeightedArcFunction r s B (q 0)) 2 ^ p *
          b (cyclicWeightedArcFunction r s B (q 0)))) = 0
    rw [hQzero, mul_zero]
  rw [cyclicWeightedArc_scaled_first k p r L hdegree,
    cyclicWeightedArc_scaled_second k p r L hdegree] at hfirst hsecond
  exact ⟨hfirst, hsecond⟩

end OnLeConjecture.DTwo
