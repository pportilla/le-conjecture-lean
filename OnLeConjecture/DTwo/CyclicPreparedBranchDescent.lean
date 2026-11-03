/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPreparedHypersurfaceFactorization
public import OnLeConjecture.DTwo.CyclicThirdDifferenceFromWeightedTail

/-!
# Descent for the prepared cyclic map from the original analytic data

The implicit branch, rescaled third difference, and unit factorization
are all constructed from the prepared first two coordinates and the
strict weighted tail of the third. This is the local descent assertion,
not the final exclusion of the cyclic case.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The actual local branch and third-difference factorization associated
with a noninvariant root of unity. -/
theorem exists_cyclicPrepared_branch_descent
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p N : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hN : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : ∀ᶠ q in 𝓝 (0 : Source 2), G q 0 = q 0 ^ 2 + q 1 ^ k)
    (hQ : ∀ᶠ q in 𝓝 (0 : Source 2), G q 1 = q 0 ^ p + q 1 ^ k * β (q 1))
    (htail : ofFunction (fun q => G q 2) (analyticAt_pi_iff.mp hG 2) -
      coordinate (0 : Fin 2) ^ N ∈ twoWeightOrderIdeal k p (k * N + 1))
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (hne : cyclicCoefficientGerm β hβ -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ) ≠ 0) :
    ∃ z : ℂ × ℂ → ℂ, ∃ hz : AnalyticAt ℂ z 0,
      z 0 = ζ ∧
      (∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
        q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0) ∧
      ∃ D : Source 3 → ℂ, ∃ hD : AnalyticAt ℂ D 0,
        (∀ᶠ q in 𝓝 (0 : Source 3),
          G (cyclicScaledFirstSource k p q) 2 -
              G (cyclicScaledSecondSource k p (cyclicPowerDifferenceBranch p z) q) 2 =
            q 2 ^ (k * N) * D q) ∧
        (coordinate (2 : Fin 3) ∣ ofFunction D hD -
          (coordinate (0 : Fin 3) ^ N - coordinate (1 : Fin 3) ^ N)) ∧
        ∃ v : Germ 3, IsUnit v ∧
          ofFunction D hD - (coordinate (0 : Fin 3) - coordinate (1 : Fin 3)) ^ N * v ∈
            Ideal.span {cyclicFirstPlaneGerm k p z hz} := by
  have hp0 : 0 < p := by omega
  obtain ⟨z, hz, hz0, hsol⟩ := exists_cyclicPlane_analytic_branch k p hk hp0 β hβ hc ζ hζ
  have hb := cyclicPowerDifferenceBranch_analyticAt p z hz
  obtain ⟨D, hD, hscale, hdiv⟩ := exists_cyclic_third_difference_of_weighted_tail
    G hG k p N hk hp0 htail (cyclicPowerDifferenceBranch p z) hb
  refine ⟨z, hz, hz0, hsol, D, hD, hscale, hdiv, ?_⟩
  exact cyclicPlane_branch_third_factorization G hinjective k p N (k * N) hk hp hN
    β hβ hc hP hQ ζ hζ hζ0 hζ1 hne z hz hz0 hsol D hD hscale hdiv

end OnLeConjecture.DTwo
