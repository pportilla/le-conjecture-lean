/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPreparedBranchDescent
public import OnLeConjecture.Analytic.ReducibleHypersurfaceCollision

/-!
# Exclusion of an invariant cyclic coefficient

An invariant coefficient makes the parameter defect vanish identically.
The resulting reducible first-plane equation contradicts injectivity on
its component with nonzero odd special-axis restriction.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclicPlane_parameter_defect_eq_zero_of_invariant
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0)
    (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) (hz0 : z 0 = ζ)
    (hsol : ∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
      q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0)
    (hinvariant : cyclicCoefficientGerm β hβ =
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ)) :
    cyclicParameterDefect p (cyclicBranchDefectGerm k z hz) = 0 := by
  let b : Source 1 → ℂ := fun q => z (0, q 0)
  have hb := cyclicBranchSlice_analyticAt z hz
  have hb0 : b 0 = ζ := by simpa only [b, Pi.zero_apply, Prod.zero_eq_mk] using hz0
  have hparam : AnalyticAt ℂ (fun q : Source 1 => ((0 : ℂ), q 0)) 0 :=
    analyticAt_const.prod
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
  have ht : Tendsto (fun q : Source 1 => ((0 : ℂ), q 0))
      (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    simpa only [ContinuousAt, Pi.zero_apply, Prod.zero_eq_mk] using hparam.continuousAt
  have hbsol : ∀ᶠ q in 𝓝 (0 : Source 1),
      β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0 := by
    filter_upwards [ht.eventually hsol] with q hq
    simpa only [zero_add] using hq
  have hzero := cyclicBranch_defect_eq_zero_of_invariant k p hk hp β hβ hc
    b hb ζ hb0 hζ hζ0 hbsol hinvariant
  rw [cyclicParameterDefect_eq_lastExtension, cyclicBranchDefectGerm_restriction,
    hzero, map_zero]

/-- Injectivity of the prepared map forces noninvariance under every
nonidentity root of unity used in the local cyclic comparison. -/
theorem cyclicPrepared_coefficient_noninvariant
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p N : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hN : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : ∀ᶠ q in 𝓝 (0 : Source 2), G q 0 = q 0 ^ 2 + q 1 ^ k)
    (hQ : ∀ᶠ q in 𝓝 (0 : Source 2), G q 1 = q 0 ^ p + q 1 ^ k * β (q 1))
    (htail : ofFunction (fun q => G q 2) (analyticAt_pi_iff.mp hG 2) -
      coordinate (0 : Fin 2) ^ N ∈ twoWeightOrderIdeal k p (k * N + 1))
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    cyclicCoefficientGerm β hβ -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ) ≠ 0 := by
  intro heq
  have hp0 : 0 < p := by omega
  obtain ⟨z, hz, hz0, hsol⟩ := exists_cyclicPlane_analytic_branch k p hk hp0 β hβ hc ζ hζ
  have hδ := cyclicPlane_parameter_defect_eq_zero_of_invariant k p hk hp0 β hβ hc
    ζ hζ hζ0 z hz hz0 hsol (sub_eq_zero.mp heq)
  let ν := k * (p - 2)
  have hν : 0 < ν := Nat.mul_pos hk (by omega)
  let b := cyclicPowerDifferenceBranch p z
  have hb := cyclicPowerDifferenceBranch_analyticAt p z hz
  have hb0 : b 0 ≠ 1 := by
    change cyclicPowerDifferenceBranch p z 0 ≠ 1
    rw [cyclicPowerDifferenceBranch_zero, hz0]
    exact hζ1
  obtain ⟨D, hD, hthird, hdiv⟩ := exists_cyclic_third_difference_of_weighted_tail
    G hG k p N hk hp0 htail b hb
  obtain ⟨K, h, e, _, _, hhEq, he0, he1, he2, hplane⟩ :=
    exists_cyclicPlane_hypersurface_coordinates p ν hp (cyclicBranchDefectGerm k z hz)
  have heH : e.forward.pullbackRingHom (coordinate 0 * coordinate 1) =
      (1 : Germ 3) * cyclicFirstPlaneGerm k p z hz := by
    rw [hδ, mul_zero, add_zero, cyclicBranchDefectGerm_powerDifference_pullback] at hplane
    simpa only [one_mul, cyclicFirstPlaneGerm, ν] using hplane.symm
  have hcorr : coordinate (2 : Fin 3) ∣ h := by
    rw [hhEq]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self _ hν.ne') _) _
  let R := cyclicRescaledImageDifference k p β b D
  have hR := cyclicRescaledImageDifference_analyticAt k p hp0 β hβ b D hb hD
  have hscale := eventually_cyclicRescaledImageDifference_scaling G k p (k * N) hk
    (by omega) β b D hb hP hQ hthird
  have hR0 : ofFunction (fun q => R q 0) (analyticAt_pi_iff.mp hR 0) =
      cyclicFirstPlaneGerm k p z hz := by
    apply Subtype.ext
    rfl
  have hR1 : ofFunction (fun q => R q 1) (analyticAt_pi_iff.mp hR 1) = 0 := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact cyclicPowerDifferenceBranch_solves k p β z hsol
  have hR2 : ofFunction (fun q => R q 2) (analyticAt_pi_iff.mp hR 2) = ofFunction D hD := by
    apply Subtype.ext
    rfl
  have he1' : e.forward.pullbackRingHom (coordinate (1 : Fin 3)) =
      (coordinate 0 + coordinate 1 + h) * 1 := by simpa only [mul_one] using he1
  exact Analytic.CyclicCover.false_of_reducible_hypersurface_scaled_injectivity
    G hinjective k p N hk hp0 hN b hb hb0 ![2 * k, k * p, k * N] R hR hscale
    (cyclicFirstPlaneGerm k p z hz) (ofFunction D hD) h 1 1 isUnit_one isUnit_one
    hR0 hR1 hR2 e he0 he1' he2 heH hcorr hdiv

end OnLeConjecture.DTwo
