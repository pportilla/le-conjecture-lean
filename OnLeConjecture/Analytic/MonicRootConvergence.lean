/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Convergence of roots of pointed monic relations

Suppose the lower coefficients of a monic polynomial relation tend to zero.
Every choice of a root of that relation then tends to zero. The proof gives a
uniform estimate and does not require a continuous choice of roots.
-/

public section

open Filter Set
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic

/-- Let `root p` satisfy a monic relation of fixed positive degree whose lower
coefficients tend to zero. Then `root p` tends to zero. -/
theorem tendsto_zero_of_monic_power_relation
    {P : Type*} {l : Filter P} {d : ℕ} (hd : 0 < d)
    (coefficient : Fin d → P → ℂ) (root : P → ℂ)
    (hcoefficient : ∀ i, Tendsto (coefficient i) l (nhds 0))
    (hroot : ∀ᶠ p in l,
      root p ^ d +
        ∑ i : Fin d, coefficient i p * root p ^ (i : ℕ) = 0) :
    Tendsto root l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let delta : ℝ := min epsilon 1 / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaEpsilon : delta < epsilon := by
    dsimp [delta]
    have hmin : min epsilon 1 ≤ epsilon := min_le_left _ _
    nlinarith [hdelta]
  let eta : ℝ := min 1 (delta ^ d) / (2 * d)
  have hdReal : (0 : ℝ) < d := by
    exact_mod_cast hd
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hdEtaOne : (d : ℝ) * eta < 1 := by
    dsimp [eta]
    have hmin : min 1 (delta ^ d) ≤ 1 := min_le_left _ _
    have hminPos : 0 < min 1 (delta ^ d) := by
      positivity
    calc
      (d : ℝ) * (min 1 (delta ^ d) / (2 * d)) =
          min 1 (delta ^ d) / 2 := by field_simp
      _ < 1 := by nlinarith
  have hdEtaDelta : (d : ℝ) * eta < delta ^ d := by
    dsimp [eta]
    have hmin : min 1 (delta ^ d) ≤ delta ^ d := min_le_right _ _
    have hminPos : 0 < min 1 (delta ^ d) := by
      positivity
    calc
      (d : ℝ) * (min 1 (delta ^ d) / (2 * d)) =
          min 1 (delta ^ d) / 2 := by field_simp
      _ < delta ^ d := by nlinarith
  have hcoefficients : ∀ᶠ p in l,
      ∀ i : Fin d, ‖coefficient i p‖ < eta := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := (hcoefficient i).eventually
      (Metric.ball_mem_nhds (0 : ℂ) heta)
    filter_upwards [hi] with p hp
    simpa only [Metric.mem_ball, dist_zero_right] using hp
  filter_upwards [hcoefficients, hroot] with p hpCoefficient hpRoot
  rw [dist_zero_right]
  have hnormPower : ‖root p‖ ^ d ≤
      ∑ i : Fin d,
        ‖coefficient i p‖ * ‖root p‖ ^ (i : ℕ) := by
    calc
      ‖root p‖ ^ d = ‖root p ^ d‖ := (norm_pow _ _).symm
      _ = ‖-(∑ i : Fin d,
          coefficient i p * root p ^ (i : ℕ))‖ := by
        congr 1
        exact eq_neg_of_add_eq_zero_left hpRoot
      _ = ‖∑ i : Fin d,
          coefficient i p * root p ^ (i : ℕ)‖ := norm_neg _
      _ ≤ ∑ i : Fin d,
          ‖coefficient i p * root p ^ (i : ℕ)‖ :=
        norm_sum_le _ _
      _ = ∑ i : Fin d,
          ‖coefficient i p‖ * ‖root p‖ ^ (i : ℕ) := by
        congr 1
        funext i
        rw [norm_mul, norm_pow]
  have hrootNormOne : ‖root p‖ < 1 := by
    by_contra hnot
    have hone : 1 ≤ ‖root p‖ := le_of_not_gt hnot
    have hsumLe :
        (∑ i : Fin d,
          ‖coefficient i p‖ * ‖root p‖ ^ (i : ℕ)) ≤
            (d : ℝ) * eta * ‖root p‖ ^ d := by
      calc
        (∑ i : Fin d,
            ‖coefficient i p‖ * ‖root p‖ ^ (i : ℕ)) ≤
            ∑ _i : Fin d, eta * ‖root p‖ ^ d := by
          apply Finset.sum_le_sum
          intro i _hi
          gcongr
          · exact (hpCoefficient i).le
          · exact Nat.le_of_lt i.isLt
        _ = (d : ℝ) * eta * ‖root p‖ ^ d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp only [nsmul_eq_mul]
          ring
    have hpowPos : 0 < ‖root p‖ ^ d := by
      positivity
    have hstrict :
        (d : ℝ) * eta * ‖root p‖ ^ d < ‖root p‖ ^ d :=
      mul_lt_of_lt_one_left hpowPos hdEtaOne
    exact (not_lt_of_ge (hnormPower.trans hsumLe)) hstrict
  have hsumLeDelta :
      (∑ i : Fin d,
        ‖coefficient i p‖ * ‖root p‖ ^ (i : ℕ)) ≤
          (d : ℝ) * eta := by
    calc
      (∑ i : Fin d,
          ‖coefficient i p‖ * ‖root p‖ ^ (i : ℕ)) ≤
          ∑ _i : Fin d, eta := by
        apply Finset.sum_le_sum
        intro i _hi
        have hpowLe : ‖root p‖ ^ (i : ℕ) ≤ 1 := by
          simpa only [one_pow] using
            pow_le_pow_left₀ (norm_nonneg _) hrootNormOne.le (i : ℕ)
        calc
          ‖coefficient i p‖ * ‖root p‖ ^ (i : ℕ) ≤
              eta * ‖root p‖ ^ (i : ℕ) := by
            gcongr
            exact (hpCoefficient i).le
          _ ≤ eta * 1 := by gcongr
          _ = eta := mul_one _
      _ = (d : ℝ) * eta := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [nsmul_eq_mul]
  have hpowerLt : ‖root p‖ ^ d < delta ^ d :=
    lt_of_le_of_lt (hnormPower.trans hsumLeDelta) hdEtaDelta
  have hnormDelta : ‖root p‖ < delta :=
    (pow_lt_pow_iff_left₀ (norm_nonneg _) hdelta.le hd.ne').mp
      hpowerLt
  exact hnormDelta.trans hdeltaEpsilon

end OnLeConjecture.Analytic
