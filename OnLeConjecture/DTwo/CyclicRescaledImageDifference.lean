/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicScaledSourceSeparation
public import OnLeConjecture.DTwo.CyclicPlaneActualHypersurface

/-!
# The actual three rescaled image differences

The first two prepared coordinates give exact polynomial scaling
identities. Combining them with an analytic rescaled third difference
produces the family used on the cyclic hypersurface.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def cyclicRescaledImageDifference
    (k p : ℕ) (β : ℂ → ℂ) (b D : Source 3 → ℂ) (q : Source 3) : Source 3 :=
  ![q 0 ^ 2 - q 1 ^ 2 + q 2 ^ (k * (p - 2)) * (1 - b q ^ k),
    q 0 ^ p - q 1 ^ p + β (q 2 ^ p) - b q ^ k * β (q 2 ^ p * b q), D q]

theorem cyclicRescaledImageDifference_analyticAt
    (k p : ℕ) (hp : 0 < p) (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0)
    (b D : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) (hD : AnalyticAt ℂ D 0) :
    AnalyticAt ℂ (cyclicRescaledImageDifference k p β b D) 0 := by
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  have hβ1 : AnalyticAt ℂ (fun q : Source 3 => β (q 2 ^ p)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 3)) _ ((hq 2).pow p)
    simpa only [Pi.pow_apply, Pi.zero_apply, zero_pow hp.ne'] using hβ
  have hβ2 : AnalyticAt ℂ (fun q : Source 3 => β (q 2 ^ p * b q)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 3)) _ (((hq 2).pow p).mul hb)
    simpa only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, zero_pow hp.ne', zero_mul] using hβ
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (((hq 0).pow 2).sub ((hq 1).pow 2)).add
      (((hq 2).pow (k * (p - 2))).mul (analyticAt_const.sub (hb.pow k)))
  · exact ((((hq 0).pow p).sub ((hq 1).pow p)).add hβ1).sub ((hb.pow k).mul hβ2)
  · exact hD

theorem cyclicFirst_scaling_identity
    (k p : ℕ) (hp : 2 ≤ p) (lmb s S b : ℂ) :
    ((lmb ^ k * s) ^ 2 + (lmb ^ p) ^ k) -
        ((lmb ^ k * S) ^ 2 + (lmb ^ p * b) ^ k) =
      lmb ^ (2 * k) * (s ^ 2 - S ^ 2 + lmb ^ (k * (p - 2)) * (1 - b ^ k)) := by
  have hexp : p * k = 2 * k + k * (p - 2) := by
    have h := Nat.sub_add_cancel hp
    nlinarith
  simp only [mul_pow, ← pow_mul, hexp, pow_add, Nat.mul_comm k 2]
  ring

theorem cyclicSecond_scaling_identity
    (k p : ℕ) (β : ℂ → ℂ) (lmb s S b : ℂ) :
    ((lmb ^ k * s) ^ p + (lmb ^ p) ^ k * β (lmb ^ p)) -
        ((lmb ^ k * S) ^ p + (lmb ^ p * b) ^ k * β (lmb ^ p * b)) =
      lmb ^ (k * p) * (s ^ p - S ^ p + β (lmb ^ p) - b ^ k * β (lmb ^ p * b)) := by
  simp only [mul_pow, ← pow_mul, Nat.mul_comm p k]
  ring

/-- The two prepared equations and the analytic third rescaling give all
three image-difference identities in one neighborhood. -/
theorem eventually_cyclicRescaledImageDifference_scaling
    (G : Source 2 → Source 3) (k p d : ℕ) (hk : 0 < k) (hp : 2 ≤ p)
    (β : ℂ → ℂ) (b D : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0)
    (hP : ∀ᶠ z in 𝓝 (0 : Source 2), G z 0 = z 0 ^ 2 + z 1 ^ k)
    (hQ : ∀ᶠ z in 𝓝 (0 : Source 2), G z 1 = z 0 ^ p + z 1 ^ k * β (z 1))
    (hthird : ∀ᶠ q in 𝓝 (0 : Source 3),
      G (cyclicScaledFirstSource k p q) 2 - G (cyclicScaledSecondSource k p b q) 2 =
        q 2 ^ d * D q) :
    ∀ᶠ q in 𝓝 (0 : Source 3), ∀ i,
      G (cyclicScaledFirstSource k p q) i - G (cyclicScaledSecondSource k p b q) i =
        q 2 ^ (![2 * k, k * p, d] i) * cyclicRescaledImageDifference k p β b D q i := by
  have hp0 : 0 < p := by omega
  have hvec : (![0, 0] : Source 2) = 0 := by ext i; fin_cases i <;> rfl
  have ht1 : Tendsto (cyclicScaledFirstSource k p) (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [ContinuousAt, cyclicScaledFirstSource, Pi.zero_apply,
      zero_pow hk.ne', zero_pow hp0.ne', zero_mul, hvec] using
      (cyclicScaledFirstSource_analyticAt k p).continuousAt
  have ht2 : Tendsto (cyclicScaledSecondSource k p b) (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [ContinuousAt, cyclicScaledSecondSource, Pi.zero_apply,
      zero_pow hk.ne', zero_pow hp0.ne', zero_mul, hvec] using
      (cyclicScaledSecondSource_analyticAt k p b hb).continuousAt
  filter_upwards [ht1.eventually hP, ht2.eventually hP,
    ht1.eventually hQ, ht2.eventually hQ, hthird] with q hP1 hP2 hQ1 hQ2 hD i
  fin_cases i
  · change G (cyclicScaledFirstSource k p q) 0 -
      G (cyclicScaledSecondSource k p b q) 0 = _
    rw [hP1, hP2]
    exact cyclicFirst_scaling_identity k p hp (q 2) (q 0) (q 1) (b q)
  · change G (cyclicScaledFirstSource k p q) 1 -
      G (cyclicScaledSecondSource k p b q) 1 = _
    rw [hQ1, hQ2]
    exact cyclicSecond_scaling_identity k p β (q 2) (q 0) (q 1) (b q)
  · exact hD

end OnLeConjecture.DTwo
