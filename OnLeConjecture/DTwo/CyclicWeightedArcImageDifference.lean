/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedLimitArc
public import OnLeConjecture.Analytic.WeightedArcInitialComparison
public import OnLeConjecture.Analytic.CyclicScaledSourceSeparation

/-!
# The original image difference on a weighted limiting arc

The finite base change identifies the original scaled source points with
arcs of weights `(L,2)`. The hypersurface factorization therefore gives
an exact radial unit order for the original third-coordinate difference.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def cyclicWeightedArcFunction
    (r : ℕ) (s : ℂ) (B : ℂ → ℂ) (t : ℂ) : Source 3 :=
  ![t ^ r * s, t ^ r * B t, t ^ 2]

theorem cyclicWeightedArcFunction_analyticAt
    (r : ℕ) (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (cyclicWeightedArcFunction r s B) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (analyticAt_id.pow r).mul analyticAt_const
  · exact (analyticAt_id.pow r).mul hB
  · exact analyticAt_id.pow 2

@[simp] theorem cyclicWeightedArcFunction_zero
    (r : ℕ) (hr : 0 < r) (s : ℂ) (B : ℂ → ℂ) :
    cyclicWeightedArcFunction r s B 0 = 0 := by
  ext i
  fin_cases i <;> simp [cyclicWeightedArcFunction, zero_pow hr.ne']

theorem cyclicWeightedArc_scaled_first
    (k p r L : ℕ) (hdegree : 2 * k + r = p * L)
    (s : ℂ) (B : ℂ → ℂ) (q : Source 1) :
    cyclicScaledFirstSource k p (cyclicWeightedArcFunction r s B (q 0)) =
      weightedSourceArc L 2 p (fun _ => s) (fun _ => 1) q := by
  have hpow : (q 0 ^ 2) ^ k * q 0 ^ r = (q 0 ^ p) ^ L := by
    rw [← pow_mul, ← pow_add, hdegree, pow_mul]
  ext i
  fin_cases i
  · change (q 0 ^ 2) ^ k * (q 0 ^ r * s) = (q 0 ^ p) ^ L * s
    rw [← mul_assoc, hpow]
  · change (q 0 ^ 2) ^ p = (q 0 ^ p) ^ 2 * 1
    simp only [← pow_mul, mul_one, Nat.mul_comm 2 p]

theorem cyclicWeightedArc_scaled_second
    (k p r L : ℕ) (hdegree : 2 * k + r = p * L)
    (s : ℂ) (B : ℂ → ℂ) (b : Source 3 → ℂ) (q : Source 1) :
    cyclicScaledSecondSource k p b (cyclicWeightedArcFunction r s B (q 0)) =
      weightedSourceArc L 2 p B (b ∘ cyclicWeightedArcFunction r s B) q := by
  have hpow : (q 0 ^ 2) ^ k * q 0 ^ r = (q 0 ^ p) ^ L := by
    rw [← pow_mul, ← pow_add, hdegree, pow_mul]
  ext i
  fin_cases i
  · change (q 0 ^ 2) ^ k * (q 0 ^ r * B (q 0)) = (q 0 ^ p) ^ L * B (q 0)
    rw [← mul_assoc, hpow]
  · change (q 0 ^ 2) ^ p * b (cyclicWeightedArcFunction r s B (q 0)) =
      (q 0 ^ p) ^ 2 * b (cyclicWeightedArcFunction r s B (q 0))
    simp only [← pow_mul, Nat.mul_comm 2 p]

/-- The exact unit order for the original third-coordinate image
difference, in the new weighted source coordinates. -/
theorem exists_cyclicWeightedArc_image_difference_unit
    (G : Source 2 → Source 3) (k p r L N : ℕ) (hr : 0 < r)
    (hdegree : 2 * k + r = p * L)
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0)
    (D : Source 3 → ℂ) (hD : AnalyticAt ℂ D 0)
    (hscale : ∀ᶠ q in 𝓝 (0 : Source 3),
      G (cyclicScaledFirstSource k p q) 2 - G (cyclicScaledSecondSource k p b q) 2 =
        q 2 ^ (k * N) * D q)
    (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) (hne : s ≠ B 0)
    (H v : Germ 3) (hv : IsUnit v)
    (hH : (cyclicWeightedArc r hr s B hB).pullbackRingHom H = 0)
    (hfactor : ofFunction D hD -
      (coordinate (0 : Fin 3) - coordinate (1 : Fin 3)) ^ N * v ∈ Ideal.span {H}) :
    AnalyticAt ℂ (b ∘ cyclicWeightedArcFunction r s B) 0 ∧
      (b ∘ cyclicWeightedArcFunction r s B) 0 = b 0 ∧
      ∃ U : Source 1 → ℂ, AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
        U 0 = (s - B 0) ^ N * valueRingHom 3 v ∧
        ∀ᶠ q in 𝓝 (0 : Source 1),
          G (weightedSourceArc L 2 p (fun _ => s) (fun _ => 1) q) 2 -
              G (weightedSourceArc L 2 p B (b ∘ cyclicWeightedArcFunction r s B) q) 2 =
            q 0 ^ (p * (L * N)) * U q := by
  have hγ := cyclicWeightedArcFunction_analyticAt r s B hB
  have hγ0 := cyclicWeightedArcFunction_zero r hr s B
  have hbcomp : AnalyticAt ℂ (b ∘ cyclicWeightedArcFunction r s B) 0 := by
    apply AnalyticAt.comp (x := (0 : ℂ)) _ hγ
    simpa only [hγ0] using hb
  have hb0 : (b ∘ cyclicWeightedArcFunction r s B) 0 = b 0 := by
    simp only [Function.comp_apply, hγ0]
  obtain ⟨u, hu, hpower, hvalue⟩ := cyclicWeightedArc_difference_power_unit
    k r N hr s B hB hne H (ofFunction D hD) v hv hH hfactor
  obtain ⟨U, hU, huU⟩ := exists_ofFunction u
  have hU0 : U 0 ≠ 0 := by
    have h := valueRingHom_ne_zero_of_isUnit hu
    simpa only [huU, valueRingHom_ofFunction] using h
  have hUvalue : U 0 = (s - B 0) ^ N * valueRingHom 3 v := by
    simpa only [huU, valueRingHom_ofFunction] using hvalue
  rw [huU] at hpower
  have hpowerFun : ∀ᶠ q in 𝓝 (0 : Source 1),
      (q 0 ^ 2) ^ (k * N) * D (cyclicWeightedArcFunction r s B (q 0)) =
        q 0 ^ ((2 * k + r) * N) * U q :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hpower)
  have ht : Tendsto (fun q : Source 1 => cyclicWeightedArcFunction r s B (q 0))
      (𝓝 0) (𝓝 (0 : Source 3)) := by
    have hγt : Tendsto (cyclicWeightedArcFunction r s B) (𝓝 (0 : ℂ)) (𝓝 (0 : Source 3)) := by
      simpa only [ContinuousAt, hγ0] using hγ.continuousAt
    exact hγt.comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).continuous.tendsto 0)
  refine ⟨hbcomp, hb0, U, hU, hU0, hUvalue, ?_⟩
  filter_upwards [ht.eventually hscale, hpowerFun] with q hq huq
  rw [cyclicWeightedArc_scaled_first k p r L hdegree,
    cyclicWeightedArc_scaled_second k p r L hdegree] at hq
  rw [hq]
  change (q 0 ^ 2) ^ (k * N) * D (cyclicWeightedArcFunction r s B (q 0)) = _
  rw [huq, hdegree, Nat.mul_assoc]

end OnLeConjecture.DTwo
