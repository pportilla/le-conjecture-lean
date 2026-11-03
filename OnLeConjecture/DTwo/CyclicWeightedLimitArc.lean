/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedLimitBranch
public import OnLeConjecture.DTwo.CyclicPlaneActualHypersurface
public import OnLeConjecture.Analytic.OneVariablePowerComparison

/-!
# Exact third-difference order on a lifted weighted arc

The lifted limiting branch lies on the actual first-plane hypersurface.
The proved hypersurface unit factorization then determines the exact
order and leading scalar of the original rescaled third difference.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def cyclicWeightedArc
    (r : ℕ) (hr : 0 < r) (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) :
    PointedMapGerm 1 3 :=
  PointedMapGerm.ofFunction
    (fun q : Source 1 => ![q 0 ^ r * s, q 0 ^ r * B (q 0), q 0 ^ 2])
    (by
      have ht := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0
      apply AnalyticAt.pi
      intro i
      fin_cases i
      · exact (ht.pow r).mul analyticAt_const
      · exact (ht.pow r).mul (cyclicCoefficient_analyticAt B hB)
      · exact ht.pow 2)
    (by ext i; fin_cases i <;> simp [zero_pow hr.ne'])

@[simp] theorem cyclicWeightedArc_pullback_first
    (r : ℕ) (hr : 0 < r) (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) :
    (cyclicWeightedArc r hr s B hB).pullbackRingHom (coordinate (0 : Fin 3)) =
      coordinate (0 : Fin 1) ^ r * constRingHom 1 s := by
  apply Subtype.ext
  rfl

@[simp] theorem cyclicWeightedArc_pullback_second
    (r : ℕ) (hr : 0 < r) (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) :
    (cyclicWeightedArc r hr s B hB).pullbackRingHom (coordinate (1 : Fin 3)) =
      coordinate (0 : Fin 1) ^ r * cyclicCoefficientGerm B hB := by
  apply Subtype.ext
  rfl

@[simp] theorem cyclicWeightedArc_pullback_last
    (r : ℕ) (hr : 0 < r) (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) :
    (cyclicWeightedArc r hr s B hB).pullbackRingHom (coordinate (2 : Fin 3)) =
      coordinate (0 : Fin 1) ^ 2 := by
  apply Subtype.ext
  rfl

/-- The analytic limiting branch solves the original first-plane equation
after the finite base change, not only its quadratic initial equation. -/
theorem cyclicWeightedArc_pullback_equation
    (p ν j r : ℕ) (hp : 2 ≤ p) (hr : 0 < r) (hrEq : r = ν + p * j)
    (ε : ℂ → ℂ) (hε : AnalyticAt ℂ ε 0)
    (K : Source 3 → ℂ) (hK : AnalyticAt ℂ K 0)
    (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0)
    (hsol : ∀ᶠ t in 𝓝 (0 : ℂ), cyclicWeightedLimitEquation p ν r ε K s (t, B t) = 0)
    (H : Germ 3)
    (hH : H = coordinate (0 : Fin 3) ^ 2 - coordinate (1 : Fin 3) ^ 2 +
      coordinate 2 ^ ν * (coordinate 2 ^ (p * j) *
        cyclicLastExtension (cyclicCoefficientGerm ε hε) +
          (coordinate 0 ^ p - coordinate 1 ^ p) * ofFunction K hK)) :
    (cyclicWeightedArc r hr s B hB).pullbackRingHom H = 0 := by
  rw [hH]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have ht : Tendsto (fun q : Source 1 => q 0) (𝓝 0) (𝓝 (0 : ℂ)) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).continuous.tendsto 0
  filter_upwards [ht.eventually hsol] with q hq
  change (q 0 ^ r * s) ^ 2 - (q 0 ^ r * B (q 0)) ^ 2 +
    (q 0 ^ 2) ^ ν * ((q 0 ^ 2) ^ (p * j) * ε (q 0 ^ 2) +
      ((q 0 ^ r * s) ^ p - (q 0 ^ r * B (q 0)) ^ p) *
        K (![q 0 ^ r * s, q 0 ^ r * B (q 0), q 0 ^ 2])) = 0
  rw [cyclicWeightedLimit_scaling_identity p ν j r hp hrEq]
  change q 0 ^ (2 * r) * cyclicWeightedLimitEquation p ν r ε K s (q 0, B (q 0)) = 0
  rw [hq, mul_zero]

/-- The exact radial order and leading scalar of the difference on an
actual lifted branch follow from the hypersurface factorization. -/
theorem cyclicWeightedArc_difference_power_unit
    (k r N : ℕ) (hr : 0 < r)
    (s : ℂ) (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) (hne : s ≠ B 0)
    (H D v : Germ 3) (hv : IsUnit v)
    (hH : (cyclicWeightedArc r hr s B hB).pullbackRingHom H = 0)
    (hfactor : D - (coordinate (0 : Fin 3) - coordinate (1 : Fin 3)) ^ N * v ∈
      Ideal.span {H}) :
    ∃ u : Germ 1, IsUnit u ∧
      (cyclicWeightedArc r hr s B hB).pullbackRingHom
          (coordinate (2 : Fin 3) ^ (k * N) * D) =
        coordinate (0 : Fin 1) ^ ((2 * k + r) * N) * u ∧
      valueRingHom 1 u = (s - B 0) ^ N * valueRingHom 3 v := by
  let φ := cyclicWeightedArc r hr s B hB
  let a := constRingHom 1 s - cyclicCoefficientGerm B hB
  have ha : IsUnit a := by
    apply isUnit_iff_valueRingHom_ne_zero.mpr
    simpa only [a, map_sub, valueRingHom_const, cyclicCoefficientGerm,
      valueRingHom_ofFunction, Pi.zero_apply] using sub_ne_zero.mpr hne
  let u := a ^ N * φ.pullbackRingHom v
  have hu : IsUnit u := (ha.pow N).mul (hv.map φ.pullbackRingHom)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hfactor
  have hmap := congrArg φ.pullbackRingHom hq
  rw [map_sub, map_mul, map_pow, map_sub, map_mul, hH, zero_mul] at hmap
  have hD : φ.pullbackRingHom D = coordinate (0 : Fin 1) ^ (r * N) * u := by
    have h := sub_eq_zero.mp hmap
    rw [cyclicWeightedArc_pullback_first, cyclicWeightedArc_pullback_second,
      ← mul_sub, mul_pow, ← pow_mul, mul_assoc] at h
    exact h
  refine ⟨u, hu, ?_, ?_⟩
  · rw [map_mul, map_pow, cyclicWeightedArc_pullback_last, ← pow_mul,
      hD, ← mul_assoc, ← pow_add]
    congr 2
    ring
  · simp only [u, a, map_mul, map_pow, map_sub, PointedMapGerm.valueRingHom_pullback,
      valueRingHom_const, cyclicCoefficientGerm, valueRingHom_ofFunction, Pi.zero_apply]

end OnLeConjecture.DTwo
