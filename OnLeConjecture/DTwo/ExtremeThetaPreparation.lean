/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.ExtremeThetaDecomposition
public import OnLeConjecture.DTwo.CyclicMinimalIntersectionExclusion
public import OnLeConjecture.Analytic.TargetAxisTriangularNormalization
public import OnLeConjecture.PlaneCurve.JacobianInvariance

/-!
# Convergent theta preparation from the extreme intersection number

The Jacobian recurrence constructs the coefficients. If the coefficient
of theta vanished at the origin, subtracting a multiple of the first
component would leave a germ of ordinary order at least `2k`, forcing
intersection at least `4k`. Analytic triangular target changes therefore
normalize that coefficient and eliminate theta from the third component.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The constant coefficient in the theta decomposition has the value
of the original germ. -/
theorem value_even_coefficient_of_extreme_theta_decomposition
    (k : ℕ) (hk : 1 ≤ k) (H : Germ 2) (A B : Germ 1) (C : Germ 2)
    (hH : H = (cyclicScalarMap k hk).pullbackRingHom A +
      extremeTheta k * (cyclicScalarMap k hk).pullbackRingHom B + coordinate 1 ^ (2 * k) * C) :
    valueRingHom 1 A = valueRingHom 2 H := by
  rw [hH]
  simp only [extremeTheta, map_add, map_mul, map_pow, map_ofNat,
    valueRingHom_coordinate, PointedMapGerm.valueRingHom_pullback, zero_mul,
    zero_pow (by omega : 2 * k ≠ 0), add_zero]

/-- The selected intersection determines a nonzero theta coefficient.
The weaker inequality `i<4k` is sufficient, so parity is unnecessary. -/
theorem theta_coefficient_nonzero_of_intersection_lt_four_mul
    (k : ℕ) (hk : 2 ≤ k) (H : Germ 2) (A B : Germ 1) (C : Germ 2)
    (hA : A ∈ maximalIdeal 1)
    (hH : H = (cyclicScalarMap k (by omega)).pullbackRingHom A +
      extremeTheta k * (cyclicScalarMap k (by omega)).pullbackRingHom B +
        coordinate 1 ^ (2 * k) * C)
    (hfinite : PlaneCurve.HasFiniteIntersection (cyclicFirst k) H)
    (hsmall : PlaneCurve.intersectionMultiplicity (cyclicFirst k) H hfinite < 4 * k) :
    valueRingHom 1 B ≠ 0 := by
  intro hzero
  have hB : B ∈ maximalIdeal 1 := mem_maximalIdeal_iff.mpr hzero
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
    (show A ∈ Ideal.span {coordinate (0 : Fin 1)} by
      rwa [← maximalIdeal_one_eq_span_coordinate])
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
    (show B ∈ Ideal.span {coordinate (0 : Fin 1)} by
      rwa [← maximalIdeal_one_eq_span_coordinate])
  let σ := cyclicScalarMap k (by omega : 1 ≤ k)
  let q := σ.pullbackRingHom a + extremeTheta k * σ.pullbackRingHom b
  have hcoord : σ.pullbackRingHom (coordinate 0) = cyclicFirst k := by
    rw [PointedMapGerm.pullback_coordinate, cyclicScalarMap_component]
    rfl
  have heq : H - cyclicFirst k * q = coordinate 1 ^ (2 * k) * C := by
    rw [hH, ha, hb, map_mul, map_mul]
    change (σ.pullbackRingHom (coordinate 0) * σ.pullbackRingHom a +
      extremeTheta k * (σ.pullbackRingHom (coordinate 0) * σ.pullbackRingHom b) +
        coordinate 1 ^ (2 * k) * C) - cyclicFirst k * q = _
    rw [hcoord]
    dsimp only [q]
    ring
  have hideal : PlaneCurve.pairIdeal (cyclicFirst k) H =
      PlaneCurve.pairIdeal (cyclicFirst k) (coordinate 1 ^ (2 * k) * C) := by
    rw [← heq, PlaneCurve.pairIdeal_sub_mul_right]
  have hfinite' := hfinite.of_pairIdeal_eq hideal
  have hi := PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq hfinite hfinite' hideal
  have horder : coordinate (1 : Fin 2) ^ (2 * k) * C ∈ maximalIdeal 2 ^ (2 * k) :=
    (maximalIdeal 2 ^ (2 * k)).mul_mem_right C
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) (2 * k))
  obtain ⟨hP, hPnext⟩ := cyclicFirst_exact_order_two k hk
  have hbound := ordinary_intersection_lower_bound 2 (2 * k) (by omega)
    (cyclicFirst k) (coordinate 1 ^ (2 * k) * C) hP hPnext horder hfinite'
  omega

/-- Construct the analytic target changes and preserve the selected pair
ideal. The two theta coefficients are outputs of the recurrence. -/
theorem exists_extreme_theta_preparation_of_intersection_lt_four_mul
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (hP : g.1.component 0 = cyclicFirst k)
    (hJQ : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (g.1.component 0) (g.1.component 1))
    (hJZ : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (g.1.component 0) (g.1.component 2))
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hsmall : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite < 4 * k) :
    ∃ f : PointedMapGerm 2 3, ∃ C₂ C₃ : Germ 2,
      g.RightLeftEquivalent f ∧ f.1.component 0 = cyclicFirst k ∧
      f.1.component 1 = extremeTheta k + coordinate 1 ^ (2 * k) * C₂ ∧
      f.1.component 2 = coordinate 1 ^ (2 * k) * C₃ ∧
      PlaneCurve.pairIdeal (f.1.component 0) (f.1.component 1) =
        PlaneCurve.pairIdeal (g.1.component 0) (g.1.component 1) := by
  have hJQ' := hJQ
  have hJZ' := hJZ
  rw [hP] at hJQ' hJZ'
  obtain ⟨A, B, H₂, hQ⟩ := exists_extreme_theta_decomposition
    k (by omega) (g.1.component 1) hJQ'
  obtain ⟨C, D, H₃, hZ⟩ := exists_extreme_theta_decomposition
    k (by omega) (g.1.component 2) hJZ'
  have hcomponentzero (i : Fin 3) : valueRingHom 2 (g.1.component i) = 0 := by
    rw [← PointedMapGerm.pullback_coordinate, PointedMapGerm.valueRingHom_pullback,
      valueRingHom_coordinate]
  have hA : A ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff,
      value_even_coefficient_of_extreme_theta_decomposition k (by omega) _ A B H₂ hQ]
    exact hcomponentzero 1
  have hC : C ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff,
      value_even_coefficient_of_extreme_theta_decomposition k (by omega) _ C D H₃ hZ]
    exact hcomponentzero 2
  have hB : IsUnit B := by
    apply isUnit_iff_valueRingHom_ne_zero.mpr
    have hf : PlaneCurve.HasFiniteIntersection (cyclicFirst k) (g.1.component 1) := by
      rwa [← hP]
    exact theta_coefficient_nonzero_of_intersection_lt_four_mul k hk _ A B H₂ hA hQ hf
      (by simpa only [hP] using hsmall)
  obtain ⟨v, hv⟩ := (hB.dvd : B ∣ D)
  let Binv : Germ 1 := ↑(hB.unit⁻¹)
  have hBinv : IsUnit Binv := (hB.unit⁻¹).isUnit
  have hBBinv : B * Binv = 1 := by
    change B * ↑(hB.unit⁻¹) = 1
    calc
      B * ↑(hB.unit⁻¹) = ↑hB.unit * ↑(hB.unit⁻¹) :=
        congrArg (fun b : Germ 1 => b * ↑(hB.unit⁻¹)) hB.unit_spec.symm
      _ = 1 := Units.mul_inv _
  let σ := cyclicScalarMap k (by omega : 1 ≤ k)
  have hscalar : g.firstCoordinateTriple = σ := by
    apply PointedMapGerm.ext_components
    intro i
    rw [PointedMapGerm.firstCoordinateTriple_component, hP, cyclicScalarMap_component]
    rfl
  obtain ⟨f, hgf, hf0, hf1, hf2⟩ :=
    g.exists_target_axis_triangular_normalization A C Binv v hA hC hBinv
  rw [hscalar] at hf1 hf2
  have hBpull : σ.pullbackRingHom B * σ.pullbackRingHom Binv = 1 := by
    rw [← map_mul, hBBinv, map_one]
  refine ⟨f, H₂ * σ.pullbackRingHom Binv, H₃ - H₂ * σ.pullbackRingHom v,
    hgf, hf0.trans hP, ?_, ?_, ?_⟩
  · rw [hf1, hQ]
    change ((σ.pullbackRingHom A + extremeTheta k * σ.pullbackRingHom B +
      coordinate 1 ^ (2 * k) * H₂) - σ.pullbackRingHom A) * σ.pullbackRingHom Binv = _
    linear_combination extremeTheta k * hBpull
  · rw [hf2, hZ, hQ, hv, map_mul]
    ring
  · obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
      (show A ∈ Ideal.span {coordinate (0 : Fin 1)} by
        rwa [← maximalIdeal_one_eq_span_coordinate])
    have hApull : σ.pullbackRingHom A = g.1.component 0 * σ.pullbackRingHom a := by
      rw [ha, map_mul, PointedMapGerm.pullback_coordinate, cyclicScalarMap_component, hP]
      rfl
    rw [hf0, hf1, hApull, PlaneCurve.pairIdeal_mul_right_of_isUnit _ _ _
      (hBinv.map σ.pullbackRingHom), PlaneCurve.pairIdeal_sub_mul_right]

/-- In particular, the extreme intersection `3k` supplies the prepared
map. The result is valid for every `k≥2`, including the required even case. -/
theorem exists_extreme_theta_preparation_of_intersection_three_mul
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (hP : g.1.component 0 = cyclicFirst k)
    (hJQ : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (g.1.component 0) (g.1.component 1))
    (hJZ : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (g.1.component 0) (g.1.component 2))
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hinter : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite = 3 * k) :
    ∃ f : PointedMapGerm 2 3, ∃ C₂ C₃ : Germ 2,
      g.RightLeftEquivalent f ∧ f.1.component 0 = cyclicFirst k ∧
      f.1.component 1 = extremeTheta k + coordinate 1 ^ (2 * k) * C₂ ∧
      f.1.component 2 = coordinate 1 ^ (2 * k) * C₃ ∧
      PlaneCurve.pairIdeal (f.1.component 0) (f.1.component 1) =
        PlaneCurve.pairIdeal (g.1.component 0) (g.1.component 1) :=
  exists_extreme_theta_preparation_of_intersection_lt_four_mul g k hk hP hJQ hJZ hfinite (by omega)

/-- The prepared first pair remains finite and retains its actual
intersection number, as required for filtered analytic elimination. -/
theorem exists_extreme_theta_preparation_with_finite_pair
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (hP : g.1.component 0 = cyclicFirst k)
    (hJQ : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (g.1.component 0) (g.1.component 1))
    (hJZ : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (g.1.component 0) (g.1.component 2))
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hinter : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite = 3 * k) :
    ∃ f : PointedMapGerm 2 3, ∃ C₂ C₃ : Germ 2,
      g.RightLeftEquivalent f ∧ f.1.component 0 = cyclicFirst k ∧
      f.1.component 1 = extremeTheta k + coordinate 1 ^ (2 * k) * C₂ ∧
      f.1.component 2 = coordinate 1 ^ (2 * k) * C₃ ∧ f.firstTwo.IsFiniteAtOrigin ∧
      ∃ hf : PlaneCurve.HasFiniteIntersection (f.1.component 0) (f.1.component 1),
        PlaneCurve.intersectionMultiplicity (f.1.component 0) (f.1.component 1) hf = 3 * k := by
  obtain ⟨f, C₂, C₃, hgf, hf0, hf1, hf2, hideal⟩ :=
    exists_extreme_theta_preparation_of_intersection_three_mul g k hk hP hJQ hJZ hfinite hinter
  have hf : PlaneCurve.HasFiniteIntersection (f.1.component 0) (f.1.component 1) := by
    rw [PlaneCurve.HasFiniteIntersection, hideal]
    exact hfinite
  have hfi : PlaneCurve.intersectionMultiplicity (f.1.component 0) (f.1.component 1) hf =
      3 * k := by
    change Module.finrank ℂ (Germ 2 ⧸ PlaneCurve.pairIdeal (f.1.component 0) (f.1.component 1)) = _
    rw [hideal]
    exact hinter
  have hpair0 : f.firstTwo.1.component 0 = f.1.component 0 := by
    rw [PointedMapGerm.firstTwo_component]
    rfl
  have hpair1 : f.firstTwo.1.component 1 = f.1.component 1 := by
    rw [PointedMapGerm.firstTwo_component]
    rfl
  have hfiniteMap : f.firstTwo.IsFiniteAtOrigin := by
    apply PointedMapGerm.finiteFiberCriterionAtOrigin_two 2
    change Module.Finite ℂ (Germ 2 ⧸ f.firstTwo.1.coordinateIdeal)
    rw [PlaneCurve.coordinateIdeal_eq_pairIdeal, hpair0, hpair1]
    exact hf
  exact ⟨f, C₂, C₃, hgf, hf0, hf1, hf2, hfiniteMap, hf, hfi⟩

end OnLeConjecture.DTwo
