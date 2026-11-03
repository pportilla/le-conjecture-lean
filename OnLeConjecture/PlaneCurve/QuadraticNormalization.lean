/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.ParametricMorse
public import OnLeConjecture.PlaneCurve.Morse

/-!
# Normalization of the one variable remainder in the quadratic normal form

This file lifts a one variable coordinate change to the second coordinate of
the plane. It transforms `x² + h(y)` into `x² + yᵏ` when the analytic germ
`h` is nonzero and vanishes at the origin.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- The linear map which exchanges the two plane coordinates. -/
@[expose] noncomputable def planeCoordinateSwapMap :
    Source 2 → Source 2 :=
  fun z ↦ ![z 1, z 0]

theorem planeCoordinateSwapMap_analyticAt :
    AnalyticAt ℂ planeCoordinateSwapMap 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0

@[simp]
theorem planeCoordinateSwapMap_zero : planeCoordinateSwapMap 0 = 0 := by
  ext i
  fin_cases i
  · rfl
  · rfl

@[simp]
theorem planeCoordinateSwapMap_involution (z : Source 2) :
    planeCoordinateSwapMap (planeCoordinateSwapMap z) = z := by
  ext i
  fin_cases i
  · rfl
  · rfl

/-- The pointed analytic equivalence which exchanges the two plane
coordinates. -/
@[expose] noncomputable def planeCoordinateSwapEquiv :
    PointedEquivGerm 2 := by
  let p : PointedMapGerm 2 2 :=
    PointedMapGerm.ofFunction planeCoordinateSwapMap
      planeCoordinateSwapMap_analyticAt planeCoordinateSwapMap_zero
  have hp : p.comp p = PointedMapGerm.identity 2 := by
    change (PointedMapGerm.ofFunction planeCoordinateSwapMap
      planeCoordinateSwapMap_analyticAt planeCoordinateSwapMap_zero).comp
        (PointedMapGerm.ofFunction planeCoordinateSwapMap
          planeCoordinateSwapMap_analyticAt planeCoordinateSwapMap_zero) = _
    rw [PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [] with z
    exact planeCoordinateSwapMap_involution z
  exact
    {
      forward := p
      inverse := p
      forward_inverse := hp
      inverse_forward := hp
    }

namespace Germ

@[simp]
theorem planeCoordinateSwapEquiv_pullback_zero :
    planeCoordinateSwapEquiv.pullbackAlgEquiv
        (Germ.coordinate (0 : Fin 2)) =
      Germ.coordinate (1 : Fin 2) := by
  rw [PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply,
    PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  change ((MapGerm.ofFunction planeCoordinateSwapMap
    planeCoordinateSwapMap_analyticAt).component (0 : Fin 2)).1 = _
  rw [MapGerm.component_ofFunction]
  rfl

@[simp]
theorem planeCoordinateSwapEquiv_pullback_one :
    planeCoordinateSwapEquiv.pullbackAlgEquiv
        (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (0 : Fin 2) := by
  rw [PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply,
    PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  change ((MapGerm.ofFunction planeCoordinateSwapMap
    planeCoordinateSwapMap_analyticAt).component (1 : Fin 2)).1 = _
  rw [MapGerm.component_ofFunction]
  rfl

/-- Pullback by the coordinate swap is an involution. -/
theorem planeCoordinateSwapEquiv_pullback_involution (q : Germ 2) :
    planeCoordinateSwapEquiv.pullbackAlgEquiv
        (planeCoordinateSwapEquiv.pullbackAlgEquiv q) = q := by
  have h := planeCoordinateSwapEquiv.pullbackRingEquiv.left_inv q
  exact h

end Germ

end OnLeConjecture.Analytic

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- A plane germ regular in the second coordinate can be made that
coordinate by an analytic equivalence which fixes the first coordinate. -/
theorem exists_equiv_pullback_coordinate_one_eq_preserving_zero
    (q : Germ 2) (hq : q ∈ Germ.maximalIdeal 2)
    (hregular : Germ.valueRingHom 2
      (Germ.partialDerivative (1 : Fin 2) q) ≠ 0) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv (Germ.coordinate (1 : Fin 2)) = q ∧
        e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2)) =
          Germ.coordinate (0 : Fin 2) := by
  let swap := planeCoordinateSwapEquiv
  let qswap : Germ 2 := swap.pullbackAlgEquiv q
  have hqswapMaximal : qswap ∈ Germ.maximalIdeal 2 := by
    exact swap.forward.pullback_mem_maximalIdeal hq
  have hqswapDerivative : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2) qswap) ≠ 0 := by
    have hswapZero : swap.forward.1.component (0 : Fin 2) =
        Germ.coordinate (1 : Fin 2) := by
      calc
        swap.forward.1.component (0 : Fin 2) =
            swap.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2)) :=
          (swap.forward.pullback_coordinate (0 : Fin 2)).symm
        _ = Germ.coordinate (1 : Fin 2) :=
          Germ.planeCoordinateSwapEquiv_pullback_zero
    have hswapOne : swap.forward.1.component (1 : Fin 2) =
        Germ.coordinate (0 : Fin 2) := by
      calc
        swap.forward.1.component (1 : Fin 2) =
            swap.pullbackAlgEquiv (Germ.coordinate (1 : Fin 2)) :=
          (swap.forward.pullback_coordinate (1 : Fin 2)).symm
        _ = Germ.coordinate (0 : Fin 2) :=
          Germ.planeCoordinateSwapEquiv_pullback_one
    change Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2)
        (Germ.compPointed q swap.forward)) ≠ 0
    rw [Germ.partialDerivative_compPointed,
      hswapZero, hswapOne,
      Germ.partialDerivative_coordinate_ne (by decide),
      Germ.partialDerivative_coordinate_same]
    simp only [mul_zero, mul_one, zero_add]
    change Germ.valueRingHom 2 (swap.forward.pullbackRingHom
      (Germ.partialDerivative (1 : Fin 2) q)) ≠ 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact hregular
  have hqswapRegular : Germ.differential qswap
      (Germ.firstCoordinateVector 1) ≠ 0 := by
    change Germ.differential qswap
      (Germ.coordinateVector (0 : Fin 2)) ≠ 0
    rw [← Germ.valueRingHom_partialDerivative]
    exact hqswapDerivative
  obtain ⟨c, hcZero, hcExtension⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      qswap hqswapMaximal hqswapRegular
  have hparameterCoordinate :
      Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1)) =
        Germ.coordinate (1 : Fin 2) := by
    have hi : (0 : Fin 1).succ = (1 : Fin 2) := by decide
    simpa only [hi] using
      Germ.hyperplaneExtension_coordinate (n := 1) (0 : Fin 1)
  have hcOne : c.pullbackAlgEquiv (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (1 : Fin 2) := by
    rw [← hparameterCoordinate, hcExtension]
  let e : PointedEquivGerm 2 := (swap.comp c).comp swap
  refine ⟨e, ?_, ?_⟩
  · change ((swap.comp c).comp swap).pullbackAlgEquiv
      (Germ.coordinate (1 : Fin 2)) = q
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply,
      PointedEquivGerm.pullbackAlgEquiv_comp_apply,
      Germ.planeCoordinateSwapEquiv_pullback_one, hcZero]
    exact Germ.planeCoordinateSwapEquiv_pullback_involution q
  · change ((swap.comp c).comp swap).pullbackAlgEquiv
      (Germ.coordinate (0 : Fin 2)) = Germ.coordinate (0 : Fin 2)
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply,
      PointedEquivGerm.pullbackAlgEquiv_comp_apply,
      Germ.planeCoordinateSwapEquiv_pullback_zero, hcOne,
      Germ.planeCoordinateSwapEquiv_pullback_one]

/-- A nonzero one variable remainder which vanishes at the origin can be
changed into a pure power without changing the first plane coordinate. -/
theorem exists_quadratic_remainder_power_normalization
    (h : Germ 1) (hne : h ≠ 0) (hmaximal : h ∈ Germ.maximalIdeal 1) :
    ∃ k : ℕ, 0 < k ∧ Germ.vanishingOrder h = k ∧
      ∃ e : PointedEquivGerm 2,
        e.pullbackAlgEquiv
            (Germ.coordinate (0 : Fin 2) ^ 2 +
              Germ.hyperplaneExtension 1 h) =
          Germ.coordinate (0 : Fin 2) ^ 2 +
            Germ.coordinate (1 : Fin 2) ^ k ∧
        e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2)) =
          Germ.coordinate (0 : Fin 2) ∧
        e.inverse.1.component (1 : Fin 2) ^ k =
          Germ.hyperplaneExtension 1 h := by
  obtain ⟨k, hk, v, hv, hh⟩ :=
    Germ.exists_eq_coordinate_mul_unit_pow_of_mem_maximalIdeal
      hne hmaximal
  have hvpowUnit : IsUnit (v ^ k) := hv.pow k
  have hhFactor : h = Germ.coordinate (0 : Fin 1) ^ k * v ^ k := by
    rw [hh, mul_pow]
  have horder : Germ.vanishingOrder h = k :=
    Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit
      hvpowUnit hhFactor
  let parameterUnit : Germ 2 := Germ.hyperplaneExtension 1 v
  have hparameterUnit : IsUnit parameterUnit :=
    hv.map (Germ.hyperplaneExtension 1)
  let parameter : Germ 2 :=
    Germ.coordinate (1 : Fin 2) * parameterUnit
  have hparameterMaximal : parameter ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp [parameter]
  have hparameterDerivative : Germ.valueRingHom 2
      (Germ.partialDerivative (1 : Fin 2) parameter) ≠ 0 := by
    have hunitValue : Germ.valueRingHom 2 parameterUnit ≠ 0 :=
      Germ.valueRingHom_ne_zero_of_isUnit hparameterUnit
    change Germ.valueRingHom 2
      (Germ.partialDerivative (1 : Fin 2)
        (Germ.coordinate (1 : Fin 2) * parameterUnit)) ≠ 0
    rw [Germ.partialDerivative_mul,
      Germ.partialDerivative_coordinate_same]
    simpa using hunitValue
  obtain ⟨c, hcParameter, hcZero⟩ :=
    exists_equiv_pullback_coordinate_one_eq_preserving_zero
      parameter hparameterMaximal hparameterDerivative
  have hparameterCoordinate :
      Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1)) =
        Germ.coordinate (1 : Fin 2) := by
    have hi : (0 : Fin 1).succ = (1 : Fin 2) := by decide
    simpa only [hi] using
      Germ.hyperplaneExtension_coordinate (n := 1) (0 : Fin 1)
  have hparameterPower : parameter ^ k =
      Germ.hyperplaneExtension 1 h := by
    rw [hh, map_pow, map_mul, hparameterCoordinate]
  have hcNormal : c.pullbackAlgEquiv
      (Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.hyperplaneExtension 1 h := by
    rw [map_add, map_pow, map_pow, hcZero, hcParameter,
      hparameterPower]
  let e : PointedEquivGerm 2 := c.symm
  have heNormal : e.pullbackAlgEquiv
      (Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.hyperplaneExtension 1 h) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k := by
    have hinverse := congrArg c.pullbackAlgEquiv.symm hcNormal
    rw [c.pullbackAlgEquiv.symm_apply_apply] at hinverse
    exact hinverse.symm
  have heZero : e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2)) =
      Germ.coordinate (0 : Fin 2) := by
    have hinverse := c.pullbackRingEquiv.left_inv
      (Germ.coordinate (0 : Fin 2))
    change c.inverse.pullbackRingHom
        (c.forward.pullbackRingHom (Germ.coordinate (0 : Fin 2))) =
      Germ.coordinate (0 : Fin 2) at hinverse
    have hcZero' : c.forward.pullbackRingHom
        (Germ.coordinate (0 : Fin 2)) =
      Germ.coordinate (0 : Fin 2) := hcZero
    rw [hcZero'] at hinverse
    exact hinverse
  have heInverseParameter : e.inverse.1.component (1 : Fin 2) ^ k =
      Germ.hyperplaneExtension 1 h := by
    change c.forward.1.component (1 : Fin 2) ^ k = _
    have hcParameter' : c.forward.1.component (1 : Fin 2) = parameter := by
      calc
        c.forward.1.component (1 : Fin 2) =
            c.pullbackAlgEquiv (Germ.coordinate (1 : Fin 2)) :=
          (c.forward.pullback_coordinate (1 : Fin 2)).symm
        _ = parameter := hcParameter
    rw [hcParameter', hparameterPower]
  exact ⟨k, hk, horder, e, heNormal, heZero, heInverseParameter⟩

/-- The preceding normalization for a prescribed finite vanishing order. -/
theorem exists_quadratic_remainder_power_normalization_of_order
    (h : Germ 1) (k : ℕ) (hne : h ≠ 0)
    (hmaximal : h ∈ Germ.maximalIdeal 1)
    (horder : Germ.vanishingOrder h = k) :
    0 < k ∧ ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin 2) ^ 2 +
            Germ.hyperplaneExtension 1 h) =
        Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k ∧
      e.pullbackAlgEquiv (Germ.coordinate (0 : Fin 2)) =
        Germ.coordinate (0 : Fin 2) := by
  obtain ⟨l, hl, hlOrder, e, heNormal, heZero, _⟩ :=
    exists_quadratic_remainder_power_normalization h hne hmaximal
  have hlk : l = k := by
    exact ENat.natCast_inj.mp (hlOrder.symm.trans horder)
  subst l
  exact ⟨hl, e, heNormal, heZero⟩

/-- The differential of `x² + yᵏ` can vanish only when `k` is at least
two. -/
theorem two_le_of_morseCurve_differential_eq_zero
    (k : ℕ) (hk : 0 < k)
    (hzero : Germ.differential (morseCurve k) = 0) :
    2 ≤ k := by
  have hy :=
    (Germ.differential_eq_zero_iff_partialDerivatives_vanish
      (morseCurve k)).mp hzero (1 : Fin 2)
  rw [partialDerivative_one_morseCurve] at hy
  by_contra hnot
  have hkOne : k = 1 := by omega
  subst k
  norm_num at hy

/-- A witnessed parametric Morse form with nonzero remainder can be changed
to `x² + yᵏ`. The exponent is the vanishing order of the remainder. -/
theorem exists_quadratic_power_normalization
    (g : Germ 2) (source : PointedEquivGerm 2) (h : Germ 1)
    (hnormal : source.pullbackAlgEquiv g =
      Germ.coordinate (0 : Fin 2) ^ 2 + Germ.hyperplaneExtension 1 h)
    (hne : h ≠ 0) (hmaximal : h ∈ Germ.maximalIdeal 1) :
    ∃ k : ℕ, 0 < k ∧ Germ.vanishingOrder h = k ∧
      ∃ e : PointedEquivGerm 2,
        e.pullbackAlgEquiv g = morseCurve k := by
  obtain ⟨k, hk, horder, remainderSource, hremainder, _, _⟩ :=
    exists_quadratic_remainder_power_normalization h hne hmaximal
  let e : PointedEquivGerm 2 := source.comp remainderSource
  refine ⟨k, hk, horder, e, ?_⟩
  change (source.comp remainderSource).pullbackAlgEquiv g = morseCurve k
  rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply, hnormal, hremainder]
  rfl

/-- If the original germ has zero differential, the exponent in the pure
power normalization is at least two. -/
theorem exists_quadratic_power_normalization_of_differential_eq_zero
    (g : Germ 2) (source : PointedEquivGerm 2) (h : Germ 1)
    (hnormal : source.pullbackAlgEquiv g =
      Germ.coordinate (0 : Fin 2) ^ 2 + Germ.hyperplaneExtension 1 h)
    (hne : h ≠ 0) (hmaximal : h ∈ Germ.maximalIdeal 1)
    (hdifferential : Germ.differential g = 0) :
    ∃ k : ℕ, 2 ≤ k ∧ Germ.vanishingOrder h = k ∧
      ∃ e : PointedEquivGerm 2,
        e.pullbackAlgEquiv g = morseCurve k := by
  obtain ⟨k, hk, horder, e, he⟩ :=
    exists_quadratic_power_normalization
      g source h hnormal hne hmaximal
  have hpullbackDifferential :
      Germ.differential (e.pullbackAlgEquiv g) = 0 := by
    change Germ.differential (Germ.compPointed g e.forward) = 0
    rw [Germ.differential_compPointed, hdifferential]
    rfl
  have hmorseDifferential : Germ.differential (morseCurve k) = 0 := by
    rw [← he]
    exact hpullbackDifferential
  exact ⟨k, two_le_of_morseCurve_differential_eq_zero
    k hk hmorseDifferential, horder, e, he⟩

/-- A witnessed parametric Morse form whose remainder has prescribed order
`k` is analytically equivalent to `x² + yᵏ`. -/
theorem exists_witnessed_quadratic_power_normalization_of_order
    (g : Germ 2) (source : PointedEquivGerm 2) (h : Germ 1) (k : ℕ)
    (hnormal : source.pullbackAlgEquiv g =
      Germ.coordinate (0 : Fin 2) ^ 2 + Germ.hyperplaneExtension 1 h)
    (hne : h ≠ 0) (hmaximal : h ∈ Germ.maximalIdeal 1)
    (horder : Germ.vanishingOrder h = k) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv g = morseCurve k := by
  obtain ⟨l, _, hlOrder, e, he⟩ :=
    exists_quadratic_power_normalization
      g source h hnormal hne hmaximal
  have hlk : l = k :=
    ENat.natCast_inj.mp (hlOrder.symm.trans horder)
  subst l
  exact ⟨e, he⟩

/-- Under the zero differential hypothesis, the prescribed exponent in the
quadratic normal form is at least two. -/
theorem two_le_and_exists_witnessed_quadratic_power_normalization_of_order
    (g : Germ 2) (source : PointedEquivGerm 2) (h : Germ 1) (k : ℕ)
    (hnormal : source.pullbackAlgEquiv g =
      Germ.coordinate (0 : Fin 2) ^ 2 + Germ.hyperplaneExtension 1 h)
    (hne : h ≠ 0) (hmaximal : h ∈ Germ.maximalIdeal 1)
    (horder : Germ.vanishingOrder h = k)
    (hdifferential : Germ.differential g = 0) :
    2 ≤ k ∧ ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv g = morseCurve k := by
  obtain ⟨l, hl, hlOrder, e, he⟩ :=
    exists_quadratic_power_normalization_of_differential_eq_zero
      g source h hnormal hne hmaximal hdifferential
  have hlk : l = k :=
    ENat.natCast_inj.mp (hlOrder.symm.trans horder)
  subst l
  exact ⟨hl, e, he⟩

end OnLeConjecture.PlaneCurve
