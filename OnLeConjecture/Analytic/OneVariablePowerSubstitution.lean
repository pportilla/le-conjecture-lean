/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.Pullback

/-!
# Power substitutions in one variable

Pullback by `t ↦ tʳ` multiplies the vanishing order of a one variable
analytic germ by the positive integer `r`.
-/

public section

namespace OnLeConjecture.Analytic

open Filter

namespace Germ

/-- The analytic map `t ↦ tʳ` on the one dimensional source. -/
@[expose] noncomputable def oneVariablePowerMap
    (r : ℕ) (z : Source 1) : Source 1 :=
  fun _ ↦ z 0 ^ r

@[simp]
theorem oneVariablePowerMap_apply
    (r : ℕ) (z : Source 1) (i : Fin 1) :
    Germ.oneVariablePowerMap r z i = z 0 ^ r :=
  rfl

theorem oneVariablePowerMap_analyticAt (r : ℕ) :
    AnalyticAt ℂ (Germ.oneVariablePowerMap r) 0 := by
  apply AnalyticAt.pi
  intro i
  change AnalyticAt ℂ (fun z : Source 1 ↦ z 0 ^ r) 0
  exact ((ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0).pow r

theorem oneVariablePowerMap_zero {r : ℕ} (hr : 1 ≤ r) :
    Germ.oneVariablePowerMap r (0 : Source 1) = 0 := by
  ext i
  simp [Germ.oneVariablePowerMap, zero_pow (by omega : r ≠ 0)]

/-- The pointed analytic germ represented by `t ↦ tʳ`. -/
@[expose] noncomputable def oneVariablePowerMapGerm
    (r : ℕ) (hr : 1 ≤ r) : PointedMapGerm 1 1 :=
  PointedMapGerm.ofFunction (Germ.oneVariablePowerMap r)
    (Germ.oneVariablePowerMap_analyticAt r)
    (Germ.oneVariablePowerMap_zero hr)

@[simp]
theorem oneVariablePowerMapGerm_pullback_coordinate
    (r : ℕ) (hr : 1 ≤ r) :
    (Germ.oneVariablePowerMapGerm r hr).pullbackRingHom
        (Germ.coordinate (0 : Fin 1)) =
      Germ.coordinate (0 : Fin 1) ^ r := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [Germ.oneVariablePowerMapGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

/-- A positive power substitution multiplies vanishing order by its
exponent. -/
theorem vanishingOrder_oneVariablePowerMapGerm_pullback
    (r : ℕ) (hr : 1 ≤ r) (q : Germ 1) :
    Germ.vanishingOrder
        ((Germ.oneVariablePowerMapGerm r hr).pullbackRingHom q) =
      r • Germ.vanishingOrder q := by
  by_cases hq : q = 0
  · subst q
    rw [map_zero, Germ.vanishingOrder_zero]
    simp [show r ≠ 0 by omega]
  · obtain ⟨n, u, hu, hfactor⟩ :=
      Germ.exists_eq_coordinate_pow_mul_unit hq
    have huPull : IsUnit
        ((Germ.oneVariablePowerMapGerm r hr).pullbackRingHom u) :=
      hu.map (Germ.oneVariablePowerMapGerm r hr).pullbackRingHom
    have hqOrder : Germ.vanishingOrder q = n :=
      Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
    conv_lhs => rw [hfactor]
    rw [map_mul, map_pow,
      Germ.oneVariablePowerMapGerm_pullback_coordinate,
      Germ.vanishingOrder_mul, Germ.vanishingOrder_pow,
      Germ.vanishingOrder_coordinate_pow,
      Germ.vanishingOrder_eq_zero_iff_isUnit.mpr huPull, hqOrder]
    simp [nsmul_eq_mul, mul_comm]

/-- A positive power substitution is injective on one variable analytic
germs. -/
theorem oneVariablePowerMapGerm_pullback_injective
    (r : ℕ) (hr : 1 ≤ r) :
    Function.Injective
      (Germ.oneVariablePowerMapGerm r hr).pullbackRingHom := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra hqNe
  obtain ⟨n, u, hu, hfactor⟩ :=
    Germ.exists_eq_coordinate_pow_mul_unit hqNe
  have huPull : IsUnit
      ((Germ.oneVariablePowerMapGerm r hr).pullbackRingHom u) :=
    hu.map (Germ.oneVariablePowerMapGerm r hr).pullbackRingHom
  rw [hfactor, map_mul, map_pow,
    Germ.oneVariablePowerMapGerm_pullback_coordinate] at hq
  exact (mul_ne_zero
    (pow_ne_zero n (pow_ne_zero r Germ.coordinate_zero_ne_zero))
    huPull.ne_zero) hq

end Germ

end OnLeConjecture.Analytic
