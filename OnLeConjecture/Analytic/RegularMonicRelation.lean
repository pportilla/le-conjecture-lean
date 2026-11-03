/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricUnitPreparation

/-!
# Monic relations for regular analytic germs

A plane germ that is regular in the first coordinate may be multiplied by
the inverse of its leading analytic quotient. The resulting germ has an
exact monic first coordinate axis. Parameter dependent preparation then
produces a monic relation whose coefficients depend analytically on the
second source coordinate and on the value of the original germ.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- A plane germ regular in order `d + 1` satisfies a monic relation in its
first coordinate whose coefficients depend analytically on the second
coordinate and on the value of the germ. -/
theorem exists_analytic_monicRelation_at_regularGermValue
    {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f (d + 1)) :
    ∃ F : Source 2 → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      f = Germ.ofFunction F hF ∧
      ∃ b : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
        AnalyticAt ℂ b (0, 0) ∧
        b (0, 0) = 0 ∧
        ∀ᶠ z : Source 2 in nhds 0,
          Germ.generalDivisionPolynomialValue (z 0)
            (b (z 1, F z)) = 0 := by
  let u : Germ 2 := Germ.firstCoordinateTailIterate (d + 1) f
  have hu : IsUnit u :=
    Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
  let s : Germ 2 := (↑(hu.unit⁻¹) : Germ 2)
  have hus : u * s = 1 := by
    calc
      u * s = (↑hu.unit : Germ 2) * (↑(hu.unit⁻¹) : Germ 2) := by
        rw [hu.unit_spec]
      _ = 1 := Units.mul_inv hu.unit
  let g : Germ 2 := f * s
  have hlineF : Germ.lineRestriction
      (Germ.firstCoordinateVector 1) f =
        Germ.coordinate (0 : Fin 1) ^ (d + 1) *
          Germ.lineRestriction (Germ.firstCoordinateVector 1) u := by
    simpa only [u] using
      Germ.lineRestriction_eq_pow_mul_tailIterate_of_regular_allOrders
        hregular
  have hlineG : Germ.lineRestriction
      (Germ.firstCoordinateVector 1) g =
        Germ.coordinate (0 : Fin 1) ^ (d + 1) := by
    change Germ.lineRestriction (Germ.firstCoordinateVector 1) (f * s) = _
    change (Germ.lineRestrictionAlgHom
        (Germ.firstCoordinateVector 1)) (f * s) = _
    rw [map_mul, Germ.lineRestrictionAlgHom_apply,
      Germ.lineRestrictionAlgHom_apply, hlineF, mul_assoc,
      ← map_mul, hus, map_one, mul_one]
  obtain ⟨F, hF, hfRepresentative⟩ :=
    Germ.exists_analyticRepresentative_allOrders f
  obtain ⟨G, hG, hgRepresentative⟩ :=
    Germ.exists_analyticRepresentative_allOrders g
  obtain ⟨V, hV, hsRepresentative⟩ :=
    Germ.exists_analyticRepresentative_allOrders s
  rcases hG with ⟨p, hp⟩
  rcases hV with ⟨v, hv⟩
  have hlineRepresentative : Germ.lineRestriction
      (Germ.firstCoordinateVector 1)
        (Germ.ofFunction G hp.analyticAt) =
      Germ.coordinate (0 : Fin 1) ^ (d + 1) := by
    rw [← hgRepresentative]
    exact hlineG
  have haxisTaylor : Germ.firstCoordinateAxisTaylorSeries
      (Germ.ofFunction G hp.analyticAt) =
        (PowerSeries.X : PowerSeries ℂ) ^ (d + 1) := by
    rw [Germ.firstCoordinateAxisTaylorSeries,
      hlineRepresentative]
    change Germ.oneVariableTaylorRingHom
        (Germ.coordinate (0 : Fin 1) ^ (d + 1)) = _
    rw [map_pow, Germ.oneVariableTaylorRingHom_apply,
      Germ.oneVariableTaylorSeries_coordinate]
  have haxis : ∀ n,
      Germ.mixedCoefficient p n n =
        if n = d + 1 then 1 else 0 := by
    intro n
    rw [Germ.mixedCoefficient_self_eq_value_firstCoordinateTaylorCoefficient
      hp n]
    rw [← Germ.firstCoordinateAxisTaylorSeries_coeff,
      haxisTaylor]
    simp [PowerSeries.coeff_X_pow]
  have hfValue : Germ.valueRingHom 2 f = 0 := by
    have hzero :=
      (Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).2
        0 (Nat.succ_pos d)
    rw [Germ.value_firstCoordinateTaylorCoefficient] at hzero
    simpa using hzero
  have hFZero : F 0 = 0 := by
    calc
      F 0 = Germ.valueRingHom 2 (Germ.ofFunction F hF) := by
        rw [Germ.valueRingHom_ofFunction]
      _ = Germ.valueRingHom 2 f := by rw [← hfRepresentative]
      _ = 0 := hfValue
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
  have hvSum : HasFPowerSeriesAt v.sum v 0 :=
    (v.hasFPowerSeriesOnBall hv.radius_pos).hasFPowerSeriesAt
  have hGSum : G =ᶠ[nhds 0] p.sum := by
    filter_upwards [hp.eventually_hasSum_sub,
      hpSum.eventually_hasSum_sub] with z hzG hzSum
    simpa only [sub_zero] using hzG.unique hzSum
  have hVSum : V =ᶠ[nhds 0] v.sum := by
    filter_upwards [hv.eventually_hasSum_sub,
      hvSum.eventually_hasSum_sub] with z hzV hzSum
    simpa only [sub_zero] using hzV.unique hzSum
  have hGermFactor : Germ.ofFunction G hp.analyticAt =
      Germ.ofFunction F hF * Germ.ofFunction V hv.analyticAt := by
    calc
      Germ.ofFunction G hp.analyticAt = g := hgRepresentative.symm
      _ = f * s := rfl
      _ = Germ.ofFunction F hF * Germ.ofFunction V hv.analyticAt := by
        rw [hfRepresentative, hsRepresentative]
  have hGFactor : G =ᶠ[nhds 0] fun z ↦ F z * V z := by
    apply Filter.Germ.coe_eq.mp
    calc
      (G : FunctionGerm 2) =
          ((Germ.ofFunction G hp.analyticAt : Germ 2) :
            FunctionGerm 2) := rfl
      _ = ((Germ.ofFunction F hF *
            Germ.ofFunction V hv.analyticAt : Germ 2) :
            FunctionGerm 2) := congrArg Subtype.val hGermFactor
      _ = ((Germ.ofFunction F hF : Germ 2) : FunctionGerm 2) *
          ((Germ.ofFunction V hv.analyticAt : Germ 2) :
            FunctionGerm 2) :=
        (analyticGermSubring 2).subtype.map_mul
          (Germ.ofFunction F hF)
          (Germ.ofFunction V hv.analyticAt)
      _ = (F : FunctionGerm 2) * (V : FunctionGerm 2) := by
        rw [Germ.coe_ofFunction, Germ.coe_ofFunction]
      _ = (((fun z : Source 2 ↦ F z * V z) : Source 2 → ℂ) :
          FunctionGerm 2) :=
        (Filter.Germ.coe_mul (l := nhds (0 : Source 2)) F V).symm
  have hfactor : ∀ᶠ z : Source 2 in nhds 0,
      p.sum z = F z * v.sum z := by
    filter_upwards [hGSum, hVSum, hGFactor] with z hGz hVz hfactorz
    calc
      p.sum z = G z := hGz.symm
      _ = F z * V z := hfactorz
      _ = F z * v.sum z := by rw [hVz]
  obtain ⟨b, hb, hbZero, hrelation⟩ :=
    Germ.exists_analytic_monicRelation_at_multiplierValue
      F p v d hp.radius_pos hv.radius_pos haxis hF hFZero hfactor
  exact ⟨F, hF, hfRepresentative, b, hb, hbZero, hrelation⟩

end Germ

end OnLeConjecture.Analytic
