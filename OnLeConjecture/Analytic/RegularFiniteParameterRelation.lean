/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteParameterPreparation

/-!
# Monic relations from regular finite parameter expansions

A finite parameter expansion whose constant coefficient is regular may be
multiplied by the inverse of its leading analytic quotient. The normalized
finite expansion then satisfies the preparation theorem with arbitrary
finite dimensional auxiliary parameters.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped BigOperators Topology

namespace Germ

variable {P ι : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
variable [Fintype ι] [DecidableEq ι]

/-- A finite expansion with a regular distinguished coefficient gives a
monic relation after every analytic substitution on which it vanishes. -/
theorem exists_analytic_monicRelation_of_regularFiniteExpansion
    (F : ι → Source 2 → ℂ) (hF : ∀ i, AnalyticAt ℂ (F i) 0)
    (d : ℕ) (i₀ : ι)
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder
      (Germ.ofFunction (F i₀) (hF i₀)) (d + 1))
    (coeff : P → ι → ℂ)
    (hcoeff : AnalyticAt ℂ coeff 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0)
    (x y : Source 2 → ℂ) (parameter : Source 2 → P)
    (hx : AnalyticAt ℂ x 0) (hy : AnalyticAt ℂ y 0)
    (hparameter : AnalyticAt ℂ parameter 0)
    (hxZero : x 0 = 0) (hyZero : y 0 = 0)
    (hparameterZero : parameter 0 = 0)
    (hvanish : ∀ᶠ z : Source 2 in nhds 0,
      ∑ i, coeff (parameter z) i *
        F i (Germ.planePoint (x z) (y z)) = 0) :
    ∃ b : ℂ × P → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (x z)
          (b (y z, parameter z)) = 0 := by
  let f : Germ 2 := Germ.ofFunction (F i₀) (hF i₀)
  let u : Germ 2 := Germ.firstCoordinateTailIterate (d + 1) f
  have hu : IsUnit u :=
    Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
  let s : Germ 2 := (↑(hu.unit⁻¹) : Germ 2)
  have hus : u * s = 1 := by
    calc
      u * s = (↑hu.unit : Germ 2) * (↑(hu.unit⁻¹) : Germ 2) := by
        rw [hu.unit_spec]
      _ = 1 := Units.mul_inv hu.unit
  let g : ι → Germ 2 := fun i ↦ Germ.ofFunction (F i) (hF i) * s
  have hlineF : Germ.lineRestriction
      (Germ.firstCoordinateVector 1) f =
        Germ.coordinate (0 : Fin 1) ^ (d + 1) *
          Germ.lineRestriction (Germ.firstCoordinateVector 1) u := by
    simpa only [u] using
      Germ.lineRestriction_eq_pow_mul_tailIterate_of_regular_allOrders
        hregular
  have hlineG : Germ.lineRestriction
      (Germ.firstCoordinateVector 1) (g i₀) =
        Germ.coordinate (0 : Fin 1) ^ (d + 1) := by
    change Germ.lineRestriction (Germ.firstCoordinateVector 1)
      (Germ.ofFunction (F i₀) (hF i₀) * s) = _
    change (Germ.lineRestrictionAlgHom
        (Germ.firstCoordinateVector 1))
      (Germ.ofFunction (F i₀) (hF i₀) * s) = _
    rw [map_mul, Germ.lineRestrictionAlgHom_apply,
      Germ.lineRestrictionAlgHom_apply]
    change Germ.lineRestriction (Germ.firstCoordinateVector 1) f *
      Germ.lineRestriction (Germ.firstCoordinateVector 1) s = _
    rw [hlineF, mul_assoc, ← map_mul, hus, map_one, mul_one]
  choose G hG hgRepresentative using fun i ↦
    Germ.exists_analyticRepresentative_allOrders (g i)
  choose p hp using fun i ↦ hG i
  obtain ⟨V, hV, hsRepresentative⟩ :=
    Germ.exists_analyticRepresentative_allOrders s
  have hlineRepresentative : Germ.lineRestriction
      (Germ.firstCoordinateVector 1)
        (Germ.ofFunction (G i₀) (hp i₀).analyticAt) =
      Germ.coordinate (0 : Fin 1) ^ (d + 1) := by
    have hrepresentative : g i₀ =
        Germ.ofFunction (G i₀) (hp i₀).analyticAt := by
      simpa only using hgRepresentative i₀
    rw [← hrepresentative]
    exact hlineG
  have haxisTaylor : Germ.firstCoordinateAxisTaylorSeries
      (Germ.ofFunction (G i₀) (hp i₀).analyticAt) =
        (PowerSeries.X : PowerSeries ℂ) ^ (d + 1) := by
    rw [Germ.firstCoordinateAxisTaylorSeries,
      hlineRepresentative]
    change Germ.oneVariableTaylorRingHom
        (Germ.coordinate (0 : Fin 1) ^ (d + 1)) = _
    rw [map_pow, Germ.oneVariableTaylorRingHom_apply,
      Germ.oneVariableTaylorSeries_coordinate]
  have haxis : ∀ n,
      Germ.mixedCoefficient (p i₀) n n =
        if n = d + 1 then 1 else 0 := by
    intro n
    rw [Germ.mixedCoefficient_self_eq_value_firstCoordinateTaylorCoefficient
      (hp i₀) n]
    rw [← Germ.firstCoordinateAxisTaylorSeries_coeff,
      haxisTaylor]
    simp [PowerSeries.coeff_X_pow]
  have hpRadius (i : ι) : 0 < (p i).radius := (hp i).radius_pos
  have hpSum (i : ι) : HasFPowerSeriesAt (p i).sum (p i) 0 :=
    ((p i).hasFPowerSeriesOnBall (hp i).radius_pos).hasFPowerSeriesAt
  have hGSum (i : ι) : G i =ᶠ[nhds 0] (p i).sum := by
    filter_upwards [(hp i).eventually_hasSum_sub,
      (hpSum i).eventually_hasSum_sub] with z hzG hzSum
    simpa only [sub_zero] using hzG.unique hzSum
  have hGermFactor (i : ι) :
      Germ.ofFunction (G i) (hp i).analyticAt =
        Germ.ofFunction (F i) (hF i) * Germ.ofFunction V hV := by
    calc
      Germ.ofFunction (G i) (hp i).analyticAt = g i := by
        have hi := hgRepresentative i
        simpa only using hi.symm
      _ = Germ.ofFunction (F i) (hF i) * s := rfl
      _ = Germ.ofFunction (F i) (hF i) * Germ.ofFunction V hV := by
        rw [← hsRepresentative]
  have hGFactor (i : ι) : G i =ᶠ[nhds 0] fun w ↦ F i w * V w := by
    apply Filter.Germ.coe_eq.mp
    calc
      (G i : FunctionGerm 2) =
          ((Germ.ofFunction (G i) (hp i).analyticAt : Germ 2) :
            FunctionGerm 2) := rfl
      _ = ((Germ.ofFunction (F i) (hF i) *
            Germ.ofFunction V hV : Germ 2) : FunctionGerm 2) :=
        congrArg Subtype.val (hGermFactor i)
      _ = ((Germ.ofFunction (F i) (hF i) : Germ 2) : FunctionGerm 2) *
          ((Germ.ofFunction V hV : Germ 2) : FunctionGerm 2) :=
        (analyticGermSubring 2).subtype.map_mul
          (Germ.ofFunction (F i) (hF i)) (Germ.ofFunction V hV)
      _ = (F i : FunctionGerm 2) * (V : FunctionGerm 2) := by
        rw [Germ.coe_ofFunction, Germ.coe_ofFunction]
      _ = (((fun w : Source 2 ↦ F i w * V w) : Source 2 → ℂ) :
          FunctionGerm 2) :=
        (Filter.Germ.coe_mul (l := nhds (0 : Source 2)) (F i) V).symm
  have hpFactor (i : ι) : ∀ᶠ w : Source 2 in nhds 0,
      (p i).sum w = F i w * V w := by
    filter_upwards [hGSum i, hGFactor i] with w hsum hfactor
    rw [← hsum]
    exact hfactor
  let planeSubstitution : Source 2 → Source 2 := fun z ↦
    Germ.planePoint (x z) (y z)
  have hplaneSubstitution : AnalyticAt ℂ planeSubstitution 0 := by
    have hpair : AnalyticAt ℂ (fun z ↦ (x z, y z)) 0 := hx.prod hy
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt
          (x 0, y 0)) hpair)
  have hplaneSubstitutionZero : planeSubstitution 0 = 0 := by
    simp [planeSubstitution, hxZero, hyZero, Germ.planePoint]
  have hpFactorPulled : ∀ᶠ z : Source 2 in nhds 0, ∀ i,
      (p i).sum (planeSubstitution z) =
        F i (planeSubstitution z) * V (planeSubstitution z) := by
    apply Filter.eventually_all.mpr
    intro i
    exact hplaneSubstitution.continuousAt.eventually (by
      simpa only [hplaneSubstitutionZero] using hpFactor i)
  have hnormalizedVanish : ∀ᶠ z : Source 2 in nhds 0,
      ∑ i, coeff (parameter z) i *
        (p i).sum (Germ.planePoint (x z) (y z)) = 0 := by
    filter_upwards [hpFactorPulled, hvanish] with z hfactor hz
    change ∑ i, coeff (parameter z) i *
      (p i).sum (planeSubstitution z) = 0
    calc
      ∑ i, coeff (parameter z) i * (p i).sum (planeSubstitution z) =
          ∑ i, coeff (parameter z) i *
            (F i (planeSubstitution z) * V (planeSubstitution z)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hfactor i]
      _ = (∑ i, coeff (parameter z) i * F i (planeSubstitution z)) *
          V (planeSubstitution z) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hz, zero_mul]
  exact Germ.exists_analytic_monicRelation_of_finiteParameterVanishing
    p d coeff i₀ hpRadius hcoeff haxis hcoeffZero
      x y parameter hx hy hparameter hxZero hyZero hparameterZero
      hnormalizedVanish

end Germ

end OnLeConjecture.Analytic
