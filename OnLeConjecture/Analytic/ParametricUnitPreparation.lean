/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricGeneralPreparation

/-!
# Weierstrass preparation with a parameter multiplier

This file prepares `p - s v`, where `p` has an exactly normalized first
coordinate axis and `v` is a second analytic series. This form preserves the
original function value when `p` is obtained by multiplying a regular
function by a source unit.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- The remainder equation for the parameter dependent dividend `p - s v`. -/
@[expose] noncomputable def shiftedMultiplierFunctionalRemainder
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d) :
    Germ.GeneralCoefficientSpace d :=
  Germ.generalFunctionalRemainder p d (w.1.1, w.2) -
    w.1.2 • Germ.generalFunctionalRemainder v d (w.1.1, w.2)

/-- The multiplier remainder equation is analytic at the normalized base
point whenever division of both series converges there. -/
theorem analyticAt_shiftedMultiplierFunctionalRemainder
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius) (hv : 0 < v.radius)
    (hbaseP : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (hbaseV : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) v).radius) :
    AnalyticAt ℂ (Germ.shiftedMultiplierFunctionalRemainder p v d)
      ((0, 0), 0) := by
  have hP := Germ.analyticAt_generalFunctionalRemainder p d hp hbaseP
  have hV := Germ.analyticAt_generalFunctionalRemainder v d hv hbaseV
  have hy : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        w.1.1) ((0, 0), 0) :=
    analyticAt_fst.comp (x := ((0, 0), 0)) analyticAt_fst
  have hinput : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        (w.1.1, w.2)) ((0, 0), 0) :=
    hy.prod analyticAt_snd
  have hPComp : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        Germ.generalFunctionalRemainder p d (w.1.1, w.2))
      ((0, 0), 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := ((0, 0), 0)) hP hinput)
  have hVComp : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        Germ.generalFunctionalRemainder v d (w.1.1, w.2))
      ((0, 0), 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := ((0, 0), 0)) hV hinput)
  have hs : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        w.1.2) ((0, 0), 0) :=
    analyticAt_snd.comp (x := ((0, 0), 0)) analyticAt_fst
  exact hPComp.sub (hs.smul hVComp)

/-- On the zero parameter fibre, the multiplier term disappears and the
remainder is minus the coefficient vector. -/
theorem shiftedMultiplierFunctionalRemainder_parameter_zero
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (a : Germ.GeneralCoefficientSpace d) :
    Germ.shiftedMultiplierFunctionalRemainder p v d ((0, 0), a) = -a := by
  rw [Germ.shiftedMultiplierFunctionalRemainder,
    Germ.generalFunctionalRemainder_parameter_zero p d haxis]
  simp

/-- The derivative in the coefficient directions is minus the identity at
the normalized base point. -/
theorem shiftedMultiplierFunctionalRemainder_fderiv_inr_eq_neg
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ
      (Germ.shiftedMultiplierFunctionalRemainder p v d) ((0, 0), 0)) :
    fderiv ℂ (Germ.shiftedMultiplierFunctionalRemainder p v d)
          ((0, 0), 0) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ)
          (Germ.GeneralCoefficientSpace d) =
      (ContinuousLinearEquiv.neg ℂ :
        Germ.GeneralCoefficientSpace d ≃L[ℂ]
          Germ.GeneralCoefficientSpace d) := by
  let inclusion := ContinuousLinearMap.inr ℂ (ℂ × ℂ)
    (Germ.GeneralCoefficientSpace d)
  have hcomp := fderiv_comp
    (x := (0 : Germ.GeneralCoefficientSpace d))
    hAnalytic.differentiableAt inclusion.differentiableAt
  have hfiber :
      (fun a : Germ.GeneralCoefficientSpace d ↦
        Germ.shiftedMultiplierFunctionalRemainder p v d ((0, 0), a)) =
        fun a : Germ.GeneralCoefficientSpace d ↦ -a := by
    funext a
    exact Germ.shiftedMultiplierFunctionalRemainder_parameter_zero
      p v d haxis a
  change fderiv ℂ
    (fun a : Germ.GeneralCoefficientSpace d ↦
      Germ.shiftedMultiplierFunctionalRemainder p v d ((0, 0), a)) 0 = _
      at hcomp
  rw [hfiber] at hcomp
  have hinclusion : fderiv ℂ
      (fun a : Germ.GeneralCoefficientSpace d ↦ ((0, 0), a)) 0 =
        inclusion := inclusion.hasFDerivAt.fderiv
  have hneg : fderiv ℂ
      (fun a : Germ.GeneralCoefficientSpace d ↦ -a) 0 =
        (ContinuousLinearEquiv.neg ℂ :
          Germ.GeneralCoefficientSpace d ≃L[ℂ]
            Germ.GeneralCoefficientSpace d) := by
    exact (ContinuousLinearEquiv.neg ℂ :
      Germ.GeneralCoefficientSpace d ≃L[ℂ]
        Germ.GeneralCoefficientSpace d).toContinuousLinearMap.hasFDerivAt.fderiv
  rw [hinclusion, hneg] at hcomp
  exact hcomp.symm

/-- The point derivative for the multiplier remainder equation is
invertible. -/
theorem shiftedMultiplierFunctionalRemainder_pointDerivative_isInvertible
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ
      (Germ.shiftedMultiplierFunctionalRemainder p v d) ((0, 0), 0)) :
    (fderiv ℂ (Germ.shiftedMultiplierFunctionalRemainder p v d)
          ((0, 0), 0) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ)
          (Germ.GeneralCoefficientSpace d)).IsInvertible := by
  rw [Germ.shiftedMultiplierFunctionalRemainder_fderiv_inr_eq_neg
    p v d haxis hAnalytic]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Analytic coefficients solve the multiplier remainder equation near the
normalized point. -/
theorem exists_analytic_shiftedMultiplierCoefficientBranch_of_base_mem
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius) (hv : 0 < v.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hbaseP : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (hbaseV : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) v).radius) :
    ∃ a : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ a (0, 0) ∧
      a (0, 0) = 0 ∧
      ∀ᶠ w in nhds (0, 0),
        Germ.generalFunctionalRemainder p d (w.1, a w) =
          w.2 • Germ.generalFunctionalRemainder v d (w.1, a w) := by
  have hAnalytic := Germ.analyticAt_shiftedMultiplierFunctionalRemainder
    p v d hp hv hbaseP hbaseV
  have hzero : Germ.shiftedMultiplierFunctionalRemainder p v d
      ((0, 0), (0 : Germ.GeneralCoefficientSpace d)) = 0 := by
    rw [Germ.shiftedMultiplierFunctionalRemainder_parameter_zero
      p v d haxis]
    simp
  have hpoint :=
    Germ.shiftedMultiplierFunctionalRemainder_pointDerivative_isInvertible
      p v d haxis hAnalytic
  let a : ℂ × ℂ → Germ.GeneralCoefficientSpace d :=
    analyticImplicitBranch
      (Germ.shiftedMultiplierFunctionalRemainder p v d)
      ((0, 0), 0) hAnalytic hpoint
  have ha : AnalyticAt ℂ a (0, 0) :=
    analyticAt_analyticImplicitBranch
      (Germ.shiftedMultiplierFunctionalRemainder p v d)
      ((0, 0), 0) hAnalytic hpoint
  have haZero : a (0, 0) = 0 :=
    analyticImplicitBranch_apply_base
      (Germ.shiftedMultiplierFunctionalRemainder p v d)
      ((0, 0), 0) hAnalytic hpoint
  have hequation : ∀ᶠ w in nhds (0, 0),
      Germ.shiftedMultiplierFunctionalRemainder p v d (w, a w) = 0 := by
    have hbranch := eventually_analyticImplicitBranch_eq
      (Germ.shiftedMultiplierFunctionalRemainder p v d)
      ((0, 0), 0) hAnalytic hpoint
    simpa only [hzero] using hbranch
  refine ⟨a, ha, haZero, ?_⟩
  filter_upwards [hequation] with w hw
  rw [Germ.shiftedMultiplierFunctionalRemainder, sub_eq_zero] at hw
  exact hw

/-- Conditional preparation of `p - s v`. -/
theorem exists_analytic_shiftedMultiplierPreparation_of_base_mem
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius) (hv : 0 < v.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hbaseP : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (hbaseV : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) v).radius) :
    ∃ a : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × (ℂ × ℂ) → ℂ,
      AnalyticAt ℂ a (0, 0) ∧
      a (0, 0) = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2.1) -
            z.2.2 * v.sum (Germ.planePoint z.1 z.2.1) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z := by
  obtain ⟨a, ha, haZero, hbranch⟩ :=
    Germ.exists_analytic_shiftedMultiplierCoefficientBranch_of_base_mem
      p v d hp hv haxis hbaseP hbaseV
  obtain ⟨Qp, hQp, hQpZero, hdivisionP⟩ :=
    Germ.exists_analytic_generalDivision_withFunctionalRemainder_of_base_mem
      p d hp hbaseP a ha haZero
  obtain ⟨Qv, hQv, hQvZero, hdivisionV⟩ :=
    Germ.exists_analytic_generalDivision_withFunctionalRemainder_of_base_mem
      v d hv hbaseV a ha haZero
  let Q : ℂ × (ℂ × ℂ) → ℂ := fun z ↦
    Qp z - z.2.2 * Qv z
  have hs : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦ z.2.2) (0, 0) :=
    analyticAt_snd.comp (x := (0, 0)) analyticAt_snd
  have hQ : AnalyticAt ℂ Q (0, 0) := hQp.sub (hs.mul hQv)
  have hQZero : Q (0, 0) = 1 := by
    change Qp (0, 0) - 0 * Qv (0, 0) = 1
    rw [hQpZero, Germ.generalFunctionalQuotient_zero p d haxis]
    ring
  refine ⟨a, Q, ha, haZero, hQ, hQZero, ?_⟩
  have hbranchInput : Tendsto
      (fun z : ℂ × (ℂ × ℂ) ↦ z.2)
      (nhds (0, 0)) (nhds (0, 0)) := continuousAt_snd
  have hbranchPulled : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      Germ.generalFunctionalRemainder p d (z.2.1, a z.2) =
        z.2.2 • Germ.generalFunctionalRemainder v d (z.2.1, a z.2) :=
    hbranchInput.eventually hbranch
  filter_upwards [hdivisionP, hdivisionV, hbranchPulled] with z hpz hvz hrem
  rw [hpz, hvz]
  rw [hrem]
  simp only [Pi.smul_apply, smul_eq_mul]
  dsimp only [Q]
  have hsum :
      (∑ i : Fin (d + 1), z.1 ^ i.1 *
        (z.2.2 * Germ.generalFunctionalRemainder v d
          (z.2.1, a z.2) i)) =
      z.2.2 * ∑ i : Fin (d + 1), z.1 ^ i.1 *
        Germ.generalFunctionalRemainder v d (z.2.1, a z.2) i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

/-- One nonzero radial scale places the base division operator inside the
convergence balls for two series simultaneously. -/
theorem exists_radialScale_generalFunctionalInput_mem_pair
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (hp : 0 < p.radius) (hv : 0 < v.radius) :
    ∃ c : ℂ, c ≠ 0 ∧
      Germ.generalFunctionalInput d
          (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d)
            (Germ.radiallyScaledGeneralSeries p d c)).radius ∧
      Germ.generalFunctionalInput d
          (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d)
            (Germ.radiallyScaledGeneralSeries v d c)).radius := by
  let qP := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  let qV := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) v
  let base := Germ.generalFunctionalInput d
    (0, (0 : Germ.GeneralCoefficientSpace d))
  have hqPRadius : 0 < qP.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hqVRadius : 0 < qV.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos v hv
  have hminRadius : 0 < min qP.radius qV.radius :=
    lt_min hqPRadius hqVRadius
  obtain ⟨delta, hdelta, hdeltaSmall⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt
      (a := ((‖base‖₊ + 1 : ℝ≥0) : ℝ≥0∞))
      (b := min qP.radius qV.radius) (by simp) hminRadius.ne'
  let c : ℂ := (delta : ℝ)
  have hc : c ≠ 0 := by
    simpa [c] using hdelta.ne'
  let scale := Germ.generalRadialAlgebraScaleContinuousLinearMap d c
  have hscaleNorm : ‖scale‖ₑ ≤ (delta : ℝ≥0∞) := by
    rw [enorm_eq_nnnorm]
    have hnorm :=
      Germ.norm_generalRadialAlgebraScaleContinuousLinearMap_le d c
    have hcNorm : ‖c‖ = (delta : ℝ) := by simp [c]
    rw [hcNorm] at hnorm
    dsimp only [scale]
    exact_mod_cast hnorm
  have hproductMin : ‖base‖ₑ * ‖scale‖ₑ < min qP.radius qV.radius := by
    calc
      ‖base‖ₑ * ‖scale‖ₑ ≤
          (‖base‖₊ : ℝ≥0∞) * (delta : ℝ≥0∞) := by
        rw [enorm_eq_nnnorm]
        gcongr
      _ = (delta : ℝ≥0∞) * (‖base‖₊ : ℝ≥0∞) := by
        rw [mul_comm]
      _ ≤ (delta : ℝ≥0∞) *
          ((‖base‖₊ + 1 : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast le_add_of_nonneg_right zero_le_one
      _ < min qP.radius qV.radius := hdeltaSmall
  have hmemP : base ∈ Metric.eball 0
      (Germ.banachAlgebraExtensionSeries
        (A := Germ.GeneralDivisionEndomorphism d)
        (Germ.radiallyScaledGeneralSeries p d c)).radius := by
    have hproduct : ‖base‖ₑ * ‖scale‖ₑ < qP.radius :=
      hproductMin.trans_le (min_le_left _ _)
    have hdiv : ‖base‖ₑ < qP.radius / ‖scale‖ₑ := by
      rw [ENNReal.lt_div_iff_mul_lt]
      · exact hproduct
      · exact Or.inr enorm_ne_top
      · exact Or.inl enorm_ne_top
    have hradius : ‖base‖ₑ <
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d)
          (Germ.radiallyScaledGeneralSeries p d c)).radius :=
      hdiv.trans_le
        (Germ.div_le_radius_banachAlgebraExtensionSeries_radiallyScaledGeneral
          p d c hc)
    exact mem_eball_zero_iff.2 hradius
  have hmemV : base ∈ Metric.eball 0
      (Germ.banachAlgebraExtensionSeries
        (A := Germ.GeneralDivisionEndomorphism d)
        (Germ.radiallyScaledGeneralSeries v d c)).radius := by
    have hproduct : ‖base‖ₑ * ‖scale‖ₑ < qV.radius :=
      hproductMin.trans_le (min_le_right _ _)
    have hdiv : ‖base‖ₑ < qV.radius / ‖scale‖ₑ := by
      rw [ENNReal.lt_div_iff_mul_lt]
      · exact hproduct
      · exact Or.inr enorm_ne_top
      · exact Or.inl enorm_ne_top
    have hradius : ‖base‖ₑ <
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d)
          (Germ.radiallyScaledGeneralSeries v d c)).radius :=
      hdiv.trans_le
        (Germ.div_le_radius_banachAlgebraExtensionSeries_radiallyScaledGeneral
          v d c hc)
    exact mem_eball_zero_iff.2 hradius
  exact ⟨c, hc, hmemP, hmemV⟩

/-- Analytic preparation of `p - s v` for every exactly normalized series
`p` and every convergent multiplier series `v`. -/
theorem exists_analytic_shiftedMultiplierPreparation
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius) (hv : 0 < v.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    ∃ b : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × (ℂ × ℂ) → ℂ,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2.1) -
            z.2.2 * v.sum (Germ.planePoint z.1 z.2.1) =
          Germ.generalDivisionPolynomialValue z.1 (b z.2) * Q z := by
  obtain ⟨c, hc, hbaseP, hbaseV⟩ :=
    Germ.exists_radialScale_generalFunctionalInput_mem_pair p v d hp hv
  let pScaled := Germ.radiallyScaledGeneralSeries p d c
  let vScaled := Germ.radiallyScaledGeneralSeries v d c
  have hpScaled : 0 < pScaled.radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos p d c hp hc
  have hvScaled : 0 < vScaled.radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos v d c hv hc
  have haxisScaled : ∀ n, Germ.mixedCoefficient pScaled n n =
      if n = d + 1 then 1 else 0 :=
    Germ.radiallyScaledGeneralSeries_exact_axis p d c hc haxis
  obtain ⟨a, QScaled, ha, haZero, hQScaled, hQScaledZero,
      hfactorScaled⟩ :=
    Germ.exists_analytic_shiftedMultiplierPreparation_of_base_mem
      pScaled vScaled d hpScaled hvScaled haxisScaled hbaseP hbaseV
  let inverseScalar : ℂ → ℂ := fun x ↦ c⁻¹ * x
  let inverseParameter : ℂ × ℂ → ℂ × ℂ := fun w ↦
    (inverseScalar w.1, w.2)
  let inverseInput : ℂ × (ℂ × ℂ) → ℂ × (ℂ × ℂ) :=
    fun z ↦ (inverseScalar z.1, inverseParameter z.2)
  let b : ℂ × ℂ → Germ.GeneralCoefficientSpace d := fun w i ↦
    c ^ (d + 1 - i.1) * a (inverseParameter w) i
  let Q : ℂ × (ℂ × ℂ) → ℂ := fun z ↦
    QScaled (inverseInput z)
  have hinverseScalar : AnalyticAt ℂ inverseScalar 0 := by
    dsimp only [inverseScalar]
    fun_prop
  have hinverseParameter : AnalyticAt ℂ inverseParameter (0, 0) :=
    (hinverseScalar.comp (x := (0, 0)) analyticAt_fst).prod analyticAt_snd
  have hinverseInput : AnalyticAt ℂ inverseInput (0, 0) :=
    (hinverseScalar.comp (x := (0, 0)) analyticAt_fst).prod
      (hinverseParameter.comp (x := (0, 0)) analyticAt_snd)
  have hinverseParameterZero : inverseParameter (0, 0) = (0, 0) := by
    simp [inverseParameter, inverseScalar]
  have hinverseInputZero : inverseInput (0, 0) = (0, 0) := by
    simp [inverseInput, inverseParameter, inverseScalar]
  have haAtInverseZero : AnalyticAt ℂ a (inverseParameter (0, 0)) := by
    simpa only [hinverseParameterZero] using ha
  have haComp : AnalyticAt ℂ (fun w ↦ a (inverseParameter w)) (0, 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) haAtInverseZero hinverseParameter)
  have hb : AnalyticAt ℂ b (0, 0) := by
    apply AnalyticAt.pi
    intro i
    have hcoordinate : AnalyticAt ℂ
        (fun w ↦ a (inverseParameter w) i) (0, 0) := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        (AnalyticAt.comp (x := (0, 0))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
            (a (inverseParameter (0, 0)))) haComp)
    exact analyticAt_const.mul hcoordinate
  have hbZero : b (0, 0) = 0 := by
    funext i
    simp [b, inverseParameter, inverseScalar, haZero]
  have hQScaledAt : AnalyticAt ℂ QScaled (inverseInput (0, 0)) := by
    simpa only [hinverseInputZero] using hQScaled
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    simpa only [Q, Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hQScaledAt hinverseInput)
  have hQZero : Q (0, 0) = 1 := by
    change QScaled (inverseInput (0, 0)) = 1
    rw [hinverseInputZero]
    exact hQScaledZero
  have hsumScaledP :=
    Germ.eventually_radiallyScaledGeneralSeries_sum_eq p d c hp hc
  have hsumScaledV :=
    Germ.eventually_radiallyScaledGeneralSeries_sum_eq v d c hv hc
  have hplaneInput : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦
        Germ.planePoint z.1 z.2.1) (0, 0) := by
    have hretained : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × ℂ) ↦ z.2.1) (0, 0) :=
      analyticAt_fst.comp (x := (0, 0)) analyticAt_snd
    have hpair : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × ℂ) ↦ (z.1, z.2.1)) (0, 0) :=
      analyticAt_fst.prod hretained
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt (0, 0)) hpair)
  have hsumInputP : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum (Germ.planePoint z.1 z.2.1) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c • Germ.planePoint z.1 z.2.1) := by
    have htendsto := hplaneInput.continuousAt
    change Tendsto (fun z : ℂ × (ℂ × ℂ) ↦
      Germ.planePoint z.1 z.2.1) (nhds (0, 0))
        (nhds (Germ.planePoint (0 : ℂ) (0 : ℂ))) at htendsto
    have hzero : Germ.planePoint (0 : ℂ) (0 : ℂ) = 0 := by
      simp [Germ.planePoint]
    rw [hzero] at htendsto
    exact htendsto.eventually hsumScaledP
  have hsumInputV : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      vScaled.sum (Germ.planePoint z.1 z.2.1) =
        (c ^ (d + 1))⁻¹ *
          v.sum (c • Germ.planePoint z.1 z.2.1) := by
    have htendsto := hplaneInput.continuousAt
    change Tendsto (fun z : ℂ × (ℂ × ℂ) ↦
      Germ.planePoint z.1 z.2.1) (nhds (0, 0))
        (nhds (Germ.planePoint (0 : ℂ) (0 : ℂ))) at htendsto
    have hzero : Germ.planePoint (0 : ℂ) (0 : ℂ) = 0 := by
      simp [Germ.planePoint]
    rw [hzero] at htendsto
    exact htendsto.eventually hsumScaledV
  have hsumAtInverseP : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum (Germ.planePoint (inverseInput z).1
          (inverseInput z).2.1) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c • Germ.planePoint (inverseInput z).1
            (inverseInput z).2.1) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hsumInputP)
  have hsumAtInverseV : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      vScaled.sum (Germ.planePoint (inverseInput z).1
          (inverseInput z).2.1) =
        (c ^ (d + 1))⁻¹ *
          v.sum (c • Germ.planePoint (inverseInput z).1
            (inverseInput z).2.1) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hsumInputV)
  have hfactorAtInverse : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum (Germ.planePoint (inverseInput z).1
          (inverseInput z).2.1) -
          (inverseInput z).2.2 *
            vScaled.sum (Germ.planePoint (inverseInput z).1
              (inverseInput z).2.1) =
        Germ.generalDivisionPolynomialValue (inverseInput z).1
            (a (inverseInput z).2) * QScaled (inverseInput z) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hfactorScaled)
  refine ⟨b, Q, hb, hbZero, hQ, hQZero, ?_⟩
  filter_upwards [hsumAtInverseP, hsumAtInverseV, hfactorAtInverse] with
      z hsumP hsumV hfactor
  have hsourceScale : c • Germ.planePoint
      (inverseInput z).1 (inverseInput z).2.1 =
      Germ.planePoint z.1 z.2.1 := by
    ext i
    fin_cases i <;>
      simp [inverseInput, inverseParameter, inverseScalar,
        Germ.planePoint, hc]
  have hparameter : (inverseInput z).2.2 = z.2.2 := rfl
  have hscaled :
      (c ^ (d + 1))⁻¹ *
          p.sum (Germ.planePoint z.1 z.2.1) -
        z.2.2 * ((c ^ (d + 1))⁻¹ *
          v.sum (Germ.planePoint z.1 z.2.1)) =
      Germ.generalDivisionPolynomialValue (inverseInput z).1
          (a (inverseInput z).2) * QScaled (inverseInput z) := by
    rw [← hfactor, hsumP, hsumV, hsourceScale, hparameter]
  calc
    p.sum (Germ.planePoint z.1 z.2.1) -
        z.2.2 * v.sum (Germ.planePoint z.1 z.2.1) =
      c ^ (d + 1) *
        ((c ^ (d + 1))⁻¹ *
            p.sum (Germ.planePoint z.1 z.2.1) -
          z.2.2 * ((c ^ (d + 1))⁻¹ *
            v.sum (Germ.planePoint z.1 z.2.1))) := by
      field_simp
    _ = c ^ (d + 1) *
        (Germ.generalDivisionPolynomialValue (inverseInput z).1
          (a (inverseInput z).2) * QScaled (inverseInput z)) := by
      rw [hscaled]
    _ = Germ.generalDivisionPolynomialValue z.1 (b z.2) * Q z := by
      rw [← mul_assoc]
      rw [show (inverseInput z).1 = inverseScalar z.1 by rfl]
      rw [Germ.pow_mul_generalDivisionPolynomialValue_inverse
        d c z.1 (a (inverseInput z).2) hc]

/-- A factorization `p = F v` produces a monic relation whose coefficients
depend analytically on the retained coordinate and the original value `F`. -/
theorem exists_analytic_monicRelation_at_multiplierValue
    (F : Source 2 → ℂ)
    (p v : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius) (hv : 0 < v.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hF : AnalyticAt ℂ F 0) (hFZero : F 0 = 0)
    (hfactor : ∀ᶠ z : Source 2 in nhds 0,
      p.sum z = F z * v.sum z) :
    ∃ b : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (z 0)
          (b (z 1, F z)) = 0 := by
  obtain ⟨b, Q, hb, hbZero, hQ, hQZero, hpreparation⟩ :=
    Germ.exists_analytic_shiftedMultiplierPreparation
      p v d hp hv haxis
  have hcoordinateZero : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0
  have hcoordinateOne : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
  let substitution : Source 2 → ℂ × (ℂ × ℂ) := fun z ↦
    (z 0, (z 1, F z))
  have hsubstitution : AnalyticAt ℂ substitution 0 :=
    hcoordinateZero.prod (hcoordinateOne.prod hF)
  have hsubstitutionZero : substitution 0 = (0, 0) := by
    simp [substitution, hFZero]
  have hpreparationSubstituted : ∀ᶠ z : Source 2 in nhds 0,
      p.sum (Germ.planePoint (z 0) (z 1)) -
          F z * v.sum (Germ.planePoint (z 0) (z 1)) =
        Germ.generalDivisionPolynomialValue (z 0)
          (b (z 1, F z)) * Q (substitution z) := by
    have hpull := hsubstitution.continuousAt.eventually (by
      simpa only [hsubstitutionZero] using hpreparation)
    filter_upwards [hpull] with z hz
    simpa only [substitution] using hz
  have hQSubstitution : AnalyticAt ℂ (fun z ↦ Q (substitution z)) 0 := by
    have hQAt : AnalyticAt ℂ Q (substitution 0) := by
      simpa only [hsubstitutionZero] using hQ
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0 : Source 2)) hQAt hsubstitution)
  have hQSubstitutionZero : Q (substitution 0) ≠ 0 := by
    rw [hsubstitutionZero, hQZero]
    exact one_ne_zero
  have hQEventually : ∀ᶠ z : Source 2 in nhds 0,
      Q (substitution z) ≠ 0 :=
    hQSubstitution.continuousAt.eventually_ne hQSubstitutionZero
  refine ⟨b, hb, hbZero, ?_⟩
  filter_upwards [hpreparationSubstituted, hfactor, hQEventually] with
      z hz hfactorz hQz
  have hplane : Germ.planePoint (z 0) (z 1) = z := by
    ext i
    fin_cases i <;> simp [Germ.planePoint]
  rw [hplane, hfactorz, sub_self] at hz
  exact (mul_eq_zero.mp hz.symm).resolve_right hQz

end Germ

end OnLeConjecture.Analytic
