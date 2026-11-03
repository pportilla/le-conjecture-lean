/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricGeneralDivision

/-!
# Weierstrass preparation after adjoining the function value

For a Taylor series normalized on the first coordinate axis, this file
prepares the function after subtracting an independent scalar parameter.
The coefficients of the monic factor depend analytically on the retained
coordinate and on the new scalar parameter.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- The remainder vector representing a scalar constant polynomial. -/
@[expose] noncomputable def generalConstantRemainder
    (d : ℕ) (s : ℂ) : Germ.GeneralCoefficientSpace d := fun i ↦
  if i = 0 then s else 0

@[simp]
theorem generalConstantRemainder_zero (d : ℕ) :
    Germ.generalConstantRemainder d 0 = 0 := by
  funext i
  simp [Germ.generalConstantRemainder]

/-- The functional remainder after subtracting an independent scalar
parameter from the dividend. -/
@[expose] noncomputable def shiftedGeneralFunctionalRemainder
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d) :
    Germ.GeneralCoefficientSpace d :=
  Germ.generalFunctionalRemainder p d (w.1.1, w.2) -
    Germ.generalConstantRemainder d w.1.2

/-- The shifted remainder is analytic wherever the original functional
remainder is analytic at the normalized point. -/
theorem analyticAt_shiftedGeneralFunctionalRemainder
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hAnalytic : AnalyticAt ℂ (Germ.generalFunctionalRemainder p d)
      (0, (0 : Germ.GeneralCoefficientSpace d))) :
    AnalyticAt ℂ (Germ.shiftedGeneralFunctionalRemainder p d)
      ((0, 0), 0) := by
  have hy : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        w.1.1) ((0, 0), 0) :=
    analyticAt_fst.comp (x := ((0, 0), 0)) analyticAt_fst
  have hinput : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        (w.1.1, w.2)) ((0, 0), 0) :=
    hy.prod analyticAt_snd
  have hremainder : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        Germ.generalFunctionalRemainder p d (w.1.1, w.2))
      ((0, 0), 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := ((0, 0), 0)) hAnalytic hinput)
  have hs : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        w.1.2) ((0, 0), 0) :=
    analyticAt_snd.comp (x := ((0, 0), 0)) analyticAt_fst
  have hconstant : AnalyticAt ℂ
      (fun w : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
        Germ.generalConstantRemainder d w.1.2) ((0, 0), 0) := by
    apply AnalyticAt.pi
    intro i
    by_cases hi : i = 0
    · simpa [Germ.generalConstantRemainder, hi] using hs
    · simpa [Germ.generalConstantRemainder, hi] using
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : (ℂ × ℂ) × Germ.GeneralCoefficientSpace d ↦
            (0 : ℂ)) ((0, 0), 0))
  exact hremainder.sub hconstant

/-- On the zero parameter fibre, the shifted remainder is minus the
coefficient vector. -/
theorem shiftedGeneralFunctionalRemainder_parameter_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (a : Germ.GeneralCoefficientSpace d) :
    Germ.shiftedGeneralFunctionalRemainder p d ((0, 0), a) = -a := by
  rw [Germ.shiftedGeneralFunctionalRemainder,
    Germ.generalFunctionalRemainder_parameter_zero p d haxis]
  simp

/-- The derivative of the shifted remainder in the coefficient directions
is minus the identity at the normalized point. -/
theorem shiftedGeneralFunctionalRemainder_fderiv_inr_eq_neg
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ
      (Germ.shiftedGeneralFunctionalRemainder p d) ((0, 0), 0)) :
    fderiv ℂ (Germ.shiftedGeneralFunctionalRemainder p d) ((0, 0), 0) ∘L
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
        Germ.shiftedGeneralFunctionalRemainder p d ((0, 0), a)) =
        fun a : Germ.GeneralCoefficientSpace d ↦ -a := by
    funext a
    exact Germ.shiftedGeneralFunctionalRemainder_parameter_zero
      p d haxis a
  change fderiv ℂ
    (fun a : Germ.GeneralCoefficientSpace d ↦
      Germ.shiftedGeneralFunctionalRemainder p d ((0, 0), a)) 0 = _ at hcomp
  rw [hfiber] at hcomp
  have hinclusion : fderiv ℂ
      (fun a : Germ.GeneralCoefficientSpace d ↦ ((0, 0), a)) 0 =
        inclusion := by
    exact inclusion.hasFDerivAt.fderiv
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

/-- The point derivative required for the shifted remainder equation is
invertible. -/
theorem shiftedGeneralFunctionalRemainder_pointDerivative_isInvertible
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ
      (Germ.shiftedGeneralFunctionalRemainder p d) ((0, 0), 0)) :
    (fderiv ℂ (Germ.shiftedGeneralFunctionalRemainder p d) ((0, 0), 0) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × ℂ)
        (Germ.GeneralCoefficientSpace d)).IsInvertible := by
  rw [Germ.shiftedGeneralFunctionalRemainder_fderiv_inr_eq_neg
    p d haxis hAnalytic]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Analytic coefficient functions solve the shifted remainder equation
near the normalized point. -/
theorem exists_analytic_shiftedGeneralCoefficientBranch_of_base_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    ∃ a : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ a (0, 0) ∧
      a (0, 0) = 0 ∧
      ∀ᶠ w in nhds (0, 0),
        Germ.generalFunctionalRemainder p d (w.1, a w) =
          Germ.generalConstantRemainder d w.2 := by
  have hRemainder :=
    Germ.analyticAt_generalFunctionalRemainder p d hp hbase
  have hAnalytic :=
    Germ.analyticAt_shiftedGeneralFunctionalRemainder p d hRemainder
  have hzero : Germ.shiftedGeneralFunctionalRemainder p d
      ((0, 0), (0 : Germ.GeneralCoefficientSpace d)) = 0 := by
    rw [Germ.shiftedGeneralFunctionalRemainder_parameter_zero p d haxis]
    simp
  have hpoint :=
    Germ.shiftedGeneralFunctionalRemainder_pointDerivative_isInvertible
      p d haxis hAnalytic
  let a : ℂ × ℂ → Germ.GeneralCoefficientSpace d :=
    analyticImplicitBranch (Germ.shiftedGeneralFunctionalRemainder p d)
      ((0, 0), 0) hAnalytic hpoint
  have ha : AnalyticAt ℂ a (0, 0) :=
    analyticAt_analyticImplicitBranch
      (Germ.shiftedGeneralFunctionalRemainder p d) ((0, 0), 0)
        hAnalytic hpoint
  have haZero : a (0, 0) = 0 := by
    exact analyticImplicitBranch_apply_base
      (Germ.shiftedGeneralFunctionalRemainder p d) ((0, 0), 0)
        hAnalytic hpoint
  have hequation : ∀ᶠ w in nhds (0, 0),
      Germ.shiftedGeneralFunctionalRemainder p d (w, a w) = 0 := by
    have hbranch := eventually_analyticImplicitBranch_eq
      (Germ.shiftedGeneralFunctionalRemainder p d) ((0, 0), 0)
        hAnalytic hpoint
    simpa only [hzero] using hbranch
  refine ⟨a, ha, haZero, ?_⟩
  filter_upwards [hequation] with w hw
  rw [Germ.shiftedGeneralFunctionalRemainder, sub_eq_zero] at hw
  exact hw

/-- Conditional division whose remainder is the functional remainder used
by the implicit equation. -/
theorem exists_analytic_generalDivision_withFunctionalRemainder_of_base_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (a : ℂ × ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a (0, 0)) (haZero : a (0, 0) = 0) :
    ∃ Q : ℂ × (ℂ × ℂ) → ℂ,
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = Germ.generalFunctionalQuotient p d 0 0 0 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2.1) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
            ∑ i : Fin (d + 1), z.1 ^ i.1 *
              Germ.generalFunctionalRemainder p d (z.2.1, a z.2) i := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  let Q : ℂ × (ℂ × ℂ) → ℂ := fun z ↦
    Germ.generalFunctionalQuotient p d z.1 z.2.1 (a z.2)
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hqAnalytic : AnalyticAt ℂ q.sum
      (Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d))) :=
    (q.hasFPowerSeriesOnBall hqRadius).analyticAt_of_mem hbase
  have haComp : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦ a z.2) (0, 0) :=
    ha.comp (x := (0, 0)) analyticAt_snd
  have hyComp : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦ z.2.1) (0, 0) :=
    analyticAt_fst.comp (x := (0, 0)) analyticAt_snd
  have hcoefficientInput : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦ (z.1, a z.2)) (0, 0) :=
    analyticAt_fst.prod haComp
  have hoperator : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦
        Germ.generalDivisionOperator z.1 (a z.2)) (0, 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.analyticAt_generalDivisionOperator
          (d := d) (0, a (0, 0))) hcoefficientInput)
  have hscalar : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦
        z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d)) (0, 0) := by
    have hproduct := hyComp.smul
      (analyticAt_const : AnalyticAt ℂ
        (fun _ : ℂ × (ℂ × ℂ) ↦
          (1 : Germ.GeneralDivisionEndomorphism d)) (0, 0))
    rw [show (fun z : ℂ × (ℂ × ℂ) ↦
        z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d)) =
      (fun z : ℂ × (ℂ × ℂ) ↦ z.2.1) •
        (fun _ : ℂ × (ℂ × ℂ) ↦
          (1 : Germ.GeneralDivisionEndomorphism d)) by rfl]
    exact hproduct
  have hinput : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦
        (Germ.generalDivisionOperator z.1 (a z.2),
          z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) :=
    hoperator.prod hscalar
  have hinputZero :
      (Germ.generalDivisionOperator (0 : ℂ) (a (0, 0)),
        (0 : ℂ) • (1 : Germ.GeneralDivisionEndomorphism d)) =
      Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) := by
    simp [Germ.generalFunctionalInput, haZero]
  have hstate : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦
        q.sum (Germ.generalDivisionOperator z.1 (a z.2),
          z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) := by
    have hqAt : AnalyticAt ℂ q.sum
        (Germ.generalDivisionOperator (0 : ℂ) (a (0, 0)),
          (0 : ℂ) • (1 : Germ.GeneralDivisionEndomorphism d)) := by
      rwa [hinputZero]
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hqAt hinput)
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    have hprojection : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × ℂ) ↦
          Germ.generalFunctionalQuotientOutput d
            (q.sum (Germ.generalDivisionOperator z.1 (a z.2),
              z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d))))
        (0, 0) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0, 0))
          ((Germ.generalFunctionalQuotientOutput d).analyticAt
            (q.sum (Germ.generalDivisionOperator (0 : ℂ) (a (0, 0)),
              (0 : ℂ) • (1 : Germ.GeneralDivisionEndomorphism d)))) hstate)
    simpa only [Q, Germ.generalFunctionalQuotient,
      Germ.generalFunctionalState, q,
      Germ.generalFunctionalQuotientOutput_apply] using hprojection
  have hplaneInput : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦
        Germ.planePoint z.1 z.2.1) (0, 0) := by
    have hpair : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × ℂ) ↦ (z.1, z.2.1)) (0, 0) :=
      analyticAt_fst.prod hyComp
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt (0, 0)) hpair)
  have hpEventually : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      Germ.planePoint z.1 z.2.1 ∈ Metric.eball 0 p.radius := by
    have hball : Metric.eball 0 p.radius ∈
        nhds (Germ.planePoint (0 : ℂ) (0 : ℂ)) := by
      simpa [Germ.planePoint] using Metric.eball_mem_nhds 0 hp
    exact hplaneInput.continuousAt.eventually hball
  have hinputMem : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      (Germ.generalDivisionOperator z.1 (a z.2),
        z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0 q.radius := by
    have hbase' :
        (Germ.generalDivisionOperator (0 : ℂ) (a (0, 0)),
          (0 : ℂ) • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
        Metric.eball 0 q.radius := by
      rwa [hinputZero]
    exact hinput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbase')
  have hzeroInput : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × ℂ) ↦
        (Germ.generalDivisionOperator 0 (a z.2),
          z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) := by
    have hzeroCoefficient : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × ℂ) ↦ ((0 : ℂ), a z.2))
        (0, 0) := analyticAt_const.prod haComp
    have hzeroOperator : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × ℂ) ↦
          Germ.generalDivisionOperator 0 (a z.2)) (0, 0) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0, 0))
          (Germ.analyticAt_generalDivisionOperator
            (d := d) (0, a (0, 0))) hzeroCoefficient)
    exact hzeroOperator.prod hscalar
  have hzeroMem : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      (Germ.generalDivisionOperator 0 (a z.2),
        z.2.1 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0 q.radius := by
    have hbase' :
        (Germ.generalDivisionOperator (0 : ℂ) (a (0, 0)),
          (0 : ℂ) • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
        Metric.eball 0 q.radius := by
      rwa [hinputZero]
    exact hzeroInput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbase')
  refine ⟨Q, hQ, ?_, ?_⟩
  · change Germ.generalFunctionalQuotient p d 0 0 (a (0, 0)) =
      Germ.generalFunctionalQuotient p d 0 0 0
    rw [haZero]
  filter_upwards [hpEventually, hinputMem, hzeroMem] with z hpz hxz hzeroz
  have hevaluation := Germ.generalDivisionStateEvaluation_functionalState
    p d z.1 z.2.1 (a z.2) hpz hxz
  have hremainder :
      (Germ.generalFunctionalState p d z.1 (a z.2) z.2.1).2 =
        Germ.generalFunctionalRemainder p d (z.2.1, a z.2) := by
    change Germ.generalRemainderProjection d
        (Germ.generalFunctionalState p d z.1 (a z.2) z.2.1) = _
    exact Germ.generalFunctionalState_remainder_eq
      p d z.1 z.2.1 (a z.2) hxz hzeroz
  rw [Germ.generalDivisionStateEvaluation, hremainder] at hevaluation
  simpa only [Q, Germ.generalFunctionalQuotient] using hevaluation.symm

/-- Conditional preparation after subtracting an independent scalar
parameter. -/
theorem exists_analytic_shiftedGeneralPreparation_of_base_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    ∃ a : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × (ℂ × ℂ) → ℂ,
      AnalyticAt ℂ a (0, 0) ∧
      a (0, 0) = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2.1) - z.2.2 =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z := by
  obtain ⟨a, ha, haZero, hbranch⟩ :=
    Germ.exists_analytic_shiftedGeneralCoefficientBranch_of_base_mem
      p d hp haxis hbase
  obtain ⟨Q, hQ, hQBase, hdivision⟩ :=
    Germ.exists_analytic_generalDivision_withFunctionalRemainder_of_base_mem
      p d hp hbase a ha haZero
  have hQZero : Q (0, 0) = 1 := by
    rw [hQBase]
    exact Germ.generalFunctionalQuotient_zero p d haxis
  refine ⟨a, Q, ha, haZero, hQ, hQZero, ?_⟩
  have hbranchInput : Tendsto
      (fun z : ℂ × (ℂ × ℂ) ↦ z.2)
      (nhds (0, 0)) (nhds (0, 0)) := continuousAt_snd
  have hbranchPulled : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      Germ.generalFunctionalRemainder p d (z.2.1, a z.2) =
        Germ.generalConstantRemainder d z.2.2 :=
    hbranchInput.eventually hbranch
  filter_upwards [hdivision, hbranchPulled] with z hz hrem
  rw [hrem] at hz
  have hsum : ∑ i : Fin (d + 1), z.1 ^ i.1 *
      Germ.generalConstantRemainder d z.2.2 i = z.2.2 := by
    simp [Germ.generalConstantRemainder]
  rw [hsum] at hz
  rw [hz]
  ring

/-- Analytic preparation after subtracting an independent scalar parameter
for every exactly normalized series of positive order. -/
theorem exists_analytic_shiftedGeneralPreparation
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    ∃ b : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × (ℂ × ℂ) → ℂ,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2.1) - z.2.2 =
          Germ.generalDivisionPolynomialValue z.1 (b z.2) * Q z := by
  obtain ⟨c, hc, hbase⟩ :=
    Germ.exists_radialScale_generalFunctionalInput_mem p d hp
  let pScaled := Germ.radiallyScaledGeneralSeries p d c
  have hpScaled : 0 < pScaled.radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos p d c hp hc
  have haxisScaled : ∀ n, Germ.mixedCoefficient pScaled n n =
      if n = d + 1 then 1 else 0 :=
    Germ.radiallyScaledGeneralSeries_exact_axis p d c hc haxis
  obtain ⟨a, QScaled, ha, haZero, hQScaled, hQScaledZero,
      hfactorScaled⟩ :=
    Germ.exists_analytic_shiftedGeneralPreparation_of_base_mem
      pScaled d hpScaled haxisScaled hbase
  let inverseScalar : ℂ → ℂ := fun x ↦ c⁻¹ * x
  let inverseValue : ℂ → ℂ := fun s ↦ (c ^ (d + 1))⁻¹ * s
  let inverseParameter : ℂ × ℂ → ℂ × ℂ := fun w ↦
    (inverseScalar w.1, inverseValue w.2)
  let inverseInput : ℂ × (ℂ × ℂ) → ℂ × (ℂ × ℂ) :=
    fun z ↦ (inverseScalar z.1, inverseParameter z.2)
  let b : ℂ × ℂ → Germ.GeneralCoefficientSpace d := fun w i ↦
    c ^ (d + 1 - i.1) * a (inverseParameter w) i
  let Q : ℂ × (ℂ × ℂ) → ℂ := fun z ↦
    QScaled (inverseInput z)
  have hinverseScalar : AnalyticAt ℂ inverseScalar 0 := by
    dsimp only [inverseScalar]
    fun_prop
  have hinverseValue : AnalyticAt ℂ inverseValue 0 := by
    dsimp only [inverseValue]
    fun_prop
  have hinverseParameter : AnalyticAt ℂ inverseParameter (0, 0) :=
    (hinverseScalar.comp (x := (0, 0)) analyticAt_fst).prod
      (hinverseValue.comp (x := (0, 0)) analyticAt_snd)
  have hinverseInput : AnalyticAt ℂ inverseInput (0, 0) :=
    (hinverseScalar.comp (x := (0, 0)) analyticAt_fst).prod
      (hinverseParameter.comp (x := (0, 0)) analyticAt_snd)
  have hinverseParameterZero : inverseParameter (0, 0) = (0, 0) := by
    simp [inverseParameter, inverseScalar, inverseValue]
  have hinverseInputZero : inverseInput (0, 0) = (0, 0) := by
    simp [inverseInput, inverseParameter, inverseScalar, inverseValue]
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
    simp [b, inverseParameter, inverseScalar, inverseValue, haZero]
  have hQScaledAt : AnalyticAt ℂ QScaled (inverseInput (0, 0)) := by
    simpa only [hinverseInputZero] using hQScaled
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    simpa only [Q, Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hQScaledAt hinverseInput)
  have hQZero : Q (0, 0) = 1 := by
    change QScaled (inverseInput (0, 0)) = 1
    rw [hinverseInputZero]
    exact hQScaledZero
  have hsumScaled :=
    Germ.eventually_radiallyScaledGeneralSeries_sum_eq p d c hp hc
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
  have hsumInput : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum (Germ.planePoint z.1 z.2.1) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c • Germ.planePoint z.1 z.2.1) :=
    (by
      have htendsto := hplaneInput.continuousAt
      change Tendsto (fun z : ℂ × (ℂ × ℂ) ↦
        Germ.planePoint z.1 z.2.1) (nhds (0, 0))
          (nhds (Germ.planePoint (0 : ℂ) (0 : ℂ))) at htendsto
      have hzero : Germ.planePoint (0 : ℂ) (0 : ℂ) = 0 := by
        simp [Germ.planePoint]
      rw [hzero] at htendsto
      exact htendsto.eventually hsumScaled)
  have hsumAtInverse : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum (Germ.planePoint (inverseInput z).1
          (inverseInput z).2.1) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c • Germ.planePoint (inverseInput z).1
            (inverseInput z).2.1) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hsumInput)
  have hfactorAtInverse : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum (Germ.planePoint (inverseInput z).1
          (inverseInput z).2.1) - (inverseInput z).2.2 =
        Germ.generalDivisionPolynomialValue (inverseInput z).1
            (a (inverseInput z).2) * QScaled (inverseInput z) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hfactorScaled)
  refine ⟨b, Q, hb, hbZero, hQ, hQZero, ?_⟩
  filter_upwards [hsumAtInverse, hfactorAtInverse] with z hsum hfactor
  have hsourceScale : c • Germ.planePoint
      (inverseInput z).1 (inverseInput z).2.1 =
      Germ.planePoint z.1 z.2.1 := by
    ext i
    fin_cases i <;>
      simp [inverseInput, inverseParameter, inverseScalar,
        Germ.planePoint, hc]
  have hscaled : (c ^ (d + 1))⁻¹ *
        p.sum (Germ.planePoint z.1 z.2.1) -
        (c ^ (d + 1))⁻¹ * z.2.2 =
      Germ.generalDivisionPolynomialValue (inverseInput z).1
          (a (inverseInput z).2) * QScaled (inverseInput z) := by
    rw [← hfactor, hsum, hsourceScale]
  calc
    p.sum (Germ.planePoint z.1 z.2.1) - z.2.2 =
        c ^ (d + 1) *
          ((c ^ (d + 1))⁻¹ *
            p.sum (Germ.planePoint z.1 z.2.1) -
            (c ^ (d + 1))⁻¹ * z.2.2) := by
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

/-- Adjoining the value of an exactly normalized analytic function produces
a monic equation for the first source coordinate. -/
theorem exists_analytic_monicRelation_at_functionValue
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    ∃ b : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (z 0)
          (b (z 1, p.sum z)) = 0 := by
  obtain ⟨b, Q, hb, hbZero, hQ, hQZero, hfactor⟩ :=
    Germ.exists_analytic_shiftedGeneralPreparation p d hp haxis
  have hfactorZero := hfactor.self_of_nhds
  have hpolynomialZero : Germ.generalDivisionPolynomialValue 0 (b (0, 0)) = 0 := by
    rw [hbZero]
    simp [Germ.generalDivisionPolynomialValue]
  have hpZero : p.sum (0 : Source 2) = 0 := by
    change p.sum (Germ.planePoint 0 0) - 0 =
      Germ.generalDivisionPolynomialValue 0 (b (0, 0)) * Q (0, 0)
        at hfactorZero
    rw [hpolynomialZero, zero_mul] at hfactorZero
    simpa [Germ.planePoint] using hfactorZero
  have hpAnalytic : AnalyticAt ℂ p.sum 0 :=
    (p.hasFPowerSeriesOnBall hp).analyticAt_of_mem
      (Metric.mem_eball_self hp)
  have hcoordinateZero : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0
  have hcoordinateOne : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
  let substitution : Source 2 → ℂ × (ℂ × ℂ) := fun z ↦
    (z 0, (z 1, p.sum z))
  have hsubstitution : AnalyticAt ℂ substitution 0 :=
    hcoordinateZero.prod (hcoordinateOne.prod hpAnalytic)
  have hsubstitutionZero : substitution 0 = (0, 0) := by
    simp [substitution, hpZero]
  have hfactorSubstituted : ∀ᶠ z : Source 2 in nhds 0,
      p.sum (Germ.planePoint (z 0) (z 1)) - p.sum z =
        Germ.generalDivisionPolynomialValue (z 0)
          (b (z 1, p.sum z)) * Q (substitution z) := by
    have hpull := hsubstitution.continuousAt.eventually (by
      simpa only [hsubstitutionZero] using hfactor)
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
  filter_upwards [hfactorSubstituted, hQEventually] with z hz hQz
  have hplane : Germ.planePoint (z 0) (z 1) = z := by
    ext i
    fin_cases i <;> simp [Germ.planePoint]
  rw [hplane, sub_self] at hz
  exact (mul_eq_zero.mp hz.symm).resolve_right hQz

/-- The monic relation may be written using any function represented by the
normalized Taylor series. -/
theorem exists_analytic_monicRelation_at_representativeValue
    (F : Source 2 → ℂ)
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : HasFPowerSeriesAt F p 0)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    ∃ b : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (z 0)
          (b (z 1, F z)) = 0 := by
  obtain ⟨b, hb, hbZero, hrelation⟩ :=
    Germ.exists_analytic_monicRelation_at_functionValue
      p d hp.radius_pos haxis
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
  have hrepresentative : F =ᶠ[nhds 0] p.sum := by
    filter_upwards [hp.eventually_hasSum_sub,
      hpSum.eventually_hasSum_sub] with z hzF hzSum
    simpa only [sub_zero] using hzF.unique hzSum
  refine ⟨b, hb, hbZero, ?_⟩
  filter_upwards [hrelation, hrepresentative] with z hz hFz
  rwa [← hFz] at hz

end Germ

end OnLeConjecture.Analytic
