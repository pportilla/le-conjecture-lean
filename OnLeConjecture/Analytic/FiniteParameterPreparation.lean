/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricUnitPreparation

/-!
# Preparation for finite parameter expansions

The dividend in this file is a finite sum of plane analytic series whose
scalar coefficients depend analytically on an auxiliary parameter. This is
the form produced by a resultant polynomial in the remaining target
coordinates.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

variable {P ι : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℂ P]
variable [Fintype ι] [DecidableEq ι]

/-- The sum of the division remainders in a finite parameter expansion. -/
@[expose] noncomputable def finiteParameterFunctionalRemainder
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ)
    (w : (ℂ × P) × Germ.GeneralCoefficientSpace d) :
    Germ.GeneralCoefficientSpace d :=
  ∑ i, coeff w.1.2 i •
    Germ.generalFunctionalRemainder (p i) d (w.1.1, w.2)

omit [DecidableEq ι] in
/-- The finite remainder sum is analytic when every constituent division
converges at the base operator. -/
theorem analyticAt_finiteParameterFunctionalRemainder
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ)
    (hp : ∀ i, 0 < (p i).radius)
    (hbase : ∀ i, Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) (p i)).radius)
    (hcoeff : AnalyticAt ℂ coeff 0) :
    AnalyticAt ℂ (Germ.finiteParameterFunctionalRemainder p d coeff)
      ((0, 0), 0) := by
  classical
  have hy : AnalyticAt ℂ
      (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
        w.1.1) ((0, 0), 0) :=
    analyticAt_fst.comp (x := ((0, 0), 0)) analyticAt_fst
  have hinput : AnalyticAt ℂ
      (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
        (w.1.1, w.2)) ((0, 0), 0) :=
    hy.prod analyticAt_snd
  have hparameter : AnalyticAt ℂ
      (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
        w.1.2) ((0, 0), 0) :=
    analyticAt_snd.comp (x := ((0, 0), 0)) analyticAt_fst
  have hcoeffComp : AnalyticAt ℂ
      (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
        coeff w.1.2) ((0, 0), 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := ((0, 0), 0)) hcoeff hparameter)
  have hterm (i : ι) : AnalyticAt ℂ
      (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
        coeff w.1.2 i •
          Germ.generalFunctionalRemainder (p i) d (w.1.1, w.2))
      ((0, 0), 0) := by
    have hremainderBase :=
      Germ.analyticAt_generalFunctionalRemainder (p i) d (hp i) (hbase i)
    have hremainder : AnalyticAt ℂ
        (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
          Germ.generalFunctionalRemainder (p i) d (w.1.1, w.2))
        ((0, 0), 0) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := ((0, 0), 0)) hremainderBase hinput)
    have hcoeffCoordinate : AnalyticAt ℂ
        (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
          coeff w.1.2 i) ((0, 0), 0) := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        (AnalyticAt.comp (x := ((0, 0), 0))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (coeff 0))
          hcoeffComp)
    exact hcoeffCoordinate.smul hremainder
  have hsum (s : Finset ι) : AnalyticAt ℂ
      (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
        ∑ i ∈ s, coeff w.1.2 i •
          Germ.generalFunctionalRemainder (p i) d (w.1.1, w.2))
      ((0, 0), 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
            (0 : Germ.GeneralCoefficientSpace d)) ((0, 0), 0))
    | @insert i s hi hs =>
        simp only [Finset.sum_insert, hi, not_false_eq_true]
        exact (hterm i).add hs
  change AnalyticAt ℂ
    (fun w : (ℂ × P) × Germ.GeneralCoefficientSpace d ↦
      ∑ i, coeff w.1.2 i •
        Germ.generalFunctionalRemainder (p i) d (w.1.1, w.2))
    ((0, 0), 0)
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum Finset.univ

omit [NormedSpace ℂ P] in
/-- If one coefficient is one and all the others vanish at the base, the
finite remainder sum is minus the divisor coefficient vector. -/
theorem finiteParameterFunctionalRemainder_parameter_zero
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ) (i₀ : ι)
    (haxis : ∀ n, Germ.mixedCoefficient (p i₀) n n =
      if n = d + 1 then 1 else 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0)
    (a : Germ.GeneralCoefficientSpace d) :
    Germ.finiteParameterFunctionalRemainder p d coeff ((0, 0), a) = -a := by
  classical
  rw [Germ.finiteParameterFunctionalRemainder]
  have hsingle :
      (∑ i, coeff 0 i • Germ.generalFunctionalRemainder (p i) d (0, a)) =
        Germ.generalFunctionalRemainder (p i₀) d (0, a) := by
    rw [Finset.sum_eq_single i₀]
    · rw [hcoeffZero i₀, if_pos rfl, one_smul]
    · intro i hi hne
      rw [hcoeffZero i, if_neg hne, zero_smul]
    · simp
  rw [hsingle,
    Germ.generalFunctionalRemainder_parameter_zero (p i₀) d haxis]

/-- The coefficient derivative of the finite remainder equation is minus
the identity. -/
theorem finiteParameterFunctionalRemainder_fderiv_inr_eq_neg
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ) (i₀ : ι)
    (haxis : ∀ n, Germ.mixedCoefficient (p i₀) n n =
      if n = d + 1 then 1 else 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0)
    (hAnalytic : AnalyticAt ℂ
      (Germ.finiteParameterFunctionalRemainder p d coeff) ((0, 0), 0)) :
    fderiv ℂ (Germ.finiteParameterFunctionalRemainder p d coeff)
          ((0, 0), 0) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × P)
          (Germ.GeneralCoefficientSpace d) =
      (ContinuousLinearEquiv.neg ℂ :
        Germ.GeneralCoefficientSpace d ≃L[ℂ]
          Germ.GeneralCoefficientSpace d) := by
  let inclusion := ContinuousLinearMap.inr ℂ (ℂ × P)
    (Germ.GeneralCoefficientSpace d)
  have hcomp := fderiv_comp
    (x := (0 : Germ.GeneralCoefficientSpace d))
    hAnalytic.differentiableAt inclusion.differentiableAt
  have hfiber :
      (fun a : Germ.GeneralCoefficientSpace d ↦
        Germ.finiteParameterFunctionalRemainder p d coeff ((0, 0), a)) =
        fun a : Germ.GeneralCoefficientSpace d ↦ -a := by
    funext a
    exact Germ.finiteParameterFunctionalRemainder_parameter_zero
      p d coeff i₀ haxis hcoeffZero a
  change fderiv ℂ
    (fun a : Germ.GeneralCoefficientSpace d ↦
      Germ.finiteParameterFunctionalRemainder p d coeff ((0, 0), a)) 0 = _
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

/-- The point derivative of the finite remainder equation is invertible. -/
theorem finiteParameterFunctionalRemainder_pointDerivative_isInvertible
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ) (i₀ : ι)
    (haxis : ∀ n, Germ.mixedCoefficient (p i₀) n n =
      if n = d + 1 then 1 else 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0)
    (hAnalytic : AnalyticAt ℂ
      (Germ.finiteParameterFunctionalRemainder p d coeff) ((0, 0), 0)) :
    (fderiv ℂ (Germ.finiteParameterFunctionalRemainder p d coeff)
          ((0, 0), 0) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × P)
          (Germ.GeneralCoefficientSpace d)).IsInvertible := by
  rw [Germ.finiteParameterFunctionalRemainder_fderiv_inr_eq_neg
    p d coeff i₀ haxis hcoeffZero hAnalytic]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The implicit function theorem solves the finite remainder equation. -/
theorem exists_analytic_finiteParameterCoefficientBranch_of_base_mem
    [CompleteSpace P]
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ) (i₀ : ι)
    (hp : ∀ i, 0 < (p i).radius)
    (hbase : ∀ i, Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) (p i)).radius)
    (hcoeff : AnalyticAt ℂ coeff 0)
    (haxis : ∀ n, Germ.mixedCoefficient (p i₀) n n =
      if n = d + 1 then 1 else 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0) :
    ∃ a : ℂ × P → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ a (0, 0) ∧
      a (0, 0) = 0 ∧
      ∀ᶠ w in nhds (0, 0),
        ∑ i, coeff w.2 i •
          Germ.generalFunctionalRemainder (p i) d (w.1, a w) = 0 := by
  have hAnalytic := Germ.analyticAt_finiteParameterFunctionalRemainder
    p d coeff hp hbase hcoeff
  have hzero : Germ.finiteParameterFunctionalRemainder p d coeff
      ((0, 0), (0 : Germ.GeneralCoefficientSpace d)) = 0 := by
    rw [Germ.finiteParameterFunctionalRemainder_parameter_zero
      p d coeff i₀ haxis hcoeffZero]
    simp
  have hpoint :=
    Germ.finiteParameterFunctionalRemainder_pointDerivative_isInvertible
      p d coeff i₀ haxis hcoeffZero hAnalytic
  let a : ℂ × P → Germ.GeneralCoefficientSpace d :=
    analyticImplicitBranch
      (Germ.finiteParameterFunctionalRemainder p d coeff)
      ((0, 0), 0) hAnalytic hpoint
  have ha : AnalyticAt ℂ a (0, 0) :=
    analyticAt_analyticImplicitBranch
      (Germ.finiteParameterFunctionalRemainder p d coeff)
      ((0, 0), 0) hAnalytic hpoint
  have haZero : a (0, 0) = 0 :=
    analyticImplicitBranch_apply_base
      (Germ.finiteParameterFunctionalRemainder p d coeff)
      ((0, 0), 0) hAnalytic hpoint
  have hequation : ∀ᶠ w in nhds (0, 0),
      Germ.finiteParameterFunctionalRemainder p d coeff (w, a w) = 0 := by
    have hbranch := eventually_analyticImplicitBranch_eq
      (Germ.finiteParameterFunctionalRemainder p d coeff)
      ((0, 0), 0) hAnalytic hpoint
    simpa only [hzero] using hbranch
  refine ⟨a, ha, haZero, ?_⟩
  simpa only [Germ.finiteParameterFunctionalRemainder] using hequation

/-- Conditional division with the functional remainder written explicitly
for an arbitrary auxiliary normed parameter space. -/
theorem exists_analytic_generalDivision_withExplicitRemainder_of_base_mem
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (a : T → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) (haZero : a 0 = 0)
    (y : T → ℂ) (hy : AnalyticAt ℂ y 0) (hyZero : y 0 = 0) :
    ∃ Q : ℂ × T → ℂ,
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = Germ.generalFunctionalQuotient p d 0 0 0 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 (y z.2)) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
            ∑ i : Fin (d + 1), z.1 ^ i.1 *
              Germ.generalFunctionalRemainder p d (y z.2, a z.2) i := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  let Q : ℂ × T → ℂ := fun z ↦
    Germ.generalFunctionalQuotient p d z.1 (y z.2) (a z.2)
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hqAnalytic : AnalyticAt ℂ q.sum
      (Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d))) :=
    (q.hasFPowerSeriesOnBall hqRadius).analyticAt_of_mem hbase
  have haComp : AnalyticAt ℂ
      (fun z : ℂ × T ↦ a z.2) (0, 0) :=
    ha.comp (x := (0, 0)) analyticAt_snd
  have hyComp : AnalyticAt ℂ
      (fun z : ℂ × T ↦ y z.2) (0, 0) :=
    hy.comp (x := (0, 0)) analyticAt_snd
  have hcoefficientInput : AnalyticAt ℂ
      (fun z : ℂ × T ↦ (z.1, a z.2)) (0, 0) :=
    analyticAt_fst.prod haComp
  have hoperator : AnalyticAt ℂ
      (fun z : ℂ × T ↦
        Germ.generalDivisionOperator z.1 (a z.2)) (0, 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.analyticAt_generalDivisionOperator
          (d := d) (0, a 0)) hcoefficientInput)
  have hscalar : AnalyticAt ℂ
      (fun z : ℂ × T ↦
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) (0, 0) := by
    have hproduct := hyComp.smul
      (analyticAt_const : AnalyticAt ℂ
        (fun _ : ℂ × T ↦
          (1 : Germ.GeneralDivisionEndomorphism d)) (0, 0))
    rw [show (fun z : ℂ × T ↦
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) =
      (fun z : ℂ × T ↦ y z.2) •
        (fun _ : ℂ × T ↦
          (1 : Germ.GeneralDivisionEndomorphism d)) by rfl]
    exact hproduct
  have hinput : AnalyticAt ℂ
      (fun z : ℂ × T ↦
        (Germ.generalDivisionOperator z.1 (a z.2),
          y z.2 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) :=
    hoperator.prod hscalar
  have hinputZero :
      (Germ.generalDivisionOperator (0 : ℂ) (a (0 : T)),
        y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) =
      Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) := by
    simp [Germ.generalFunctionalInput, haZero, hyZero]
  have hstate : AnalyticAt ℂ
      (fun z : ℂ × T ↦
        q.sum
          (Germ.generalDivisionOperator z.1 (a z.2),
            y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)))
      (0, 0) := by
    have hqAt : AnalyticAt ℂ q.sum
        (Germ.generalDivisionOperator (0 : ℂ) (a (0 : T)),
          y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) := by
      rwa [hinputZero]
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hqAt hinput)
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    have hprojection : AnalyticAt ℂ
        (fun z : ℂ × T ↦ Germ.generalFunctionalQuotientOutput d
          (q.sum
            (Germ.generalDivisionOperator z.1 (a z.2),
              y z.2 • (1 : Germ.GeneralDivisionEndomorphism d))))
        (0, 0) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0, 0))
          ((Germ.generalFunctionalQuotientOutput d).analyticAt
            (q.sum
              (Germ.generalDivisionOperator (0 : ℂ) (a (0 : T)),
                y 0 • (1 : Germ.GeneralDivisionEndomorphism d)))) hstate)
    simpa only [Q, Germ.generalFunctionalQuotient,
      Germ.generalFunctionalState, q,
      Germ.generalFunctionalQuotientOutput_apply] using hprojection
  have hQZero : Q (0, 0) =
      Germ.generalFunctionalQuotient p d 0 0 0 := by
    simp [Q, hyZero, haZero]
  have hplaneInput : AnalyticAt ℂ
      (fun z : ℂ × T ↦ Germ.planePoint z.1 (y z.2)) (0, 0) := by
    have hpairAnalytic : AnalyticAt ℂ
        (fun z : ℂ × T ↦ (z.1, y z.2)) (0, 0) :=
      analyticAt_fst.prod hyComp
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt
          ((0 : ℂ), y 0)) hpairAnalytic)
  have hpEventually : ∀ᶠ z : ℂ × T in nhds (0, 0),
      Germ.planePoint z.1 (y z.2) ∈ Metric.eball 0 p.radius := by
    have hzero : Germ.planePoint (0 : ℂ) (y (0 : T)) = 0 := by
      simp [hyZero, Germ.planePoint]
    have hball : Metric.eball 0 p.radius ∈
        nhds (Germ.planePoint (0 : ℂ) (y (0 : T))) := by
      rw [hzero]
      exact Metric.eball_mem_nhds 0 hp
    exact hplaneInput.continuousAt.eventually hball
  have hinputMem : ∀ᶠ z : ℂ × T in nhds (0, 0),
      (Germ.generalDivisionOperator z.1 (a z.2),
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0 q.radius := by
    have hbase' :
        (Germ.generalDivisionOperator (0 : ℂ) (a (0 : T)),
          y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
        Metric.eball 0 q.radius := by
      rwa [hinputZero]
    exact hinput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbase')
  have hzeroInput : AnalyticAt ℂ
      (fun z : ℂ × T ↦
        (Germ.generalDivisionOperator 0 (a z.2),
          y z.2 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) := by
    have hzeroCoefficient : AnalyticAt ℂ
        (fun z : ℂ × T ↦ ((0 : ℂ), a z.2)) (0, 0) :=
      analyticAt_const.prod haComp
    have hzeroOperator : AnalyticAt ℂ
        (fun z : ℂ × T ↦
          Germ.generalDivisionOperator 0 (a z.2)) (0, 0) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0, 0))
          (Germ.analyticAt_generalDivisionOperator
            (d := d) (0, a 0)) hzeroCoefficient)
    exact hzeroOperator.prod hscalar
  have hzeroMem : ∀ᶠ z : ℂ × T in nhds (0, 0),
      (Germ.generalDivisionOperator 0 (a z.2),
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0 q.radius := by
    have hbase' :
        (Germ.generalDivisionOperator (0 : ℂ) (a (0 : T)),
          y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
        Metric.eball 0 q.radius := by
      rwa [hinputZero]
    exact hzeroInput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbase')
  refine ⟨Q, hQ, hQZero, ?_⟩
  filter_upwards [hpEventually, hinputMem, hzeroMem] with z hpz hxz hzeroz
  have hevaluation := Germ.generalDivisionStateEvaluation_functionalState
    p d z.1 (y z.2) (a z.2) hpz hxz
  have hremainder :
      (Germ.generalFunctionalState p d z.1 (a z.2) (y z.2)).2 =
        Germ.generalFunctionalRemainder p d (y z.2, a z.2) := by
    change Germ.generalRemainderProjection d
        (Germ.generalFunctionalState p d z.1 (a z.2) (y z.2)) = _
    exact Germ.generalFunctionalState_remainder_eq
      p d z.1 (y z.2) (a z.2) hxz hzeroz
  rw [Germ.generalDivisionStateEvaluation, hremainder] at hevaluation
  simpa only [Q, Germ.generalFunctionalQuotient] using hevaluation.symm

/-- Conditional preparation of a finite parameter expansion. -/
theorem exists_analytic_finiteParameterPreparation_of_base_mem
    [CompleteSpace P]
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ) (i₀ : ι)
    (hp : ∀ i, 0 < (p i).radius)
    (hbase : ∀ i, Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) (p i)).radius)
    (hcoeff : AnalyticAt ℂ coeff 0)
    (haxis : ∀ n, Germ.mixedCoefficient (p i₀) n n =
      if n = d + 1 then 1 else 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0) :
    ∃ a : ℂ × P → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × (ℂ × P) → ℂ,
      AnalyticAt ℂ a (0, 0) ∧
      a (0, 0) = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        ∑ i, coeff z.2.2 i *
            (p i).sum (Germ.planePoint z.1 z.2.1) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z := by
  obtain ⟨a, ha, haZero, hbranch⟩ :=
    Germ.exists_analytic_finiteParameterCoefficientBranch_of_base_mem
      p d coeff i₀ hp hbase hcoeff haxis hcoeffZero
  let retained : ℂ × P → ℂ := fun w ↦ w.1
  have hretained : AnalyticAt ℂ retained 0 := analyticAt_fst
  have hretainedZero : retained 0 = 0 := rfl
  choose quotient hquotient hquotientZero hdivision using fun i ↦
    Germ.exists_analytic_generalDivision_withExplicitRemainder_of_base_mem
      (p i) d (hp i) (hbase i) a ha haZero
        retained hretained hretainedZero
  let Q : ℂ × (ℂ × P) → ℂ := fun z ↦
    ∑ i, coeff z.2.2 i * quotient i z
  have hparameter : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × P) ↦ z.2.2) (0, 0) :=
    analyticAt_snd.comp (x := (0, 0)) analyticAt_snd
  have hcoeffComp : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × P) ↦ coeff z.2.2) (0, 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hcoeff hparameter)
  have hQTerm (i : ι) : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × P) ↦
        coeff z.2.2 i * quotient i z) (0, 0) := by
    have hcoordinate : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × P) ↦ coeff z.2.2 i) (0, 0) := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        (AnalyticAt.comp (x := (0, 0))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (coeff 0))
          hcoeffComp)
    exact hcoordinate.mul (hquotient i)
  have hQSum (s : Finset ι) : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × P) ↦
        ∑ i ∈ s, coeff z.2.2 i * quotient i z) (0, 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ × (ℂ × P) ↦ (0 : ℂ)) (0, 0))
    | @insert i s hi hs =>
        simp only [Finset.sum_insert, hi, not_false_eq_true]
        exact (hQTerm i).add hs
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    change AnalyticAt ℂ
      (fun z : ℂ × (ℂ × P) ↦
        ∑ i, coeff z.2.2 i * quotient i z) (0, 0)
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      hQSum Finset.univ
  have hQZero : Q (0, 0) = 1 := by
    change ∑ i, coeff 0 i * quotient i (0, 0) = 1
    rw [Finset.sum_eq_single i₀]
    · rw [hcoeffZero i₀, if_pos rfl, one_mul,
        hquotientZero i₀,
        Germ.generalFunctionalQuotient_zero (p i₀) d haxis]
    · intro i hi hne
      rw [hcoeffZero i, if_neg hne, zero_mul]
    · simp
  have hdivisionAll : ∀ᶠ z : ℂ × (ℂ × P) in nhds (0, 0),
      ∀ i, (p i).sum (Germ.planePoint z.1 z.2.1) =
        Germ.generalDivisionPolynomialValue z.1 (a z.2) * quotient i z +
          ∑ k : Fin (d + 1), z.1 ^ k.1 *
            Germ.generalFunctionalRemainder (p i) d
              (z.2.1, a z.2) k := by
    apply Filter.eventually_all.mpr
    intro i
    simpa only [retained] using hdivision i
  have hbranchPulled : ∀ᶠ z : ℂ × (ℂ × P) in nhds (0, 0),
      ∑ i, coeff z.2.2 i •
        Germ.generalFunctionalRemainder (p i) d (z.2.1, a z.2) = 0 :=
    (show Tendsto (fun z : ℂ × (ℂ × P) ↦ z.2)
      (nhds (0, 0)) (nhds (0, 0)) from continuousAt_snd).eventually hbranch
  refine ⟨a, Q, ha, haZero, hQ, hQZero, ?_⟩
  filter_upwards [hdivisionAll, hbranchPulled] with z hdiv hrem
  have hremCoordinate (k : Fin (d + 1)) :
      ∑ i, coeff z.2.2 i *
        Germ.generalFunctionalRemainder (p i) d (z.2.1, a z.2) k = 0 := by
    have hk := congrFun hrem k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hk
  have hquotientSum :
      (∑ i, coeff z.2.2 i *
        (Germ.generalDivisionPolynomialValue z.1 (a z.2) *
          quotient i z)) =
      Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z := by
    rw [show Q z = ∑ i, coeff z.2.2 i * quotient i z by rfl,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hremainderSum :
      (∑ i, coeff z.2.2 i *
        (∑ k : Fin (d + 1), z.1 ^ k.1 *
          Germ.generalFunctionalRemainder (p i) d
            (z.2.1, a z.2) k)) = 0 := by
    calc
      (∑ i, coeff z.2.2 i *
          (∑ k : Fin (d + 1), z.1 ^ k.1 *
            Germ.generalFunctionalRemainder (p i) d
              (z.2.1, a z.2) k)) =
          ∑ i, ∑ k : Fin (d + 1), coeff z.2.2 i *
            (z.1 ^ k.1 * Germ.generalFunctionalRemainder (p i) d
              (z.2.1, a z.2) k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ k : Fin (d + 1), ∑ i, coeff z.2.2 i *
            (z.1 ^ k.1 * Germ.generalFunctionalRemainder (p i) d
              (z.2.1, a z.2) k) := Finset.sum_comm
      _ = ∑ k : Fin (d + 1), z.1 ^ k.1 *
            (∑ i, coeff z.2.2 i *
              Germ.generalFunctionalRemainder (p i) d
                (z.2.1, a z.2) k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by simp only [hremCoordinate, mul_zero, Finset.sum_const_zero]
  calc
    ∑ i, coeff z.2.2 i *
        (p i).sum (Germ.planePoint z.1 z.2.1) =
      ∑ i, coeff z.2.2 i *
        (Germ.generalDivisionPolynomialValue z.1 (a z.2) * quotient i z +
          ∑ k : Fin (d + 1), z.1 ^ k.1 *
            Germ.generalFunctionalRemainder (p i) d
              (z.2.1, a z.2) k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdiv i]
    _ = (∑ i, coeff z.2.2 i *
          (Germ.generalDivisionPolynomialValue z.1 (a z.2) * quotient i z)) +
        ∑ i, coeff z.2.2 i *
          (∑ k : Fin (d + 1), z.1 ^ k.1 *
            Germ.generalFunctionalRemainder (p i) d
              (z.2.1, a z.2) k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z := by
      rw [hquotientSum, hremainderSum, add_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- A common radial scale places every series in a finite family inside its
division convergence ball. -/
theorem exists_radialScale_generalFunctionalInput_mem_finite
    [Finite ι]
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (i₀ : ι) (hp : ∀ i, 0 < (p i).radius) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ i,
      Germ.generalFunctionalInput d
          (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d)
            (Germ.radiallyScaledGeneralSeries (p i) d c)).radius := by
  let _ := Fintype.ofFinite ι
  let q := fun i : ι ↦
    Germ.banachAlgebraExtensionSeries
      (A := Germ.GeneralDivisionEndomorphism d) (p i)
  let base := Germ.generalFunctionalInput d
    (0, (0 : Germ.GeneralCoefficientSpace d))
  have hindices : (Finset.univ : Finset ι).Nonempty :=
    ⟨i₀, Finset.mem_univ i₀⟩
  let radiusMin : ℝ≥0∞ :=
    Finset.univ.inf' hindices fun i ↦ (q i).radius
  have hqRadius (i : ι) : 0 < (q i).radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos (p i) (hp i)
  have hminRadius : 0 < radiusMin := by
    change 0 < Finset.univ.inf' hindices (fun i ↦ (q i).radius)
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact hqRadius i
  obtain ⟨delta, hdelta, hdeltaSmall⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt
      (a := ((‖base‖₊ + 1 : ℝ≥0) : ℝ≥0∞))
      (b := radiusMin) (by simp) hminRadius.ne'
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
  have hproductMin : ‖base‖ₑ * ‖scale‖ₑ < radiusMin := by
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
      _ < radiusMin := hdeltaSmall
  refine ⟨c, hc, ?_⟩
  intro i
  have hminLe : radiusMin ≤ (q i).radius := by
    exact Finset.inf'_le (fun j ↦ (q j).radius) (Finset.mem_univ i)
  have hproduct : ‖base‖ₑ * ‖scale‖ₑ < (q i).radius :=
    hproductMin.trans_le hminLe
  have hdiv : ‖base‖ₑ < (q i).radius / ‖scale‖ₑ := by
    rw [ENNReal.lt_div_iff_mul_lt]
    · exact hproduct
    · exact Or.inr enorm_ne_top
    · exact Or.inl enorm_ne_top
  have hradius : ‖base‖ₑ <
      (Germ.banachAlgebraExtensionSeries
        (A := Germ.GeneralDivisionEndomorphism d)
        (Germ.radiallyScaledGeneralSeries (p i) d c)).radius :=
    hdiv.trans_le
      (Germ.div_le_radius_banachAlgebraExtensionSeries_radiallyScaledGeneral
        (p i) d c hc)
  exact mem_eball_zero_iff.2 hradius

/-- Preparation of a finite parameter expansion without a convergence ball
hypothesis. -/
theorem exists_analytic_finiteParameterPreparation
    [CompleteSpace P]
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ) (i₀ : ι)
    (hp : ∀ i, 0 < (p i).radius)
    (hcoeff : AnalyticAt ℂ coeff 0)
    (haxis : ∀ n, Germ.mixedCoefficient (p i₀) n n =
      if n = d + 1 then 1 else 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0) :
    ∃ b : ℂ × P → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × (ℂ × P) → ℂ,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        ∑ i, coeff z.2.2 i *
            (p i).sum (Germ.planePoint z.1 z.2.1) =
          Germ.generalDivisionPolynomialValue z.1 (b z.2) * Q z := by
  obtain ⟨c, hc, hbase⟩ :=
    Germ.exists_radialScale_generalFunctionalInput_mem_finite
      p d i₀ hp
  let pScaled : ι → FormalMultilinearSeries ℂ (Source 2) ℂ :=
    fun i ↦ Germ.radiallyScaledGeneralSeries (p i) d c
  have hpScaled (i : ι) : 0 < (pScaled i).radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos (p i) d c (hp i) hc
  have haxisScaled : ∀ n, Germ.mixedCoefficient (pScaled i₀) n n =
      if n = d + 1 then 1 else 0 :=
    Germ.radiallyScaledGeneralSeries_exact_axis (p i₀) d c hc haxis
  obtain ⟨a, QScaled, ha, haZero, hQScaled, hQScaledZero,
      hfactorScaled⟩ :=
    Germ.exists_analytic_finiteParameterPreparation_of_base_mem
      pScaled d coeff i₀ hpScaled hbase hcoeff haxisScaled hcoeffZero
  let inverseScalar : ℂ → ℂ := fun x ↦ c⁻¹ * x
  let inverseParameter : ℂ × P → ℂ × P := fun w ↦
    (inverseScalar w.1, w.2)
  let inverseInput : ℂ × (ℂ × P) → ℂ × (ℂ × P) :=
    fun z ↦ (inverseScalar z.1, inverseParameter z.2)
  let b : ℂ × P → Germ.GeneralCoefficientSpace d := fun w i ↦
    c ^ (d + 1 - i.1) * a (inverseParameter w) i
  let Q : ℂ × (ℂ × P) → ℂ := fun z ↦
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
  have hplaneInput : AnalyticAt ℂ
      (fun z : ℂ × (ℂ × P) ↦
        Germ.planePoint z.1 z.2.1) (0, 0) := by
    have hretained : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × P) ↦ z.2.1) (0, 0) :=
      analyticAt_fst.comp (x := (0, 0)) analyticAt_snd
    have hpair : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × P) ↦ (z.1, z.2.1)) (0, 0) :=
      analyticAt_fst.prod hretained
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt (0, 0)) hpair)
  have hsumInput (i : ι) :
      ∀ᶠ z : ℂ × (ℂ × P) in nhds (0, 0),
        (pScaled i).sum (Germ.planePoint z.1 z.2.1) =
          (c ^ (d + 1))⁻¹ *
            (p i).sum (c • Germ.planePoint z.1 z.2.1) := by
    have hsumScaled :=
      Germ.eventually_radiallyScaledGeneralSeries_sum_eq
        (p i) d c (hp i) hc
    have htendsto := hplaneInput.continuousAt
    change Tendsto (fun z : ℂ × (ℂ × P) ↦
      Germ.planePoint z.1 z.2.1) (nhds (0, 0))
        (nhds (Germ.planePoint (0 : ℂ) (0 : ℂ))) at htendsto
    have hzero : Germ.planePoint (0 : ℂ) (0 : ℂ) = 0 := by
      simp [Germ.planePoint]
    rw [hzero] at htendsto
    exact htendsto.eventually hsumScaled
  have hsumAtInverseAll :
      ∀ᶠ z : ℂ × (ℂ × P) in nhds (0, 0), ∀ i,
        (pScaled i).sum (Germ.planePoint (inverseInput z).1
            (inverseInput z).2.1) =
          (c ^ (d + 1))⁻¹ *
            (p i).sum (c • Germ.planePoint (inverseInput z).1
              (inverseInput z).2.1) := by
    apply Filter.eventually_all.mpr
    intro i
    exact hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hsumInput i)
  have hfactorAtInverse :
      ∀ᶠ z : ℂ × (ℂ × P) in nhds (0, 0),
        ∑ i, coeff (inverseInput z).2.2 i *
            (pScaled i).sum (Germ.planePoint (inverseInput z).1
              (inverseInput z).2.1) =
          Germ.generalDivisionPolynomialValue (inverseInput z).1
              (a (inverseInput z).2) * QScaled (inverseInput z) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hfactorScaled)
  refine ⟨b, Q, hb, hbZero, hQ, hQZero, ?_⟩
  filter_upwards [hsumAtInverseAll, hfactorAtInverse] with z hsum hfactor
  have hsourceScale : c • Germ.planePoint
      (inverseInput z).1 (inverseInput z).2.1 =
      Germ.planePoint z.1 z.2.1 := by
    ext i
    fin_cases i <;>
      simp [inverseInput, inverseParameter, inverseScalar,
        Germ.planePoint, hc]
  have hauxiliary : (inverseInput z).2.2 = z.2.2 := rfl
  have hscaled :
      ∑ i, coeff z.2.2 i *
          ((c ^ (d + 1))⁻¹ *
            (p i).sum (Germ.planePoint z.1 z.2.1)) =
        Germ.generalDivisionPolynomialValue (inverseInput z).1
          (a (inverseInput z).2) * QScaled (inverseInput z) := by
    calc
      ∑ i, coeff z.2.2 i *
          ((c ^ (d + 1))⁻¹ *
            (p i).sum (Germ.planePoint z.1 z.2.1)) =
        ∑ i, coeff (inverseInput z).2.2 i *
          (pScaled i).sum (Germ.planePoint (inverseInput z).1
            (inverseInput z).2.1) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hauxiliary, hsum i, hsourceScale]
      _ = Germ.generalDivisionPolynomialValue (inverseInput z).1
          (a (inverseInput z).2) * QScaled (inverseInput z) := hfactor
  calc
    ∑ i, coeff z.2.2 i *
        (p i).sum (Germ.planePoint z.1 z.2.1) =
      c ^ (d + 1) *
        (∑ i, coeff z.2.2 i *
          ((c ^ (d + 1))⁻¹ *
            (p i).sum (Germ.planePoint z.1 z.2.1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
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

/-- Eventual vanishing of a finite parameter expansion gives a monic
relation for the chosen scalar source function. -/
theorem exists_analytic_monicRelation_of_finiteParameterVanishing
    [CompleteSpace P]
    (p : ι → FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (coeff : P → ι → ℂ) (i₀ : ι)
    (hp : ∀ i, 0 < (p i).radius)
    (hcoeff : AnalyticAt ℂ coeff 0)
    (haxis : ∀ n, Germ.mixedCoefficient (p i₀) n n =
      if n = d + 1 then 1 else 0)
    (hcoeffZero : ∀ i, coeff 0 i = if i = i₀ then 1 else 0)
    (x y : Source 2 → ℂ) (parameter : Source 2 → P)
    (hx : AnalyticAt ℂ x 0) (hy : AnalyticAt ℂ y 0)
    (hparameter : AnalyticAt ℂ parameter 0)
    (hxZero : x 0 = 0) (hyZero : y 0 = 0)
    (hparameterZero : parameter 0 = 0)
    (hvanish : ∀ᶠ z : Source 2 in nhds 0,
      ∑ i, coeff (parameter z) i *
        (p i).sum (Germ.planePoint (x z) (y z)) = 0) :
    ∃ b : ℂ × P → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (x z)
          (b (y z, parameter z)) = 0 := by
  obtain ⟨b, Q, hb, hbZero, hQ, hQZero, hpreparation⟩ :=
    Germ.exists_analytic_finiteParameterPreparation
      p d coeff i₀ hp hcoeff haxis hcoeffZero
  let substitution : Source 2 → ℂ × (ℂ × P) := fun z ↦
    (x z, (y z, parameter z))
  have hsubstitution : AnalyticAt ℂ substitution 0 :=
    hx.prod (hy.prod hparameter)
  have hsubstitutionZero : substitution 0 = (0, 0) := by
    simp [substitution, hxZero, hyZero, hparameterZero]
  have hpreparationSubstituted : ∀ᶠ z : Source 2 in nhds 0,
      ∑ i, coeff (parameter z) i *
          (p i).sum (Germ.planePoint (x z) (y z)) =
        Germ.generalDivisionPolynomialValue (x z)
          (b (y z, parameter z)) * Q (substitution z) := by
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
  filter_upwards [hpreparationSubstituted, hvanish, hQEventually] with
      z hfactor hz hQz
  rw [hz] at hfactor
  exact (mul_eq_zero.mp hfactor.symm).resolve_right hQz

end Germ

end OnLeConjecture.Analytic
