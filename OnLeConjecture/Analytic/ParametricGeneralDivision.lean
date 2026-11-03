/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralWeierstrassDivision

/-!
# Weierstrass division with auxiliary parameters

The finite division state depends analytically on the coordinate retained as
a parameter and on every lower coefficient of the divisor. Consequently the
coefficient vector may depend on an arbitrary finite dimensional analytic
parameter. This form of division is needed when the constant coefficient of
the divisor contains a target coordinate.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Conditional Weierstrass division when the retained coordinate and the
lower coefficients depend analytically on an auxiliary parameter. -/
theorem exists_analytic_generalDivision_withParameters_of_base_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (a : P → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) (haZero : a 0 = 0)
    (y : P → ℂ) (hy : AnalyticAt ℂ y 0) (hyZero : y 0 = 0) :
    ∃ Q : ℂ × P → ℂ,
      ∃ R : P → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ Q (0, 0) ∧
      AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 (y z.2)) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
            ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  let Q : ℂ × P → ℂ := fun z ↦
    Germ.generalFunctionalQuotient p d z.1 (y z.2) (a z.2)
  let R : P → Germ.GeneralCoefficientSpace d := fun w ↦
    Germ.generalFunctionalRemainder p d (y w, a w)
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hqAnalytic : AnalyticAt ℂ q.sum
      (Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d))) :=
    (q.hasFPowerSeriesOnBall hqRadius).analyticAt_of_mem hbase
  have haComp : AnalyticAt ℂ
      (fun z : ℂ × P ↦ a z.2) (0, 0) :=
    ha.comp (x := (0, 0)) analyticAt_snd
  have hyComp : AnalyticAt ℂ
      (fun z : ℂ × P ↦ y z.2) (0, 0) :=
    hy.comp (x := (0, 0)) analyticAt_snd
  have hcoefficientInput : AnalyticAt ℂ
      (fun z : ℂ × P ↦ (z.1, a z.2)) (0, 0) :=
    analyticAt_fst.prod haComp
  have hoperator : AnalyticAt ℂ
      (fun z : ℂ × P ↦
        Germ.generalDivisionOperator z.1 (a z.2)) (0, 0) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.analyticAt_generalDivisionOperator
          (d := d) (0, a 0)) hcoefficientInput)
  have hscalar : AnalyticAt ℂ
      (fun z : ℂ × P ↦
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) (0, 0) := by
    have hproduct := hyComp.smul
      (analyticAt_const : AnalyticAt ℂ
        (fun _ : ℂ × P ↦
          (1 : Germ.GeneralDivisionEndomorphism d)) (0, 0))
    rw [show (fun z : ℂ × P ↦
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) =
      (fun z : ℂ × P ↦ y z.2) •
        (fun _ : ℂ × P ↦
          (1 : Germ.GeneralDivisionEndomorphism d)) by rfl]
    exact hproduct
  have hinput : AnalyticAt ℂ
      (fun z : ℂ × P ↦
        (Germ.generalDivisionOperator z.1 (a z.2),
          y z.2 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) :=
    hoperator.prod hscalar
  have hinputZero :
      (Germ.generalDivisionOperator (0 : ℂ) (a (0 : P)),
        y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) =
      Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) := by
    simp [Germ.generalFunctionalInput, haZero, hyZero]
  have hstate : AnalyticAt ℂ
      (fun z : ℂ × P ↦
        q.sum
          (Germ.generalDivisionOperator z.1 (a z.2),
            y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)))
      (0, 0) := by
    have hqAt : AnalyticAt ℂ q.sum
        (Germ.generalDivisionOperator (0 : ℂ) (a (0 : P)),
          y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) := by
      rwa [hinputZero]
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hqAt hinput)
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    have hprojection : AnalyticAt ℂ
        (fun z : ℂ × P ↦ Germ.generalFunctionalQuotientOutput d
          (q.sum
            (Germ.generalDivisionOperator z.1 (a z.2),
              y z.2 • (1 : Germ.GeneralDivisionEndomorphism d))))
        (0, 0) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0, 0))
          ((Germ.generalFunctionalQuotientOutput d).analyticAt
            (q.sum
              (Germ.generalDivisionOperator (0 : ℂ) (a (0 : P)),
                y 0 • (1 : Germ.GeneralDivisionEndomorphism d)))) hstate)
    simpa only [Q, Germ.generalFunctionalQuotient,
      Germ.generalFunctionalState, q,
      Germ.generalFunctionalQuotientOutput_apply] using hprojection
  have hpair : AnalyticAt ℂ
      (fun w : P ↦ (y w, a w)) 0 := hy.prod ha
  have hRBase :=
    Germ.analyticAt_generalFunctionalRemainder p d hp hbase
  have hRAt : AnalyticAt ℂ (Germ.generalFunctionalRemainder p d)
      (y 0, a 0) := by
    simpa only [hyZero, haZero] using hRBase
  have hR : AnalyticAt ℂ R 0 := by
    simpa only [R, Function.comp_def] using
      (AnalyticAt.comp (x := 0) hRAt hpair)
  have hplaneInput : AnalyticAt ℂ
      (fun z : ℂ × P ↦ Germ.planePoint z.1 (y z.2)) (0, 0) := by
    have hpairAnalytic : AnalyticAt ℂ
        (fun z : ℂ × P ↦ (z.1, y z.2)) (0, 0) :=
      analyticAt_fst.prod hyComp
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0, 0))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt
          ((0 : ℂ), y 0)) hpairAnalytic)
  have hpEventually : ∀ᶠ z : ℂ × P in nhds (0, 0),
      Germ.planePoint z.1 (y z.2) ∈ Metric.eball 0 p.radius := by
    have hzero : Germ.planePoint (0 : ℂ) (y (0 : P)) = 0 := by
      simp [hyZero, Germ.planePoint]
    have hball : Metric.eball 0 p.radius ∈
        nhds (Germ.planePoint (0 : ℂ) (y (0 : P))) := by
      rw [hzero]
      exact Metric.eball_mem_nhds 0 hp
    exact hplaneInput.continuousAt.eventually hball
  have hinputMem : ∀ᶠ z : ℂ × P in nhds (0, 0),
      (Germ.generalDivisionOperator z.1 (a z.2),
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0 q.radius := by
    have hbase' :
        (Germ.generalDivisionOperator (0 : ℂ) (a (0 : P)),
          y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
        Metric.eball 0 q.radius := by
      rwa [hinputZero]
    exact hinput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbase')
  have hzeroInput : AnalyticAt ℂ
      (fun z : ℂ × P ↦
        (Germ.generalDivisionOperator 0 (a z.2),
          y z.2 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) := by
    have hzeroCoefficient : AnalyticAt ℂ
        (fun z : ℂ × P ↦ ((0 : ℂ), a z.2)) (0, 0) :=
      analyticAt_const.prod haComp
    have hzeroOperator : AnalyticAt ℂ
        (fun z : ℂ × P ↦
          Germ.generalDivisionOperator 0 (a z.2)) (0, 0) := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0, 0))
          (Germ.analyticAt_generalDivisionOperator
            (d := d) (0, a 0)) hzeroCoefficient)
    exact hzeroOperator.prod hscalar
  have hzeroMem : ∀ᶠ z : ℂ × P in nhds (0, 0),
      (Germ.generalDivisionOperator 0 (a z.2),
        y z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0 q.radius := by
    have hbase' :
        (Germ.generalDivisionOperator (0 : ℂ) (a (0 : P)),
          y 0 • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
        Metric.eball 0 q.radius := by
      rwa [hinputZero]
    exact hzeroInput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbase')
  refine ⟨Q, R, hQ, hR, ?_⟩
  filter_upwards [hpEventually, hinputMem, hzeroMem] with z hpz hxz hzeroz
  have hevaluation := Germ.generalDivisionStateEvaluation_functionalState
    p d z.1 (y z.2) (a z.2) hpz hxz
  have hremainder :
      (Germ.generalFunctionalState p d z.1 (a z.2) (y z.2)).2 =
        R z.2 := by
    change Germ.generalRemainderProjection d
        (Germ.generalFunctionalState p d z.1 (a z.2) (y z.2)) =
      R z.2
    simpa only [R] using Germ.generalFunctionalState_remainder_eq
      p d z.1 (y z.2) (a z.2) hxz hzeroz
  rw [Germ.generalDivisionStateEvaluation, hremainder] at hevaluation
  simpa only [Q, Germ.generalFunctionalQuotient] using hevaluation.symm

/-- Radial normalization of a coefficient vector with two auxiliary
parameters. -/
@[expose] noncomputable def radiallyScaledTwoParameterCoefficients
    (d : ℕ) (c : ℂ)
    (a : ℂ × ℂ → Germ.GeneralCoefficientSpace d) :
    ℂ × ℂ → Germ.GeneralCoefficientSpace d := fun w i ↦
  (c ^ (d + 1 - i.1))⁻¹ * a (c * w.1, c * w.2) i

/-- Scaling back the two parameter coefficient vector recovers the original
coefficient vector. -/
theorem pow_mul_radiallyScaledTwoParameterCoefficients_inverse
    (d : ℕ) (c : ℂ)
    (a : ℂ × ℂ → Germ.GeneralCoefficientSpace d) (hc : c ≠ 0)
    (w : ℂ × ℂ) :
    (fun i ↦ c ^ (d + 1 - i.1) *
      Germ.radiallyScaledTwoParameterCoefficients d c a
        (c⁻¹ * w.1, c⁻¹ * w.2) i) = a w := by
  funext i
  simp [Germ.radiallyScaledTwoParameterCoefficients, hc]

/-- Radial normalization preserves analytic dependence on two auxiliary
parameters. -/
theorem analyticAt_radiallyScaledTwoParameterCoefficients
    (d : ℕ) (c : ℂ)
    (a : ℂ × ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a (0, 0)) :
    AnalyticAt ℂ
      (Germ.radiallyScaledTwoParameterCoefficients d c a) (0, 0) := by
  have hscale : AnalyticAt ℂ
      (fun w : ℂ × ℂ ↦ (c * w.1, c * w.2)) (0, 0) := by
    exact (analyticAt_const.mul analyticAt_fst).prod
      (analyticAt_const.mul analyticAt_snd)
  have haAtScaled : AnalyticAt ℂ a
      (c * (0 : ℂ), c * (0 : ℂ)) := by
    simpa only [mul_zero] using ha
  have haComp : AnalyticAt ℂ
      (fun w : ℂ × ℂ ↦ a (c * w.1, c * w.2)) (0, 0) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) haAtScaled hscale)
  apply AnalyticAt.pi
  intro i
  have hcoordinate : AnalyticAt ℂ
      (fun w : ℂ × ℂ ↦ a (c * w.1, c * w.2) i) (0, 0) := by
    have hcomp := AnalyticAt.comp (x := (0, 0))
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
        (a (c * 0, c * 0))) haComp
    have heq :
        (ContinuousLinearMap.proj (R := ℂ) i) ∘
            (fun w : ℂ × ℂ ↦ a (c * w.1, c * w.2)) =
          fun w : ℂ × ℂ ↦ a (c * w.1, c * w.2) i := by
      rfl
    rwa [heq] at hcomp
  exact analyticAt_const.mul hcoordinate

@[simp]
theorem radiallyScaledTwoParameterCoefficients_zero
    (d : ℕ) (c : ℂ)
    (a : ℂ × ℂ → Germ.GeneralCoefficientSpace d)
    (haZero : a (0, 0) = 0) :
    Germ.radiallyScaledTwoParameterCoefficients d c a (0, 0) = 0 := by
  funext i
  simp [Germ.radiallyScaledTwoParameterCoefficients, haZero]

/-- Weierstrass division with two auxiliary parameters. The first auxiliary
coordinate is the retained source coordinate. -/
theorem exists_analytic_generalDivision_withTwoParameters
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (a : ℂ × ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a (0, 0)) (haZero : a (0, 0) = 0) :
    ∃ Q : ℂ × (ℂ × ℂ) → ℂ,
      ∃ R : ℂ × ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ Q (0, 0) ∧
      AnalyticAt ℂ R (0, 0) ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2.1) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
            ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
  obtain ⟨c, hc, hbase⟩ :=
    Germ.exists_radialScale_generalFunctionalInput_mem p d hp
  let pScaled := Germ.radiallyScaledGeneralSeries p d c
  let aScaled :=
    Germ.radiallyScaledTwoParameterCoefficients d c a
  have hpScaled : 0 < pScaled.radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos p d c hp hc
  have haScaled : AnalyticAt ℂ aScaled (0, 0) :=
    Germ.analyticAt_radiallyScaledTwoParameterCoefficients d c a ha
  have haScaledZero : aScaled (0, 0) = 0 :=
    Germ.radiallyScaledTwoParameterCoefficients_zero d c a haZero
  obtain ⟨QScaled, RScaled, hQScaled, hRScaled, hdivisionScaled⟩ :=
    Germ.exists_analytic_generalDivision_withParameters_of_base_mem
      pScaled d hpScaled hbase aScaled haScaled haScaledZero
        (fun w : ℂ × ℂ ↦ w.1) analyticAt_fst rfl
  let inverseScalar : ℂ → ℂ := fun x ↦ c⁻¹ * x
  let inverseParameter : ℂ × ℂ → ℂ × ℂ := fun w ↦
    (inverseScalar w.1, inverseScalar w.2)
  let inverseInput : ℂ × (ℂ × ℂ) → ℂ × (ℂ × ℂ) :=
    fun z ↦ (inverseScalar z.1, inverseParameter z.2)
  let Q : ℂ × (ℂ × ℂ) → ℂ := fun z ↦
    QScaled (inverseInput z)
  let R : ℂ × ℂ → Germ.GeneralCoefficientSpace d := fun w i ↦
    c ^ (d + 1 - i.1) * RScaled (inverseParameter w) i
  have hinverseScalar : AnalyticAt ℂ inverseScalar 0 := by
    dsimp only [inverseScalar]
    fun_prop
  have hinverseParameter : AnalyticAt ℂ inverseParameter (0, 0) := by
    exact (hinverseScalar.comp (x := (0, 0)) analyticAt_fst).prod
      (hinverseScalar.comp (x := (0, 0)) analyticAt_snd)
  have hinverseInput : AnalyticAt ℂ inverseInput (0, 0) := by
    have hfirst := hinverseScalar.comp
      (x := ((0 : ℂ), ((0 : ℂ), (0 : ℂ)))) analyticAt_fst
    have hsecond := hinverseParameter.comp
      (x := ((0 : ℂ), ((0 : ℂ), (0 : ℂ)))) analyticAt_snd
    exact hfirst.prod hsecond
  have hinverseParameterZero : inverseParameter (0, 0) = (0, 0) := by
    simp [inverseParameter, inverseScalar]
  have hinverseInputZero : inverseInput (0, 0) = (0, 0) := by
    simp [inverseInput, inverseParameter, inverseScalar]
  have hQScaledAt : AnalyticAt ℂ QScaled (inverseInput (0, 0)) := by
    simpa only [hinverseInputZero] using hQScaled
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    simpa only [Q, Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hQScaledAt hinverseInput)
  have hRScaledAt : AnalyticAt ℂ RScaled
      (inverseParameter (0, 0)) := by
    rw [hinverseParameterZero]
    exact hRScaled
  have hRComp : AnalyticAt ℂ
      (fun w ↦ RScaled (inverseParameter w)) (0, 0) := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hRScaledAt hinverseParameter)
  have hR : AnalyticAt ℂ R (0, 0) := by
    apply AnalyticAt.pi
    intro i
    have hcoordinate : AnalyticAt ℂ
        (fun w ↦ RScaled (inverseParameter w) i) (0, 0) := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0, 0))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
            (RScaled (inverseParameter (0, 0)))) hRComp)
    exact analyticAt_const.mul hcoordinate
  have hsumScaled :=
    Germ.eventually_radiallyScaledGeneralSeries_sum_eq p d c hp hc
  have hplaneTendsto : Tendsto
      (fun z : ℂ × (ℂ × ℂ) ↦ Germ.planePoint z.1 z.2.1)
      (nhds (0, 0)) (nhds 0) := by
    have hanalytic : AnalyticAt ℂ
        (fun z : ℂ × (ℂ × ℂ) ↦
          Germ.planePoint z.1 z.2.1) (0, 0) := by
      have hpair : AnalyticAt ℂ
          (fun z : ℂ × (ℂ × ℂ) ↦ (z.1, z.2.1)) (0, 0) :=
        analyticAt_fst.prod (analyticAt_fst.comp
          (x := ((0 : ℂ), ((0 : ℂ), (0 : ℂ)))) analyticAt_snd)
      simpa only [Function.comp_def,
        Germ.generalPlanePointContinuousLinearMap_apply] using
        (AnalyticAt.comp (x := (0, 0))
          (Germ.generalPlanePointContinuousLinearMap.analyticAt (0, 0)) hpair)
    have hcontinuous := hanalytic.continuousAt
    change Tendsto (fun z : ℂ × (ℂ × ℂ) ↦
      Germ.planePoint z.1 z.2.1) (nhds (0, 0))
        (nhds (Germ.planePoint (0 : ℂ) (0 : ℂ))) at hcontinuous
    simpa [Germ.planePoint] using hcontinuous
  have hsumInput : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum (Germ.planePoint z.1 z.2.1) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c • Germ.planePoint z.1 z.2.1) :=
    hplaneTendsto.eventually hsumScaled
  have hsumAtInverse : ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum
          (Germ.planePoint (inverseInput z).1 (inverseInput z).2.1) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c •
            Germ.planePoint (inverseInput z).1 (inverseInput z).2.1) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hsumInput)
  have hdivisionAtInverse :
      ∀ᶠ z : ℂ × (ℂ × ℂ) in nhds (0, 0),
      pScaled.sum
          (Germ.planePoint (inverseInput z).1 (inverseInput z).2.1) =
        Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2) * QScaled (inverseInput z) +
          ∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hdivisionScaled)
  refine ⟨Q, R, hQ, hR, ?_⟩
  filter_upwards [hsumAtInverse, hdivisionAtInverse] with z hsum hdivision
  have hsourceScale : c • Germ.planePoint
      (inverseInput z).1 (inverseInput z).2.1 =
      Germ.planePoint z.1 z.2.1 := by
    ext i
    fin_cases i <;>
      simp [inverseInput, inverseParameter, inverseScalar,
        Germ.planePoint, hc]
  have hscaled : (c ^ (d + 1))⁻¹ *
      p.sum (Germ.planePoint z.1 z.2.1) =
        Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2) * QScaled (inverseInput z) +
          ∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i := by
    rw [← hdivision, hsum, hsourceScale]
  have hpolynomial : c ^ (d + 1) *
      Germ.generalDivisionPolynomialValue (inverseInput z).1
        (aScaled (inverseInput z).2) =
      Germ.generalDivisionPolynomialValue z.1 (a z.2) := by
    rw [show (inverseInput z).1 = inverseScalar z.1 by rfl]
    rw [Germ.pow_mul_generalDivisionPolynomialValue_inverse
      d c z.1 (aScaled (inverseInput z).2) hc]
    congr 1
    simpa only [inverseInput] using
      Germ.pow_mul_radiallyScaledTwoParameterCoefficients_inverse
        d c a hc z.2
  have hremainder : c ^ (d + 1) *
      (∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
          RScaled (inverseInput z).2 i) =
      ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
    simpa only [inverseInput, inverseParameter, R] using
      Germ.pow_mul_generalRemainderSum_inverse d c z.1
        (RScaled (inverseParameter z.2)) hc
  calc
    p.sum (Germ.planePoint z.1 z.2.1) =
        c ^ (d + 1) * ((c ^ (d + 1))⁻¹ *
          p.sum (Germ.planePoint z.1 z.2.1)) := by
      rw [← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero (d + 1) hc), one_mul]
    _ = c ^ (d + 1) *
        (Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2) * QScaled (inverseInput z) +
          ∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i) := by
      rw [hscaled]
    _ = (c ^ (d + 1) *
          Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2)) * QScaled (inverseInput z) +
        c ^ (d + 1) *
          (∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i) := by
      ring
    _ = Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
          ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
      rw [hpolynomial, hremainder]

/-- Radial normalization of a coefficient vector on an auxiliary normed
space. -/
@[expose] noncomputable def radiallyScaledParameterCoefficients
    (d : ℕ) (c : ℂ)
    (a : P → Germ.GeneralCoefficientSpace d) :
    P → Germ.GeneralCoefficientSpace d := fun w i ↦
  (c ^ (d + 1 - i.1))⁻¹ * a (c • w) i

/-- Scaling back a coefficient vector on an auxiliary normed space recovers
the original vector. -/
theorem pow_mul_radiallyScaledParameterCoefficients_inverse
    (d : ℕ) (c : ℂ)
    (a : P → Germ.GeneralCoefficientSpace d) (hc : c ≠ 0)
    (w : P) :
    (fun i ↦ c ^ (d + 1 - i.1) *
      Germ.radiallyScaledParameterCoefficients d c a (c⁻¹ • w) i) =
        a w := by
  funext i
  simp [Germ.radiallyScaledParameterCoefficients, smul_smul, hc]

/-- Radial normalization preserves analytic dependence on an auxiliary
normed space. -/
theorem analyticAt_radiallyScaledParameterCoefficients
    (d : ℕ) (c : ℂ)
    (a : P → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ
      (Germ.radiallyScaledParameterCoefficients d c a) 0 := by
  have hscale : AnalyticAt ℂ (fun w : P ↦ c • w) 0 := by
    fun_prop
  have haAtScaled : AnalyticAt ℂ a (c • (0 : P)) := by
    simpa only [smul_zero] using ha
  have haComp : AnalyticAt ℂ (fun w : P ↦ a (c • w)) 0 := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0 : P)) haAtScaled hscale)
  apply AnalyticAt.pi
  intro i
  have hcoordinate : AnalyticAt ℂ (fun w : P ↦ a (c • w) i) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : P))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (a (c • 0)))
        haComp)
  exact analyticAt_const.mul hcoordinate

@[simp]
theorem radiallyScaledParameterCoefficients_zero
    (d : ℕ) (c : ℂ)
    (a : P → Germ.GeneralCoefficientSpace d)
    (haZero : a 0 = 0) :
    Germ.radiallyScaledParameterCoefficients d c a 0 = 0 := by
  funext i
  simp [Germ.radiallyScaledParameterCoefficients, haZero]

/-- Weierstrass division with an auxiliary normed parameter space. A
continuous linear functional selects the retained coordinate of the
dividend. -/
theorem exists_analytic_generalDivision_withLinearParameter
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (a : P → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) (haZero : a 0 = 0)
    (y : P →L[ℂ] ℂ) :
    ∃ Q : ℂ × P → ℂ,
      ∃ R : P → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ Q (0, 0) ∧
      AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 (y z.2)) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
            ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
  obtain ⟨c, hc, hbase⟩ :=
    Germ.exists_radialScale_generalFunctionalInput_mem p d hp
  let pScaled := Germ.radiallyScaledGeneralSeries p d c
  let aScaled := Germ.radiallyScaledParameterCoefficients d c a
  have hpScaled : 0 < pScaled.radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos p d c hp hc
  have haScaled : AnalyticAt ℂ aScaled 0 :=
    Germ.analyticAt_radiallyScaledParameterCoefficients d c a ha
  have haScaledZero : aScaled 0 = 0 :=
    Germ.radiallyScaledParameterCoefficients_zero d c a haZero
  obtain ⟨QScaled, RScaled, hQScaled, hRScaled, hdivisionScaled⟩ :=
    Germ.exists_analytic_generalDivision_withParameters_of_base_mem
      pScaled d hpScaled hbase aScaled haScaled haScaledZero
        y (y.analyticAt 0) y.map_zero
  let inverseScalar : ℂ → ℂ := fun x ↦ c⁻¹ * x
  let inverseParameter : P → P := fun w ↦ c⁻¹ • w
  let inverseInput : ℂ × P → ℂ × P := fun z ↦
    (inverseScalar z.1, inverseParameter z.2)
  let Q : ℂ × P → ℂ := fun z ↦ QScaled (inverseInput z)
  let R : P → Germ.GeneralCoefficientSpace d := fun w i ↦
    c ^ (d + 1 - i.1) * RScaled (inverseParameter w) i
  have hinverseScalar : AnalyticAt ℂ inverseScalar 0 := by
    dsimp only [inverseScalar]
    fun_prop
  have hinverseParameter : AnalyticAt ℂ inverseParameter 0 := by
    dsimp only [inverseParameter]
    fun_prop
  have hinverseInput : AnalyticAt ℂ inverseInput (0, 0) := by
    have hfirst := hinverseScalar.comp
      (x := ((0 : ℂ), (0 : P))) analyticAt_fst
    have hsecond := hinverseParameter.comp
      (x := ((0 : ℂ), (0 : P))) analyticAt_snd
    exact hfirst.prod hsecond
  have hinverseParameterZero : inverseParameter 0 = 0 := by
    simp [inverseParameter]
  have hinverseInputZero : inverseInput (0, 0) = (0, 0) := by
    simp [inverseInput, inverseParameter, inverseScalar]
  have hQScaledAt : AnalyticAt ℂ QScaled (inverseInput (0, 0)) := by
    simpa only [hinverseInputZero] using hQScaled
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    simpa only [Q, Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hQScaledAt hinverseInput)
  have hRScaledAt : AnalyticAt ℂ RScaled (inverseParameter 0) := by
    rw [hinverseParameterZero]
    exact hRScaled
  have hRComp : AnalyticAt ℂ
      (fun w ↦ RScaled (inverseParameter w)) 0 := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp (x := (0 : P)) hRScaledAt hinverseParameter)
  have hR : AnalyticAt ℂ R 0 := by
    apply AnalyticAt.pi
    intro i
    have hcoordinate : AnalyticAt ℂ
        (fun w ↦ RScaled (inverseParameter w) i) 0 := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        (AnalyticAt.comp (x := (0 : P))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
            (RScaled (inverseParameter 0))) hRComp)
    exact analyticAt_const.mul hcoordinate
  have hsumScaled :=
    Germ.eventually_radiallyScaledGeneralSeries_sum_eq p d c hp hc
  have hplaneTendsto : Tendsto
      (fun z : ℂ × P ↦ Germ.planePoint z.1 (y z.2))
      (nhds (0, 0)) (nhds 0) := by
    have hy : AnalyticAt ℂ (fun z : ℂ × P ↦ y z.2) (0, 0) :=
      (y.analyticAt (0 : P)).comp
        (x := ((0 : ℂ), (0 : P))) analyticAt_snd
    have hpair : AnalyticAt ℂ
        (fun z : ℂ × P ↦ (z.1, y z.2)) (0, 0) :=
      analyticAt_fst.prod hy
    have hanalytic : AnalyticAt ℂ
        (fun z : ℂ × P ↦ Germ.planePoint z.1 (y z.2))
        (0, 0) := by
      simpa only [Function.comp_def,
        Germ.generalPlanePointContinuousLinearMap_apply] using
        (AnalyticAt.comp (x := ((0 : ℂ), (0 : P)))
          (Germ.generalPlanePointContinuousLinearMap.analyticAt
            ((0 : ℂ), y (0 : P)))
          hpair)
    have hcontinuous := hanalytic.continuousAt
    change Tendsto (fun z : ℂ × P ↦
      Germ.planePoint z.1 (y z.2)) (nhds (0, 0))
        (nhds (Germ.planePoint (0 : ℂ) (y (0 : P)))) at hcontinuous
    simpa [Germ.planePoint] using hcontinuous
  have hsumInput : ∀ᶠ z : ℂ × P in nhds (0, 0),
      pScaled.sum (Germ.planePoint z.1 (y z.2)) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c • Germ.planePoint z.1 (y z.2)) :=
    hplaneTendsto.eventually hsumScaled
  have hsumAtInverse : ∀ᶠ z : ℂ × P in nhds (0, 0),
      pScaled.sum (Germ.planePoint (inverseInput z).1
          (y (inverseInput z).2)) =
        (c ^ (d + 1))⁻¹ *
          p.sum (c • Germ.planePoint (inverseInput z).1
            (y (inverseInput z).2)) :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hsumInput)
  have hdivisionAtInverse : ∀ᶠ z : ℂ × P in nhds (0, 0),
      pScaled.sum (Germ.planePoint (inverseInput z).1
          (y (inverseInput z).2)) =
        Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2) * QScaled (inverseInput z) +
          ∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i :=
    hinverseInput.continuousAt.eventually (by
      simpa only [hinverseInputZero] using hdivisionScaled)
  refine ⟨Q, R, hQ, hR, ?_⟩
  filter_upwards [hsumAtInverse, hdivisionAtInverse] with z hsum hdivision
  have hsourceScale : c • Germ.planePoint
      (inverseInput z).1 (y (inverseInput z).2) =
      Germ.planePoint z.1 (y z.2) := by
    ext i
    fin_cases i <;>
      simp [inverseInput, inverseParameter, inverseScalar,
        Germ.planePoint, map_smul, hc]
  have hscaled : (c ^ (d + 1))⁻¹ *
      p.sum (Germ.planePoint z.1 (y z.2)) =
        Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2) * QScaled (inverseInput z) +
          ∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i := by
    rw [← hdivision, hsum, hsourceScale]
  have hpolynomial : c ^ (d + 1) *
      Germ.generalDivisionPolynomialValue (inverseInput z).1
        (aScaled (inverseInput z).2) =
      Germ.generalDivisionPolynomialValue z.1 (a z.2) := by
    rw [show (inverseInput z).1 = inverseScalar z.1 by rfl]
    rw [Germ.pow_mul_generalDivisionPolynomialValue_inverse
      d c z.1 (aScaled (inverseInput z).2) hc]
    congr 1
    simpa only [inverseInput] using
      Germ.pow_mul_radiallyScaledParameterCoefficients_inverse
        d c a hc z.2
  have hremainder : c ^ (d + 1) *
      (∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
          RScaled (inverseInput z).2 i) =
      ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
    simpa only [inverseInput, inverseParameter, R] using
      Germ.pow_mul_generalRemainderSum_inverse d c z.1
        (RScaled (inverseParameter z.2)) hc
  calc
    p.sum (Germ.planePoint z.1 (y z.2)) =
        c ^ (d + 1) * ((c ^ (d + 1))⁻¹ *
          p.sum (Germ.planePoint z.1 (y z.2))) := by
      rw [← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero (d + 1) hc), one_mul]
    _ = c ^ (d + 1) *
        (Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2) * QScaled (inverseInput z) +
          ∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i) := by
      rw [hscaled]
    _ = (c ^ (d + 1) *
          Germ.generalDivisionPolynomialValue (inverseInput z).1
            (aScaled (inverseInput z).2)) * QScaled (inverseInput z) +
        c ^ (d + 1) *
          (∑ i : Fin (d + 1), (inverseInput z).1 ^ i.1 *
            RScaled (inverseInput z).2 i) := by
      ring
    _ = Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
          ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
      rw [hpolynomial, hremainder]

end Germ

end OnLeConjecture.Analytic
