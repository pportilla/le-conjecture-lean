/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralDivisionState
public import OnLeConjecture.Analytic.AnalyticImplicitFunction

/-!
# Functional calculus for analytic Weierstrass preparation

Finite state division turns a scalar analytic Taylor series into analytic
quotient and remainder functions for a monic polynomial of any positive
degree. For an exactly normalized coordinate axis, the derivative of the
remainder with respect to the polynomial coefficients is minus the identity.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- The lower coefficients of a monic polynomial of degree `d + 1`, ordered
by increasing powers. -/
abbrev GeneralCoefficientSpace (d : ℕ) := Fin (d + 1) → ℂ

/-- Projection from a division state to its remainder. -/
@[expose] noncomputable def generalRemainderProjection (d : ℕ) :
    Germ.GeneralDivisionState d →L[ℂ] Germ.GeneralCoefficientSpace d :=
  ContinuousLinearMap.snd ℂ ℂ (Germ.GeneralCoefficientSpace d)

@[simp]
theorem generalRemainderProjection_apply
    {d : ℕ} (s : Germ.GeneralDivisionState d) :
    Germ.generalRemainderProjection d s = s.2 :=
  rfl

/-- Simultaneous analytic quotient and remainder state. -/
@[expose] noncomputable def generalFunctionalState
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (x : ℂ) (a : Germ.GeneralCoefficientSpace d) (y : ℂ) :
    Germ.GeneralDivisionState d :=
  (Germ.banachAlgebraExtensionSeries
      (A := Germ.GeneralDivisionEndomorphism d) p).sum
      (Germ.generalDivisionOperator x a,
        y • (1 : Germ.GeneralDivisionEndomorphism d))
    (Germ.generalDivisionInitialState d)

/-- The analytic remainder map used in the implicit equation. -/
@[expose] noncomputable def generalFunctionalRemainder
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (s : ℂ × Germ.GeneralCoefficientSpace d) :
    Germ.GeneralCoefficientSpace d :=
  Germ.generalRemainderProjection d
    (Germ.generalFunctionalState p d 0 s.2 s.1)

/-- The quotient component of the functional state. -/
@[expose] noncomputable def generalFunctionalQuotient
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (x y : ℂ) (a : Germ.GeneralCoefficientSpace d) : ℂ :=
  (Germ.generalFunctionalState p d x a y).1

/-- The algebra input encoding the parameter and polynomial coefficients. -/
@[expose] noncomputable def generalFunctionalInput
    (d : ℕ) (s : ℂ × Germ.GeneralCoefficientSpace d) :
    Germ.GeneralDivisionEndomorphism d ×
      Germ.GeneralDivisionEndomorphism d :=
  (Germ.generalDivisionOperator 0 s.2,
    s.1 • (1 : Germ.GeneralDivisionEndomorphism d))

/-- Linear embedding that discards the parameter coordinate and retains the
polynomial coefficients. -/
@[expose] noncomputable def generalCoefficientEmbedding (d : ℕ) :
    (ℂ × Germ.GeneralCoefficientSpace d) →L[ℂ]
      (ℂ × Germ.GeneralCoefficientSpace d) :=
  (ContinuousLinearMap.inr ℂ ℂ (Germ.GeneralCoefficientSpace d)).comp
    (ContinuousLinearMap.snd ℂ ℂ (Germ.GeneralCoefficientSpace d))

@[simp]
theorem generalCoefficientEmbedding_apply
    {d : ℕ} (s : ℂ × Germ.GeneralCoefficientSpace d) :
    Germ.generalCoefficientEmbedding d s = (0, s.2) :=
  rfl

/-- The algebra input depends analytically on the parameter and polynomial
coefficients. -/
theorem analyticAt_generalFunctionalInput
    {d : ℕ} (s : ℂ × Germ.GeneralCoefficientSpace d) :
    AnalyticAt ℂ (Germ.generalFunctionalInput d) s := by
  have hop : AnalyticAt ℂ
      (fun w : ℂ × Germ.GeneralCoefficientSpace d ↦
        Germ.generalDivisionOperator 0 0 +
          Germ.generalDivisionOperatorContinuousLinearMap d
            (Germ.generalCoefficientEmbedding d w)) s :=
    analyticAt_const.add
      (((Germ.generalDivisionOperatorContinuousLinearMap d).comp
        (Germ.generalCoefficientEmbedding d)).analyticAt s)
  have hscalar : AnalyticAt ℂ
      (fun w : ℂ × Germ.GeneralCoefficientSpace d ↦
        w.1 • (1 : Germ.GeneralDivisionEndomorphism d)) s :=
    (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.fst ℂ ℂ (Germ.GeneralCoefficientSpace d))
      (1 : Germ.GeneralDivisionEndomorphism d)).analyticAt s
  have hpair := hop.prod hscalar
  convert hpair using 1
  funext w
  unfold Germ.generalFunctionalInput
  congr 1
  simpa using Germ.generalDivisionOperator_eq_base_add_linear
    (Germ.generalCoefficientEmbedding d w)

/-- Continuous extraction of the remainder after applying an endomorphism
to the initial division state. -/
@[expose] noncomputable def generalFunctionalOutput (d : ℕ) :
    Germ.GeneralDivisionEndomorphism d →L[ℂ]
      Germ.GeneralCoefficientSpace d :=
  (Germ.generalRemainderProjection d).comp
    (ContinuousLinearMap.apply ℂ (Germ.GeneralDivisionState d)
      (Germ.generalDivisionInitialState d))

@[simp]
theorem generalFunctionalOutput_apply
    {d : ℕ} (T : Germ.GeneralDivisionEndomorphism d) :
    Germ.generalFunctionalOutput d T =
      (T (Germ.generalDivisionInitialState d)).2 :=
  rfl

/-- The remainder map is analytic whenever the base division operator lies
in the convergence ball of the extended Taylor series. -/
theorem analyticAt_generalFunctionalRemainder
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    AnalyticAt ℂ (Germ.generalFunctionalRemainder p d)
      (0, (0 : Germ.GeneralCoefficientSpace d)) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hsum : AnalyticAt ℂ q.sum
      (Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d))) :=
    (q.hasFPowerSeriesOnBall hqRadius).analyticAt_of_mem hbase
  have hinput := Germ.analyticAt_generalFunctionalInput
    (d := d) (0, (0 : Germ.GeneralCoefficientSpace d))
  have hstate : AnalyticAt ℂ
      (fun s ↦ q.sum (Germ.generalFunctionalInput d s))
      (0, (0 : Germ.GeneralCoefficientSpace d)) :=
    AnalyticAt.comp
      (x := (0, (0 : Germ.GeneralCoefficientSpace d))) hsum hinput
  have hout : AnalyticAt ℂ
      (fun s ↦ Germ.generalFunctionalOutput d
        (q.sum (Germ.generalFunctionalInput d s)))
      (0, (0 : Germ.GeneralCoefficientSpace d)) :=
    AnalyticAt.comp
      (x := (0, (0 : Germ.GeneralCoefficientSpace d)))
      ((Germ.generalFunctionalOutput d).analyticAt
        (q.sum (Germ.generalFunctionalInput d
          (0, (0 : Germ.GeneralCoefficientSpace d))))) hstate
  convert hout using 1
  funext s
  rfl

/-- At a zero second algebra coordinate, only the pure first coordinate
coefficient remains. -/
theorem general_banachAlgebraExtensionSeries_apply_second_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d n : ℕ) (T : Germ.GeneralDivisionEndomorphism d) :
    Germ.banachAlgebraExtensionSeries p n
        (fun _ : Fin n ↦ (T, 0)) =
      Germ.mixedCoefficient p n n • T ^ n := by
  rw [Germ.banachAlgebraExtensionSeries_apply_diagonal]
  let last : Fin (n + 1) := ⟨n, by omega⟩
  rw [Finset.sum_eq_single last]
  · simp only [last, Nat.sub_self, pow_zero, mul_one]
    apply ContinuousLinearMap.ext
    intro s
    apply Prod.ext
    · simp [mul_apply_eq_comp]
    · funext i
      simp [mul_apply_eq_comp]
  · intro i hi hne
    have hlt : i.1 < n := by
      have hle : i.1 ≤ n := Nat.lt_succ_iff.mp i.2
      have hnot : i.1 ≠ n := by
        intro heq
        apply hne
        apply Fin.ext
        exact heq
      omega
    rw [zero_pow (Nat.sub_pos_of_lt hlt).ne']
    simp
  · simp

/-- Exact axis normalization collapses the functional state at parameter
zero to the state of the leading monomial. -/
theorem generalFunctionalState_parameter_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (x : ℂ) (a : Germ.GeneralCoefficientSpace d) :
    Germ.generalFunctionalState p d x a 0 =
      Germ.generalDivisionMonomialState x a (d + 1) := by
  have hzeroId : (0 : ℂ) •
      (1 : Germ.GeneralDivisionEndomorphism d) = 0 := by
    apply ContinuousLinearMap.ext
    intro s
    apply Prod.ext
    · simp
    · funext i
      simp
  rw [Germ.generalFunctionalState, FormalMultilinearSeries.sum]
  rw [tsum_eq_single (d + 1)]
  · rw [hzeroId]
    rw [Germ.general_banachAlgebraExtensionSeries_apply_second_zero,
      haxis, if_pos rfl]
    simp [Germ.generalDivisionMonomialState_eq_pow_apply]
  · intro n hn
    rw [hzeroId]
    rw [Germ.general_banachAlgebraExtensionSeries_apply_second_zero,
      haxis, if_neg hn]
    simp

/-- On the special parameter fibre, the remainder map is minus the
coefficient vector. -/
theorem generalFunctionalRemainder_parameter_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (a : Germ.GeneralCoefficientSpace d) :
    Germ.generalFunctionalRemainder p d (0, a) = -a := by
  rw [Germ.generalFunctionalRemainder,
    Germ.generalFunctionalState_parameter_zero p d haxis,
    Germ.generalDivisionMonomialState_divisorDegree]
  rfl

/-- The derivative of the remainder map in the coefficient directions is
minus the identity at the normalized base point. -/
theorem generalFunctionalRemainder_fderiv_inr_eq_neg
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ (Germ.generalFunctionalRemainder p d)
      (0, (0 : Germ.GeneralCoefficientSpace d))) :
    fderiv ℂ (Germ.generalFunctionalRemainder p d)
          (0, (0 : Germ.GeneralCoefficientSpace d)) ∘L
        ContinuousLinearMap.inr ℂ ℂ (Germ.GeneralCoefficientSpace d) =
      (ContinuousLinearEquiv.neg ℂ :
        Germ.GeneralCoefficientSpace d ≃L[ℂ]
          Germ.GeneralCoefficientSpace d) := by
  let inclusion :=
    ContinuousLinearMap.inr ℂ ℂ (Germ.GeneralCoefficientSpace d)
  have hcomp := fderiv_comp
    (x := (0 : Germ.GeneralCoefficientSpace d))
    hAnalytic.differentiableAt inclusion.differentiableAt
  have hfiber :
      (fun a : Germ.GeneralCoefficientSpace d ↦
        Germ.generalFunctionalRemainder p d (0, a)) =
        fun a : Germ.GeneralCoefficientSpace d ↦ -a := by
    funext a
    exact Germ.generalFunctionalRemainder_parameter_zero p d haxis a
  change fderiv ℂ
    (fun a : Germ.GeneralCoefficientSpace d ↦
      Germ.generalFunctionalRemainder p d (0, a)) 0 = _ at hcomp
  rw [hfiber] at hcomp
  have hinclusion : fderiv ℂ
      (fun a : Germ.GeneralCoefficientSpace d ↦ (0, a)) 0 =
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

/-- The point derivative required by the analytic implicit function theorem
is invertible. -/
theorem generalFunctionalRemainder_pointDerivative_isInvertible
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ (Germ.generalFunctionalRemainder p d)
      (0, (0 : Germ.GeneralCoefficientSpace d))) :
    (fderiv ℂ (Germ.generalFunctionalRemainder p d)
          (0, (0 : Germ.GeneralCoefficientSpace d)) ∘L
        ContinuousLinearMap.inr ℂ ℂ
          (Germ.GeneralCoefficientSpace d)).IsInvertible := by
  rw [Germ.generalFunctionalRemainder_fderiv_inr_eq_neg
    p d haxis hAnalytic]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Analytic coefficient functions solve the division remainder equation
near the normalized base point. -/
theorem exists_analytic_generalCoefficientBranch
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    ∃ a : ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ a 0 ∧
      a 0 = 0 ∧
      ∀ᶠ y in nhds 0,
        Germ.generalFunctionalRemainder p d (y, a y) = 0 := by
  have hAnalytic := Germ.analyticAt_generalFunctionalRemainder p d hp hbase
  have hzero : Germ.generalFunctionalRemainder p d
      (0, (0 : Germ.GeneralCoefficientSpace d)) = 0 := by
    rw [Germ.generalFunctionalRemainder_parameter_zero p d haxis]
    simp
  have hpoint :=
    Germ.generalFunctionalRemainder_pointDerivative_isInvertible
      p d haxis hAnalytic
  exact exists_analytic_simpleZeroBranch
    (Germ.generalFunctionalRemainder p d)
      (0 : Germ.GeneralCoefficientSpace d) hzero hAnalytic hpoint

/-- Inside both convergence balls, evaluation of the functional division
state recovers the original scalar Taylor sum. -/
theorem generalDivisionStateEvaluation_functionalState
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (x y : ℂ) (a : Germ.GeneralCoefficientSpace d)
    (hpMem : Germ.planePoint x y ∈ Metric.eball 0 p.radius)
    (hqMem :
      (Germ.generalDivisionOperator x a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    Germ.generalDivisionStateEvaluation x a
        (Germ.generalFunctionalState p d x a y) =
      p.sum (Germ.planePoint x y) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  let evaluation : Germ.GeneralDivisionEndomorphism d →L[ℂ] ℂ :=
    (Germ.generalDivisionStateEvaluationLinear x a).comp
      (ContinuousLinearMap.apply ℂ (Germ.GeneralDivisionState d)
        (Germ.generalDivisionInitialState d))
  have hqSum := q.hasSum hqMem
  have hqEvaluated := hqSum.map evaluation evaluation.continuous
  have hqScalarRaw : HasSum
      (fun n ↦ p n
        (fun _ : Fin n ↦ Germ.planePoint x y))
      (evaluation (q.sum (Germ.generalDivisionOperator x a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)))) := by
    apply HasSum.congr_fun hqEvaluated
    intro n
    simpa [q, evaluation] using
      (Germ.generalDivisionStateEvaluation_banachAlgebraExtensionSeries
        p n x y a).symm
  have hqScalar : HasSum
      (fun n ↦ p n
        (fun _ : Fin n ↦ Germ.planePoint x y))
      (Germ.generalDivisionStateEvaluation x a
        (Germ.generalFunctionalState p d x a y)) := by
    simpa [q, evaluation, Germ.generalFunctionalState] using hqScalarRaw
  exact hqScalar.unique (p.hasSum hpMem)

/-- Projecting an algebra monomial to its remainder removes the quotient
evaluation parameter. -/
theorem generalRemainderProjection_algebraHomogeneousMonomial_independent
    {d : ℕ} (n : ℕ) (i : Fin (n + 1))
    (x z y : ℂ) (a : Germ.GeneralCoefficientSpace d) :
    Germ.generalRemainderProjection d
        (Germ.algebraHomogeneousMonomial n i
          (fun _ : Fin n ↦
            (Germ.generalDivisionOperator x a,
              y • (1 : Germ.GeneralDivisionEndomorphism d)))
          (Germ.generalDivisionInitialState d)) =
      Germ.generalRemainderProjection d
        (Germ.algebraHomogeneousMonomial n i
          (fun _ : Fin n ↦
            (Germ.generalDivisionOperator z a,
              y • (1 : Germ.GeneralDivisionEndomorphism d)))
          (Germ.generalDivisionInitialState d)) := by
  rw [Germ.algebraHomogeneousMonomial_generalDivisionOperator_apply,
    Germ.algebraHomogeneousMonomial_generalDivisionOperator_apply,
    map_smul, map_smul]
  simp only [Germ.generalRemainderProjection_apply]
  exact congrArg (fun r ↦ y ^ (n - i.1) • r)
    (Germ.generalDivisionMonomialState_remainder_independent
      x z a i.1)

/-- Each extended homogeneous coefficient has remainder independent of the
quotient evaluation parameter. -/
theorem generalFunctionalOutput_extensionTerm_independent
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {d : ℕ} (n : ℕ) (x z y : ℂ)
    (a : Germ.GeneralCoefficientSpace d) :
    Germ.generalFunctionalOutput d
        (Germ.banachAlgebraExtensionSeries p n
          (fun _ : Fin n ↦
            (Germ.generalDivisionOperator x a,
              y • (1 : Germ.GeneralDivisionEndomorphism d)))) =
      Germ.generalFunctionalOutput d
        (Germ.banachAlgebraExtensionSeries p n
          (fun _ : Fin n ↦
            (Germ.generalDivisionOperator z a,
              y • (1 : Germ.GeneralDivisionEndomorphism d)))) := by
  simp only [Germ.generalFunctionalOutput_apply,
    Germ.banachAlgebraExtensionSeries, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_apply]
  exact congrArg
    (fun r : Germ.GeneralCoefficientSpace d ↦
      Germ.mixedCoefficient p n i.1 • r)
    (Germ.generalRemainderProjection_algebraHomogeneousMonomial_independent
      n i x z y a)

/-- Where both extended series converge, the summed remainder is independent
of the quotient evaluation parameter. -/
theorem generalFunctionalState_remainder_independent
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {d : ℕ} (x z y : ℂ) (a : Germ.GeneralCoefficientSpace d)
    (hxMem :
      (Germ.generalDivisionOperator x a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (hzMem :
      (Germ.generalDivisionOperator z a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    Germ.generalRemainderProjection d
        (Germ.generalFunctionalState p d x a y) =
      Germ.generalRemainderProjection d
        (Germ.generalFunctionalState p d z a y) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  have hxSum := (q.hasSum hxMem).map (Germ.generalFunctionalOutput d)
    (Germ.generalFunctionalOutput d).continuous
  have hzSum := (q.hasSum hzMem).map (Germ.generalFunctionalOutput d)
    (Germ.generalFunctionalOutput d).continuous
  have hzAsX : HasSum
      (fun n ↦ Germ.generalFunctionalOutput d
        (q n (fun _ : Fin n ↦
          (Germ.generalDivisionOperator x a,
            y • (1 : Germ.GeneralDivisionEndomorphism d)))))
      (Germ.generalFunctionalOutput d
        (q.sum (Germ.generalDivisionOperator z a,
          y • (1 : Germ.GeneralDivisionEndomorphism d)))) := by
    apply HasSum.congr_fun hzSum
    intro n
    exact Germ.generalFunctionalOutput_extensionTerm_independent
      p n x z y a
  simpa [q, Germ.generalFunctionalState] using hxSum.unique hzAsX

/-- The remainder at an arbitrary quotient evaluation point agrees with the
implicit remainder map. -/
theorem generalFunctionalState_remainder_eq
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (x y : ℂ) (a : Germ.GeneralCoefficientSpace d)
    (hxMem :
      (Germ.generalDivisionOperator x a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (hzeroMem :
      (Germ.generalDivisionOperator 0 a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    Germ.generalRemainderProjection d
        (Germ.generalFunctionalState p d x a y) =
      Germ.generalFunctionalRemainder p d (y, a) := by
  exact Germ.generalFunctionalState_remainder_independent
    p x 0 y a hxMem hzeroMem

/-- A zero of the functional remainder gives a monic polynomial
factorization identity wherever the relevant series converge. -/
theorem generalFunctionalPreparation_identity
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (x y : ℂ) (a : Germ.GeneralCoefficientSpace d)
    (hpMem : Germ.planePoint x y ∈ Metric.eball 0 p.radius)
    (hxMem :
      (Germ.generalDivisionOperator x a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (hzeroMem :
      (Germ.generalDivisionOperator 0 a,
        y • (1 : Germ.GeneralDivisionEndomorphism d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (hrem : Germ.generalFunctionalRemainder p d (y, a) = 0) :
    p.sum (Germ.planePoint x y) =
      Germ.generalDivisionPolynomialValue x a *
        Germ.generalFunctionalQuotient p d x y a := by
  let s := Germ.generalFunctionalState p d x a y
  have hprojection : Germ.generalRemainderProjection d s = 0 := by
    rw [Germ.generalFunctionalState_remainder_eq
      p d x y a hxMem hzeroMem, hrem]
  have hremainder : s.2 = 0 := by
    simpa [s] using hprojection
  have hevaluation := Germ.generalDivisionStateEvaluation_functionalState
    p d x y a hpMem hxMem
  change Germ.generalDivisionStateEvaluation x a s =
    p.sum (Germ.planePoint x y) at hevaluation
  rw [Germ.generalDivisionStateEvaluation, hremainder] at hevaluation
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero] at hevaluation
  simpa [s, Germ.generalFunctionalQuotient] using hevaluation.symm

/-- The quotient obtained from an exactly normalized axis takes value one at
the origin. -/
theorem generalFunctionalQuotient_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    Germ.generalFunctionalQuotient p d 0 0
        (0 : Germ.GeneralCoefficientSpace d) = 1 := by
  rw [Germ.generalFunctionalQuotient,
    Germ.generalFunctionalState_parameter_zero p d haxis,
    Germ.generalDivisionMonomialState_divisorDegree]

/-- Continuous extraction of the quotient coordinate after applying an
endomorphism to the initial division state. -/
@[expose] noncomputable def generalFunctionalQuotientOutput (d : ℕ) :
    Germ.GeneralDivisionEndomorphism d →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ (Germ.GeneralCoefficientSpace d)).comp
    (ContinuousLinearMap.apply ℂ (Germ.GeneralDivisionState d)
      (Germ.generalDivisionInitialState d))

@[simp]
theorem generalFunctionalQuotientOutput_apply
    {d : ℕ} (T : Germ.GeneralDivisionEndomorphism d) :
    Germ.generalFunctionalQuotientOutput d T =
      (T (Germ.generalDivisionInitialState d)).1 :=
  rfl

/-- The algebra input after substituting coefficient functions depending on
the second plane coordinate. -/
@[expose] noncomputable def generalFunctionalFullInput
    (d : ℕ) (a : ℂ → Germ.GeneralCoefficientSpace d)
    (z : ℂ × ℂ) :
    Germ.GeneralDivisionEndomorphism d ×
      Germ.GeneralDivisionEndomorphism d :=
  (Germ.generalDivisionOperator z.1 (a z.2),
    z.2 • (1 : Germ.GeneralDivisionEndomorphism d))

/-- The full algebra input is analytic after substitution of an analytic
coefficient branch. -/
theorem analyticAt_generalFunctionalFullInput
    (d : ℕ) (a : ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ (Germ.generalFunctionalFullInput d a) (0, 0) := by
  have haComp : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ a z.2) (0, 0) :=
    AnalyticAt.comp (x := (0, 0)) ha analyticAt_snd
  have hcoeff : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ (z.1, a z.2)) (0, 0) :=
    analyticAt_fst.prod haComp
  have hoperatorBase := Germ.analyticAt_generalDivisionOperator
    (d := d) (0, a 0)
  have hoperator : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.generalDivisionOperator z.1 (a z.2)) (0, 0) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hoperatorBase hcoeff)
  have hscalar : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        z.2 • (1 : Germ.GeneralDivisionEndomorphism d)) (0, 0) :=
    (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.snd ℂ ℂ ℂ)
      (1 : Germ.GeneralDivisionEndomorphism d)).analyticAt (0, 0)
  exact hoperator.prod hscalar

/-- Substituting an analytic coefficient branch into the functional
quotient produces an analytic function of the two plane coordinates. -/
theorem analyticAt_generalFunctionalQuotient_comp
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (a : ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0)
    (haZero : a 0 = 0) :
    AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.generalFunctionalQuotient p d z.1 z.2 (a z.2))
      (0, 0) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hsum : AnalyticAt ℂ q.sum
      (Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d))) :=
    (q.hasFPowerSeriesOnBall hqRadius).analyticAt_of_mem hbase
  have hinput := Germ.analyticAt_generalFunctionalFullInput d a ha
  have hsumBase : AnalyticAt ℂ q.sum
      (Germ.generalDivisionOperator 0 (a 0),
        (0 : ℂ) • (1 : Germ.GeneralDivisionEndomorphism d)) := by
    simpa [Germ.generalFunctionalInput, haZero] using hsum
  have hstate : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ q.sum
        (Germ.generalDivisionOperator z.1 (a z.2),
          z.2 • (1 : Germ.GeneralDivisionEndomorphism d))) (0, 0) := by
    simpa [Function.comp_def, Germ.generalFunctionalFullInput] using
      (AnalyticAt.comp (x := (0, 0)) hsumBase hinput)
  have hquotient : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ Germ.generalFunctionalQuotientOutput d
        (q.sum (Germ.generalDivisionOperator z.1 (a z.2),
          z.2 • (1 : Germ.GeneralDivisionEndomorphism d)))) (0, 0) :=
    AnalyticAt.comp (x := (0, 0))
      ((Germ.generalFunctionalQuotientOutput d).analyticAt
        (q.sum (Germ.generalDivisionOperator 0 (a 0),
          (0 : ℂ) • (1 : Germ.GeneralDivisionEndomorphism d)))) hstate
  convert hquotient using 1
  funext z
  rfl

/-- Continuous linear identification of a coordinate pair with a point of
the two dimensional source. -/
@[expose] noncomputable def generalPlanePointContinuousLinearMap :
    (ℂ × ℂ) →L[ℂ] Source 2 :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℂ ℂ ℂ)
      Germ.firstAxis +
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℂ ℂ ℂ)
      Germ.secondAxis

@[simp]
theorem generalPlanePointContinuousLinearMap_apply (z : ℂ × ℂ) :
    Germ.generalPlanePointContinuousLinearMap z =
      Germ.planePoint z.1 z.2 :=
  rfl

/-- Conditional analytic Weierstrass preparation for an exactly normalized
axis. The extra condition places the base division operator in the
convergence ball of the Banach algebra extension. -/
theorem exists_analytic_generalPreparation_of_base_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius) :
    ∃ a : ℂ → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧
      a 0 = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z := by
  obtain ⟨a, ha, haZero, hrem⟩ :=
    Germ.exists_analytic_generalCoefficientBranch p d hp haxis hbase
  let Q : ℂ × ℂ → ℂ := fun z ↦
    Germ.generalFunctionalQuotient p d z.1 z.2 (a z.2)
  have hQAnalytic : AnalyticAt ℂ Q (0, 0) :=
    Germ.analyticAt_generalFunctionalQuotient_comp
      p d hp hbase a ha haZero
  have hQZero : Q (0, 0) = 1 := by
    simpa [Q, haZero] using Germ.generalFunctionalQuotient_zero p d haxis
  have hpEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.planePoint z.1 z.2 ∈ Metric.eball 0 p.radius := by
    have htendsto :=
      Germ.generalPlanePointContinuousLinearMap.continuous.continuousAt
        (x := ((0, 0) : ℂ × ℂ))
    have hball : Metric.eball 0 p.radius ∈
        nhds (Germ.generalPlanePointContinuousLinearMap (0, 0)) := by
      simpa [Germ.planePoint] using Metric.eball_mem_nhds 0 hp
    have heventually := htendsto.eventually hball
    filter_upwards [heventually] with z hz
    rw [Metric.mem_eball]
    simpa only [Germ.generalPlanePointContinuousLinearMap_apply] using hz
  have hinputAnalytic := Germ.analyticAt_generalFunctionalFullInput d a ha
  have hbaseFull : Germ.generalFunctionalFullInput d a (0, 0) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius := by
    simpa [Germ.generalFunctionalFullInput, Germ.generalFunctionalInput,
      haZero] using hbase
  have hxEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.generalFunctionalFullInput d a z ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d) p).radius :=
    hinputAnalytic.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbaseFull)
  have hzeroSource : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ ((0 : ℂ), z.2)) (0, 0) :=
    analyticAt_const.prod analyticAt_snd
  have hzeroInput : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.generalFunctionalFullInput d a (0, z.2)) (0, 0) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hinputAnalytic hzeroSource)
  have hzeroEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.generalFunctionalFullInput d a (0, z.2) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d) p).radius :=
    hzeroInput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbaseFull)
  have hremEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.generalFunctionalRemainder p d (z.2, a z.2) = 0 := by
    have hsnd : Tendsto (fun z : ℂ × ℂ ↦ z.2)
        (nhds (0, 0)) (nhds 0) := continuousAt_snd
    exact hsnd.eventually hrem
  refine ⟨a, Q, ha, haZero, hQAnalytic, hQZero, ?_⟩
  filter_upwards [hpEventually, hxEventually, hzeroEventually,
    hremEventually] with z hpz hxz hzeroz hremz
  exact Germ.generalFunctionalPreparation_identity
    p d z.1 z.2 (a z.2) hpz hxz hzeroz hremz

end Germ

end OnLeConjecture.Analytic
