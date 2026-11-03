/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CubicDivisionState
public import OnLeConjecture.Analytic.AnalyticImplicitFunction

/-!
# Functional calculus for analytic cubic preparation

The four dimensional division state turns a scalar analytic Taylor series
into an analytic quotient and remainder map. When the restriction to the
first coordinate axis is exactly `x³`, the derivative of the remainder map
with respect to the three polynomial coefficients is minus the identity.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- The three coefficients of a monic cubic, ordered from constant to
quadratic. -/
abbrev CubicCoefficientSpace := Fin 3 → ℂ

/-- Projection from a division state to its three remainder coordinates. -/
@[expose] noncomputable def cubicRemainderProjection :
    Germ.CubicDivisionState →L[ℂ] Germ.CubicCoefficientSpace :=
  ContinuousLinearMap.pi fun i ↦
    ContinuousLinearMap.proj (R := ℂ) i.succ

@[simp]
theorem cubicRemainderProjection_apply
    (s : Germ.CubicDivisionState) (i : Fin 3) :
    Germ.cubicRemainderProjection s i = s i.succ := by
  rfl

/-- Simultaneous analytic quotient and remainder state. -/
@[expose] noncomputable def cubicFunctionalState
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (x a₂ a₁ a₀ y : ℂ) : Germ.CubicDivisionState :=
  (Germ.banachAlgebraExtensionSeries
      (A := Germ.CubicDivisionEndomorphism) p).sum
      (Germ.cubicDivisionOperator x a₂ a₁ a₀,
        y • (1 : Germ.CubicDivisionEndomorphism))
    Germ.cubicDivisionInitialState

/-- The analytic remainder map used in the implicit equation. -/
@[expose] noncomputable def cubicFunctionalRemainder
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.CubicCoefficientSpace :=
  Germ.cubicRemainderProjection
    (Germ.cubicFunctionalState p 0 (s.2 2) (s.2 1) (s.2 0) s.1)

/-- The quotient component of the functional state. -/
@[expose] noncomputable def cubicFunctionalQuotient
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (x y : ℂ) (a : Germ.CubicCoefficientSpace) : ℂ :=
  Germ.cubicFunctionalState p x (a 2) (a 1) (a 0) y 0

/-- The algebra input encoding the parameter and the three cubic
coefficients. -/
@[expose] noncomputable def cubicFunctionalInput
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.CubicDivisionEndomorphism × Germ.CubicDivisionEndomorphism :=
  (Germ.cubicDivisionOperator 0 (s.2 2) (s.2 1) (s.2 0),
    s.1 • (1 : Germ.CubicDivisionEndomorphism))

/-- Linear embedding of the three cubic coefficients into the four operator
parameters. -/
@[expose] noncomputable def cubicCoefficientEmbedding :
    (ℂ × Germ.CubicCoefficientSpace) →L[ℂ] Source 4 :=
  ContinuousLinearMap.pi fun i ↦
    Fin.cases 0
      (fun j ↦ Fin.cases
        ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).comp
          (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace))
        (fun k ↦ Fin.cases
          ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).comp
            (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace))
          (fun _ ↦
            (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).comp
              (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace)) k) j) i

@[simp]
theorem cubicCoefficientEmbedding_apply_zero
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicCoefficientEmbedding s 0 = 0 := by
  simp [Germ.cubicCoefficientEmbedding]

@[simp]
theorem cubicCoefficientEmbedding_apply_one
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicCoefficientEmbedding s 1 = s.2 2 := by
  change (ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).comp
    (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace) s = _
  rfl

@[simp]
theorem cubicCoefficientEmbedding_apply_two
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicCoefficientEmbedding s 2 = s.2 1 := by
  change (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).comp
    (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace) s = _
  rfl

@[simp]
theorem cubicCoefficientEmbedding_apply_three
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicCoefficientEmbedding s 3 = s.2 0 := by
  change (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).comp
    (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace) s = _
  rfl

/-- Linear embedding of the quotient evaluation point and cubic
coefficients into the four division operator parameters. -/
@[expose] noncomputable def cubicFullCoefficientEmbedding :
    (ℂ × Germ.CubicCoefficientSpace) →L[ℂ] Source 4 :=
  ContinuousLinearMap.pi fun i ↦
    Fin.cases (ContinuousLinearMap.fst ℂ ℂ Germ.CubicCoefficientSpace)
      (fun j ↦ Fin.cases
        ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).comp
          (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace))
        (fun k ↦ Fin.cases
          ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).comp
            (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace))
          (fun _ ↦
            (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).comp
              (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace)) k) j) i

@[simp]
theorem cubicFullCoefficientEmbedding_apply_zero
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicFullCoefficientEmbedding s 0 = s.1 := by
  rfl

@[simp]
theorem cubicFullCoefficientEmbedding_apply_one
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicFullCoefficientEmbedding s 1 = s.2 2 := by
  change (ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).comp
    (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace) s = _
  rfl

@[simp]
theorem cubicFullCoefficientEmbedding_apply_two
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicFullCoefficientEmbedding s 2 = s.2 1 := by
  change (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).comp
    (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace) s = _
  rfl

@[simp]
theorem cubicFullCoefficientEmbedding_apply_three
    (s : ℂ × Germ.CubicCoefficientSpace) :
    Germ.cubicFullCoefficientEmbedding s 3 = s.2 0 := by
  change (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).comp
    (ContinuousLinearMap.snd ℂ ℂ Germ.CubicCoefficientSpace) s = _
  rfl

/-- The algebra input depends analytically on the parameter and cubic
coefficients. -/
theorem analyticAt_cubicFunctionalInput
    (s : ℂ × Germ.CubicCoefficientSpace) :
    AnalyticAt ℂ Germ.cubicFunctionalInput s := by
  have hop : AnalyticAt ℂ
      (fun w ↦ Germ.cubicDivisionOperator 0 0 0 0 +
        Germ.cubicDivisionOperatorContinuousLinearMap
          (Germ.cubicCoefficientEmbedding w)) s :=
    analyticAt_const.add
      ((Germ.cubicDivisionOperatorContinuousLinearMap.comp
        Germ.cubicCoefficientEmbedding).analyticAt s)
  have hscalar : AnalyticAt ℂ
      (fun w : ℂ × Germ.CubicCoefficientSpace ↦
        w.1 • (1 : Germ.CubicDivisionEndomorphism)) s := by
    exact (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.fst ℂ ℂ Germ.CubicCoefficientSpace)
      (1 : Germ.CubicDivisionEndomorphism)).analyticAt s
  have hpair := hop.prod hscalar
  convert hpair using 1
  funext w
  unfold Germ.cubicFunctionalInput
  congr 1
  simpa using Germ.cubicDivisionOperator_eq_base_add_linear
    (Germ.cubicCoefficientEmbedding w)

/-- Continuous extraction of the remainder coordinates after applying an
endomorphism to the initial division state. -/
@[expose] noncomputable def cubicFunctionalOutput :
    Germ.CubicDivisionEndomorphism →L[ℂ] Germ.CubicCoefficientSpace :=
  Germ.cubicRemainderProjection.comp
    (ContinuousLinearMap.apply ℂ Germ.CubicDivisionState
      Germ.cubicDivisionInitialState)

@[simp]
theorem cubicFunctionalOutput_apply
    (T : Germ.CubicDivisionEndomorphism) :
    Germ.cubicFunctionalOutput T =
      Germ.cubicRemainderProjection
        (T Germ.cubicDivisionInitialState) := by
  rfl

/-- The cubic remainder map is analytic whenever the base division operator
lies in the convergence ball of the extended Taylor series. -/
theorem analyticAt_cubicFunctionalRemainder
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius)
    (hbase : Germ.cubicFunctionalInput
        (0, (0 : Germ.CubicCoefficientSpace)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius) :
    AnalyticAt ℂ (Germ.cubicFunctionalRemainder p)
      (0, (0 : Germ.CubicCoefficientSpace)) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.CubicDivisionEndomorphism) p
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hsum : AnalyticAt ℂ q.sum
      (Germ.cubicFunctionalInput
        (0, (0 : Germ.CubicCoefficientSpace))) :=
    (q.hasFPowerSeriesOnBall hqRadius).analyticAt_of_mem hbase
  have hinput := Germ.analyticAt_cubicFunctionalInput
    (0, (0 : Germ.CubicCoefficientSpace))
  have hstate : AnalyticAt ℂ
      (fun s ↦ q.sum (Germ.cubicFunctionalInput s))
      (0, (0 : Germ.CubicCoefficientSpace)) :=
    AnalyticAt.comp
      (x := (0, (0 : Germ.CubicCoefficientSpace))) hsum hinput
  have hout : AnalyticAt ℂ
      (fun s ↦ Germ.cubicFunctionalOutput
        (q.sum (Germ.cubicFunctionalInput s)))
      (0, (0 : Germ.CubicCoefficientSpace)) :=
    AnalyticAt.comp
      (x := (0, (0 : Germ.CubicCoefficientSpace)))
      (Germ.cubicFunctionalOutput.analyticAt
        (q.sum (Germ.cubicFunctionalInput
          (0, (0 : Germ.CubicCoefficientSpace))))) hstate
  convert hout using 1
  funext s
  rfl

/-- At a zero second algebra coordinate, only the pure first coordinate
coefficient remains. -/
theorem banachAlgebraExtensionSeries_apply_second_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (T : Germ.CubicDivisionEndomorphism) :
    Germ.banachAlgebraExtensionSeries p d
        (fun _ : Fin d ↦ (T, 0)) =
      Germ.mixedCoefficient p d d • T ^ d := by
  rw [Germ.banachAlgebraExtensionSeries_apply_diagonal]
  let last : Fin (d + 1) := ⟨d, by omega⟩
  rw [Finset.sum_eq_single last]
  · simp only [last, Nat.sub_self, pow_zero, mul_one]
    ext s i
    simp [mul_apply_eq_comp]
  · intro i hi hne
    have hlt : i.1 < d := by
      have hle : i.1 ≤ d := Nat.lt_succ_iff.mp i.2
      have hnot : i.1 ≠ d := by
        intro heq
        apply hne
        apply Fin.ext
        exact heq
      omega
    rw [zero_pow (Nat.sub_pos_of_lt hlt).ne']
    simp
  · simp

/-- Exact cubic axis coefficients collapse the functional state at parameter
zero to the state of the monomial `x³`. -/
theorem cubicFunctionalState_parameter_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0)
    (x a₂ a₁ a₀ : ℂ) :
    Germ.cubicFunctionalState p x a₂ a₁ a₀ 0 =
      Germ.cubicDivisionMonomialState x a₂ a₁ a₀ 3 := by
  have hzeroId : (0 : ℂ) •
      (1 : Germ.CubicDivisionEndomorphism) = 0 := by
    ext s i
    simp
  rw [Germ.cubicFunctionalState,
    FormalMultilinearSeries.sum]
  rw [tsum_eq_single 3]
  · rw [hzeroId]
    rw [Germ.banachAlgebraExtensionSeries_apply_second_zero,
      haxis, if_pos rfl]
    simp [Germ.cubicDivisionMonomialState_eq_pow_apply]
  · intro d hd
    rw [hzeroId]
    rw [Germ.banachAlgebraExtensionSeries_apply_second_zero,
      haxis, if_neg hd]
    have hzero : (0 : ℂ) •
        (Germ.cubicDivisionOperator x a₂ a₁ a₀) ^ d = 0 :=
      by
        ext s i
        simp
    rw [hzero]

/-- Under exact cubic axis normalization, the remainder map on the special
parameter fiber is minus the coefficient vector. -/
theorem cubicFunctionalRemainder_parameter_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0)
    (a : Germ.CubicCoefficientSpace) :
    Germ.cubicFunctionalRemainder p (0, a) = -a := by
  funext i
  fin_cases i
  · simp only [Germ.cubicFunctionalRemainder,
      Germ.cubicRemainderProjection_apply]
    rw [Germ.cubicFunctionalState_parameter_zero p haxis]
    simp [Germ.cubicDivisionMonomialState]
  · simp only [Germ.cubicFunctionalRemainder,
      Germ.cubicRemainderProjection_apply]
    rw [Germ.cubicFunctionalState_parameter_zero p haxis]
    simp [Germ.cubicDivisionMonomialState]
  · simp only [Germ.cubicFunctionalRemainder,
      Germ.cubicRemainderProjection_apply]
    rw [Germ.cubicFunctionalState_parameter_zero p haxis]
    simp [Germ.cubicDivisionMonomialState]

/-- The derivative of the cubic remainder map in the coefficient directions
is minus the identity at the normalized cubic base point. -/
theorem cubicFunctionalRemainder_fderiv_inr_eq_neg
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ (Germ.cubicFunctionalRemainder p)
      (0, (0 : Germ.CubicCoefficientSpace))) :
    fderiv ℂ (Germ.cubicFunctionalRemainder p)
          (0, (0 : Germ.CubicCoefficientSpace)) ∘L
        ContinuousLinearMap.inr ℂ ℂ Germ.CubicCoefficientSpace =
      (ContinuousLinearEquiv.neg ℂ :
        Germ.CubicCoefficientSpace ≃L[ℂ] Germ.CubicCoefficientSpace) := by
  let inclusion :=
    ContinuousLinearMap.inr ℂ ℂ Germ.CubicCoefficientSpace
  have hcomp := fderiv_comp
    (x := (0 : Germ.CubicCoefficientSpace))
    hAnalytic.differentiableAt inclusion.differentiableAt
  have hfiber :
      (fun a : Germ.CubicCoefficientSpace ↦
        Germ.cubicFunctionalRemainder p (0, a)) =
        fun a : Germ.CubicCoefficientSpace ↦ -a := by
    funext a
    exact Germ.cubicFunctionalRemainder_parameter_zero p haxis a
  change fderiv ℂ
    (fun a : Germ.CubicCoefficientSpace ↦
      Germ.cubicFunctionalRemainder p (0, a)) 0 = _ at hcomp
  rw [hfiber] at hcomp
  have hinclusion : fderiv ℂ
      (fun a : Germ.CubicCoefficientSpace ↦ (0, a)) 0 = inclusion := by
    exact inclusion.hasFDerivAt.fderiv
  have hneg : fderiv ℂ
      (fun a : Germ.CubicCoefficientSpace ↦ -a) 0 =
        (ContinuousLinearEquiv.neg ℂ :
          Germ.CubicCoefficientSpace ≃L[ℂ]
            Germ.CubicCoefficientSpace) := by
    exact (ContinuousLinearEquiv.neg ℂ :
      Germ.CubicCoefficientSpace ≃L[ℂ]
        Germ.CubicCoefficientSpace).toContinuousLinearMap.hasFDerivAt.fderiv
  rw [hinclusion, hneg] at hcomp
  exact hcomp.symm

/-- The point derivative required by the analytic implicit function theorem
is invertible. -/
theorem cubicFunctionalRemainder_pointDerivative_isInvertible
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0)
    (hAnalytic : AnalyticAt ℂ (Germ.cubicFunctionalRemainder p)
      (0, (0 : Germ.CubicCoefficientSpace))) :
    (fderiv ℂ (Germ.cubicFunctionalRemainder p)
          (0, (0 : Germ.CubicCoefficientSpace)) ∘L
        ContinuousLinearMap.inr ℂ ℂ
          Germ.CubicCoefficientSpace).IsInvertible := by
  rw [Germ.cubicFunctionalRemainder_fderiv_inr_eq_neg p haxis hAnalytic]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Analytic coefficient functions solve the cubic division remainder
equation near the normalized base point. -/
theorem exists_analytic_cubicCoefficientBranch
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0)
    (hbase : Germ.cubicFunctionalInput
        (0, (0 : Germ.CubicCoefficientSpace)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius) :
    ∃ a : ℂ → Germ.CubicCoefficientSpace,
      AnalyticAt ℂ a 0 ∧
      a 0 = 0 ∧
      ∀ᶠ y in nhds 0,
        Germ.cubicFunctionalRemainder p (y, a y) = 0 := by
  have hAnalytic := Germ.analyticAt_cubicFunctionalRemainder p hp hbase
  have hzero : Germ.cubicFunctionalRemainder p
      (0, (0 : Germ.CubicCoefficientSpace)) = 0 := by
    rw [Germ.cubicFunctionalRemainder_parameter_zero p haxis]
    simp
  have hpoint :=
    Germ.cubicFunctionalRemainder_pointDerivative_isInvertible
      p haxis hAnalytic
  exact exists_analytic_simpleZeroBranch
    (Germ.cubicFunctionalRemainder p)
      (0 : Germ.CubicCoefficientSpace) hzero hAnalytic hpoint

/-- Inside both convergence balls, evaluation of the functional division
state recovers the original scalar Taylor sum. -/
theorem cubicDivisionStateEvaluation_functionalState
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (x y a₂ a₁ a₀ : ℂ)
    (hpMem : Germ.planePoint x y ∈ Metric.eball 0 p.radius)
    (hqMem :
      (Germ.cubicDivisionOperator x a₂ a₁ a₀,
        y • (1 : Germ.CubicDivisionEndomorphism)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius) :
    Germ.cubicDivisionStateEvaluation x a₂ a₁ a₀
        (Germ.cubicFunctionalState p x a₂ a₁ a₀ y) =
      p.sum (Germ.planePoint x y) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.CubicDivisionEndomorphism) p
  let evaluation : Germ.CubicDivisionEndomorphism →L[ℂ] ℂ :=
    (Germ.cubicDivisionStateEvaluationLinear x a₂ a₁ a₀).comp
      (ContinuousLinearMap.apply ℂ Germ.CubicDivisionState
        Germ.cubicDivisionInitialState)
  have hqSum := q.hasSum hqMem
  have hqEvaluated := hqSum.map evaluation evaluation.continuous
  have hqScalar : HasSum
      (fun d ↦ p d
        (fun _ : Fin d ↦ Germ.planePoint x y))
      (Germ.cubicDivisionStateEvaluation x a₂ a₁ a₀
        (Germ.cubicFunctionalState p x a₂ a₁ a₀ y)) := by
    apply HasSum.congr_fun hqEvaluated
    intro d
    simpa [q, evaluation] using
      (Germ.cubicDivisionStateEvaluation_banachAlgebraExtensionSeries
        p d x y a₂ a₁ a₀).symm
  exact hqScalar.unique (p.hasSum hpMem)

/-- Projecting an algebra monomial to its remainder coordinates removes the
quotient evaluation parameter. -/
theorem cubicRemainderProjection_algebraHomogeneousMonomial_independent
    (d : ℕ) (i : Fin (d + 1)) (x z y a₂ a₁ a₀ : ℂ) :
    Germ.cubicRemainderProjection
        (Germ.algebraHomogeneousMonomial d i
          (fun _ : Fin d ↦
            (Germ.cubicDivisionOperator x a₂ a₁ a₀,
              y • (1 : Germ.CubicDivisionEndomorphism)))
          Germ.cubicDivisionInitialState) =
      Germ.cubicRemainderProjection
        (Germ.algebraHomogeneousMonomial d i
          (fun _ : Fin d ↦
            (Germ.cubicDivisionOperator z a₂ a₁ a₀,
              y • (1 : Germ.CubicDivisionEndomorphism)))
          Germ.cubicDivisionInitialState) := by
  rw [Germ.algebraHomogeneousMonomial_divisionOperator_apply,
    Germ.algebraHomogeneousMonomial_divisionOperator_apply,
    map_smul, map_smul]
  ext j
  simp only [Pi.smul_apply, Germ.cubicRemainderProjection_apply]
  rw [Germ.cubicDivisionMonomialState_remainder_independent]

/-- Each extended homogeneous coefficient has remainder coordinates
independent of the quotient evaluation parameter. -/
theorem cubicFunctionalOutput_extensionTerm_independent
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (x z y a₂ a₁ a₀ : ℂ) :
    Germ.cubicFunctionalOutput
        (Germ.banachAlgebraExtensionSeries p d
          (fun _ : Fin d ↦
            (Germ.cubicDivisionOperator x a₂ a₁ a₀,
              y • (1 : Germ.CubicDivisionEndomorphism)))) =
      Germ.cubicFunctionalOutput
        (Germ.banachAlgebraExtensionSeries p d
          (fun _ : Fin d ↦
            (Germ.cubicDivisionOperator z a₂ a₁ a₀,
              y • (1 : Germ.CubicDivisionEndomorphism)))) := by
  simp only [Germ.cubicFunctionalOutput_apply,
    Germ.banachAlgebraExtensionSeries, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_apply, map_smul]
  exact congrArg
    (fun s : Germ.CubicCoefficientSpace ↦
      Germ.mixedCoefficient p d i.1 • s)
    (Germ.cubicRemainderProjection_algebraHomogeneousMonomial_independent
      d i x z y a₂ a₁ a₀)

/-- Where both extended series converge, the summed remainder coordinates
are independent of the quotient evaluation parameter. -/
theorem cubicFunctionalState_remainder_independent
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (x z y a₂ a₁ a₀ : ℂ)
    (hxMem :
      (Germ.cubicDivisionOperator x a₂ a₁ a₀,
        y • (1 : Germ.CubicDivisionEndomorphism)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius)
    (hzMem :
      (Germ.cubicDivisionOperator z a₂ a₁ a₀,
        y • (1 : Germ.CubicDivisionEndomorphism)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius) :
    Germ.cubicRemainderProjection
        (Germ.cubicFunctionalState p x a₂ a₁ a₀ y) =
      Germ.cubicRemainderProjection
        (Germ.cubicFunctionalState p z a₂ a₁ a₀ y) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.CubicDivisionEndomorphism) p
  have hxSum := (q.hasSum hxMem).map Germ.cubicFunctionalOutput
    Germ.cubicFunctionalOutput.continuous
  have hzSum := (q.hasSum hzMem).map Germ.cubicFunctionalOutput
    Germ.cubicFunctionalOutput.continuous
  have hzAsX : HasSum
      (fun d ↦ Germ.cubicFunctionalOutput
        (q d (fun _ : Fin d ↦
          (Germ.cubicDivisionOperator x a₂ a₁ a₀,
            y • (1 : Germ.CubicDivisionEndomorphism)))))
      (Germ.cubicFunctionalOutput
        (q.sum (Germ.cubicDivisionOperator z a₂ a₁ a₀,
          y • (1 : Germ.CubicDivisionEndomorphism)))) := by
    apply HasSum.congr_fun hzSum
    intro d
    exact Germ.cubicFunctionalOutput_extensionTerm_independent
      p d x z y a₂ a₁ a₀
  simpa [q, Germ.cubicFunctionalState] using hxSum.unique hzAsX

/-- The remainder coordinates at an arbitrary quotient evaluation point
agree with the implicit remainder map. -/
theorem cubicFunctionalState_remainder_eq
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (x y : ℂ) (a : Germ.CubicCoefficientSpace)
    (hxMem :
      (Germ.cubicDivisionOperator x (a 2) (a 1) (a 0),
        y • (1 : Germ.CubicDivisionEndomorphism)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius)
    (hzeroMem :
      (Germ.cubicDivisionOperator 0 (a 2) (a 1) (a 0),
        y • (1 : Germ.CubicDivisionEndomorphism)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius) :
    Germ.cubicRemainderProjection
        (Germ.cubicFunctionalState p x (a 2) (a 1) (a 0) y) =
      Germ.cubicFunctionalRemainder p (y, a) := by
  exact Germ.cubicFunctionalState_remainder_independent
    p x 0 y (a 2) (a 1) (a 0) hxMem hzeroMem

/-- A zero of the functional remainder map yields the monic cubic
factorization identity at every point where the relevant series converge. -/
theorem cubicFunctionalPreparation_identity
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (x y : ℂ) (a : Germ.CubicCoefficientSpace)
    (hpMem : Germ.planePoint x y ∈ Metric.eball 0 p.radius)
    (hxMem :
      (Germ.cubicDivisionOperator x (a 2) (a 1) (a 0),
        y • (1 : Germ.CubicDivisionEndomorphism)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius)
    (hzeroMem :
      (Germ.cubicDivisionOperator 0 (a 2) (a 1) (a 0),
        y • (1 : Germ.CubicDivisionEndomorphism)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius)
    (hrem : Germ.cubicFunctionalRemainder p (y, a) = 0) :
    p.sum (Germ.planePoint x y) =
      Germ.cubicDivisionPolynomialValue x (a 2) (a 1) (a 0) *
        Germ.cubicFunctionalQuotient p x y a := by
  let s := Germ.cubicFunctionalState p x (a 2) (a 1) (a 0) y
  have hprojection : Germ.cubicRemainderProjection s = 0 := by
    rw [Germ.cubicFunctionalState_remainder_eq p x y a hxMem hzeroMem,
      hrem]
  have h₁ : s 1 = 0 := by
    have h := congrFun hprojection (0 : Fin 3)
    simpa [s] using h
  have h₂ : s 2 = 0 := by
    have h := congrFun hprojection (1 : Fin 3)
    simpa [s] using h
  have h₃ : s 3 = 0 := by
    have h := congrFun hprojection (2 : Fin 3)
    simpa [s] using h
  have hevaluation := Germ.cubicDivisionStateEvaluation_functionalState
    p x y (a 2) (a 1) (a 0) hpMem hxMem
  change Germ.cubicDivisionStateEvaluation x (a 2) (a 1) (a 0) s =
    p.sum (Germ.planePoint x y) at hevaluation
  rw [Germ.cubicDivisionStateEvaluation, h₁, h₂, h₃] at hevaluation
  simpa [s, Germ.cubicFunctionalQuotient] using hevaluation.symm

/-- The quotient obtained from an exactly normalized cubic axis takes the
value one at the origin. -/
theorem cubicFunctionalQuotient_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0) :
    Germ.cubicFunctionalQuotient p 0 0
        (0 : Germ.CubicCoefficientSpace) = 1 := by
  rw [Germ.cubicFunctionalQuotient,
    Germ.cubicFunctionalState_parameter_zero p haxis]
  simp [Germ.cubicDivisionMonomialState]

/-- Continuous extraction of the quotient coordinate after applying an
endomorphism to the initial division state. -/
@[expose] noncomputable def cubicFunctionalQuotientOutput :
    Germ.CubicDivisionEndomorphism →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 4)).comp
    (ContinuousLinearMap.apply ℂ Germ.CubicDivisionState
      Germ.cubicDivisionInitialState)

@[simp]
theorem cubicFunctionalQuotientOutput_apply
    (T : Germ.CubicDivisionEndomorphism) :
    Germ.cubicFunctionalQuotientOutput T =
      T Germ.cubicDivisionInitialState 0 := by
  rfl

/-- The algebra input after substituting coefficient functions depending on
the second plane coordinate. -/
@[expose] noncomputable def cubicFunctionalFullInput
    (a : ℂ → Germ.CubicCoefficientSpace) (z : ℂ × ℂ) :
    Germ.CubicDivisionEndomorphism × Germ.CubicDivisionEndomorphism :=
  (Germ.cubicDivisionOperator z.1 (a z.2 2) (a z.2 1) (a z.2 0),
    z.2 • (1 : Germ.CubicDivisionEndomorphism))

/-- The full algebra input is analytic after substitution of an analytic
coefficient branch. -/
theorem analyticAt_cubicFunctionalFullInput
    (a : ℂ → Germ.CubicCoefficientSpace)
    (ha : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ (Germ.cubicFunctionalFullInput a) (0, 0) := by
  have haComp : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ a z.2) (0, 0) :=
    AnalyticAt.comp (x := (0, 0)) ha analyticAt_snd
  have hcoeff : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ (z.1, a z.2)) (0, 0) :=
    analyticAt_fst.prod haComp
  have hoperatorVariable : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.cubicDivisionOperatorContinuousLinearMap
          (Germ.cubicFullCoefficientEmbedding (z.1, a z.2)))
      (0, 0) := by
    let L := Germ.cubicDivisionOperatorContinuousLinearMap.comp
      Germ.cubicFullCoefficientEmbedding
    have hlinear : AnalyticAt ℂ (L :
        ℂ × Germ.CubicCoefficientSpace →
          Germ.CubicDivisionEndomorphism) (0, a 0) :=
      L.analyticAt (0, a 0)
    have hcomp := AnalyticAt.comp (x := (0, 0)) hlinear hcoeff
    simpa [L, Function.comp_def] using hcomp
  have hoperator : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.cubicDivisionOperator z.1 (a z.2 2)
          (a z.2 1) (a z.2 0)) (0, 0) := by
    have hconst : AnalyticAt ℂ
        (fun _ : ℂ × ℂ ↦
          Germ.cubicDivisionOperator 0 0 0 0) (0, 0) :=
      analyticAt_const
    have hadd := hconst.add hoperatorVariable
    convert hadd using 1
    funext z
    simpa using Germ.cubicDivisionOperator_eq_base_add_linear
      (Germ.cubicFullCoefficientEmbedding (z.1, a z.2))
  have hscalar : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        z.2 • (1 : Germ.CubicDivisionEndomorphism)) (0, 0) :=
    (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.snd ℂ ℂ ℂ)
      (1 : Germ.CubicDivisionEndomorphism)).analyticAt (0, 0)
  exact hoperator.prod hscalar

/-- Substituting an analytic coefficient branch into the functional quotient
produces an analytic function of the two plane coordinates. -/
theorem analyticAt_cubicFunctionalQuotient_comp
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius)
    (hbase : Germ.cubicFunctionalInput
        (0, (0 : Germ.CubicCoefficientSpace)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius)
    (a : ℂ → Germ.CubicCoefficientSpace)
    (ha : AnalyticAt ℂ a 0)
    (haZero : a 0 = 0) :
    AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.cubicFunctionalQuotient p z.1 z.2 (a z.2)) (0, 0) := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.CubicDivisionEndomorphism) p
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  have hsum : AnalyticAt ℂ q.sum
      (Germ.cubicFunctionalInput
        (0, (0 : Germ.CubicCoefficientSpace))) :=
    (q.hasFPowerSeriesOnBall hqRadius).analyticAt_of_mem hbase
  have hinput := Germ.analyticAt_cubicFunctionalFullInput a ha
  have hsumBase : AnalyticAt ℂ q.sum
      (Germ.cubicDivisionOperator 0 (a 0 2) (a 0 1) (a 0 0),
        (0 : ℂ) • (1 : Germ.CubicDivisionEndomorphism)) := by
    simpa [Germ.cubicFunctionalInput, haZero] using hsum
  have hstate : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ q.sum
        (Germ.cubicDivisionOperator z.1 (a z.2 2)
            (a z.2 1) (a z.2 0),
          z.2 • (1 : Germ.CubicDivisionEndomorphism))) (0, 0) :=
    by
      simpa [Function.comp_def, Germ.cubicFunctionalFullInput] using
        (AnalyticAt.comp (x := (0, 0)) hsumBase hinput)
  have hquotient : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ Germ.cubicFunctionalQuotientOutput
        (q.sum
          (Germ.cubicDivisionOperator z.1 (a z.2 2)
              (a z.2 1) (a z.2 0),
            z.2 • (1 : Germ.CubicDivisionEndomorphism)))) (0, 0) :=
    AnalyticAt.comp (x := (0, 0))
      (Germ.cubicFunctionalQuotientOutput.analyticAt
        (q.sum
          (Germ.cubicDivisionOperator 0 (a 0 2) (a 0 1) (a 0 0),
            (0 : ℂ) • (1 : Germ.CubicDivisionEndomorphism)))) hstate
  convert hquotient using 1
  funext z
  rfl

/-- Continuous linear identification of a coordinate pair with a point of
the two dimensional source. -/
@[expose] noncomputable def planePointContinuousLinearMap :
    (ℂ × ℂ) →L[ℂ] Source 2 :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℂ ℂ ℂ)
      Germ.firstAxis +
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℂ ℂ ℂ)
      Germ.secondAxis

@[simp]
theorem planePointContinuousLinearMap_apply (z : ℂ × ℂ) :
    Germ.planePointContinuousLinearMap z =
      Germ.planePoint z.1 z.2 := by
  rfl

/-- Conditional analytic cubic preparation for an exactly normalized axis.
The only extra condition is that the base division operator lie in the
convergence ball of the Banach algebra extension. -/
theorem exists_analytic_cubicPreparation_of_base_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0)
    (hbase : Germ.cubicFunctionalInput
        (0, (0 : Germ.CubicCoefficientSpace)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius) :
    ∃ a : ℂ → Germ.CubicCoefficientSpace, ∃ Q : ℂ × ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧
      a 0 = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2) =
          Germ.cubicDivisionPolynomialValue z.1
              (a z.2 2) (a z.2 1) (a z.2 0) * Q z := by
  obtain ⟨a, ha, haZero, hrem⟩ :=
    Germ.exists_analytic_cubicCoefficientBranch p hp haxis hbase
  let Q : ℂ × ℂ → ℂ := fun z ↦
    Germ.cubicFunctionalQuotient p z.1 z.2 (a z.2)
  have hQAnalytic : AnalyticAt ℂ Q (0, 0) :=
    Germ.analyticAt_cubicFunctionalQuotient_comp
      p hp hbase a ha haZero
  have hQZero : Q (0, 0) = 1 := by
    simpa [Q, haZero] using Germ.cubicFunctionalQuotient_zero p haxis
  have hpEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.planePoint z.1 z.2 ∈ Metric.eball 0 p.radius := by
    have htendsto :=
      Germ.planePointContinuousLinearMap.continuous.continuousAt
        (x := ((0, 0) : ℂ × ℂ))
    have hball : Metric.eball 0 p.radius ∈
        nhds (Germ.planePointContinuousLinearMap (0, 0)) := by
      simpa [Germ.planePoint] using Metric.eball_mem_nhds 0 hp
    have heventually := htendsto.eventually hball
    filter_upwards [heventually] with z hz
    rw [Metric.mem_eball]
    simpa only [Germ.planePointContinuousLinearMap_apply] using hz
  have hinputAnalytic := Germ.analyticAt_cubicFunctionalFullInput a ha
  have hbaseFull : Germ.cubicFunctionalFullInput a (0, 0) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius := by
    simpa [Germ.cubicFunctionalFullInput, Germ.cubicFunctionalInput,
      haZero] using hbase
  have hxEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.cubicFunctionalFullInput a z ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.CubicDivisionEndomorphism) p).radius :=
    hinputAnalytic.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbaseFull)
  have hzeroSource : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ ((0 : ℂ), z.2)) (0, 0) :=
    analyticAt_const.prod analyticAt_snd
  have hzeroInput : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.cubicFunctionalFullInput a (0, z.2)) (0, 0) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hinputAnalytic hzeroSource)
  have hzeroEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.cubicFunctionalFullInput a (0, z.2) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.CubicDivisionEndomorphism) p).radius :=
    hzeroInput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbaseFull)
  have hremEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.cubicFunctionalRemainder p (z.2, a z.2) = 0 := by
    have hsnd : Tendsto (fun z : ℂ × ℂ ↦ z.2)
        (nhds (0, 0)) (nhds 0) := continuousAt_snd
    exact hsnd.eventually hrem
  refine ⟨a, Q, ha, haZero, hQAnalytic, hQZero, ?_⟩
  filter_upwards [hpEventually, hxEventually, hzeroEventually,
    hremEventually] with z hpz hxz hzeroz hremz
  exact Germ.cubicFunctionalPreparation_identity p z.1 z.2 (a z.2)
    hpz hxz hzeroz hremz

end Germ

end OnLeConjecture.Analytic
