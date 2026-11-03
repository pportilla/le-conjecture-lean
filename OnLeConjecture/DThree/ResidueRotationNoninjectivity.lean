/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Noninjectivity
public import OnLeConjecture.DThree.ResidueRotationMultiplePersistence

/-!
# Noninjectivity from a residual rotation component

Zeros of the rescaled perturbation persist in every neighborhood of the
initial collision. The weighted radial substitution converts these zeros into
equal values at distinct source points converging to the origin.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Analytic elimination produces a full zero in every prescribed
neighborhood of the base point. -/
theorem eventually_exists_fullZero_of_analyticElimination_mem_nhds
    (plane : ((ℂ × ℂ) × E) → E)
    (third : ((ℂ × ℂ) × E) → ℂ)
    (q : E)
    (hplane : AnalyticAt ℂ plane ((0, 0), q))
    (hpoint :
      (fderiv ℂ plane ((0, 0), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) E).IsInvertible)
    (hplaneZero : plane ((0, 0), q) = 0)
    (hthird : AnalyticAt ℂ third ((0, 0), q))
    (m : ℕ) (u : ℂ → ℂ) (hm : 0 < m)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda),
        analyticImplicitBranch plane ((0, 0), q) hplane hpoint (0, lambda)) =
          lambda ^ m * u lambda)
    (U : Set (((ℂ × ℂ) × E))) (hU : U ∈ nhds ((0, 0), q)) :
    ∀ᶠ tau in nhds 0,
      ∃ lambda,
        ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hpoint
            (tau, lambda)) ∈ U ∧
        plane ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hpoint
            (tau, lambda)) = 0 ∧
        third ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hpoint
            (tau, lambda)) = 0 := by
  let branch := analyticImplicitBranch plane ((0, 0), q) hplane hpoint
  have hbranch : AnalyticAt ℂ branch (0, 0) :=
    analyticAt_analyticImplicitBranch plane ((0, 0), q) hplane hpoint
  have hbranchBase : branch (0, 0) = q :=
    analyticImplicitBranch_apply_base plane ((0, 0), q) hplane hpoint
  let scalar : ℂ × ℂ → ℂ := fun p ↦ third (p, branch p)
  have hlift : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ (p, branch p)) (0, 0) :=
    analyticAt_id.prod hbranch
  have hliftBase :
      (((0, 0) : ℂ × ℂ), branch (0, 0)) = (((0, 0) : ℂ × ℂ), q) := by
    rw [hbranchBase]
  have hscalar : AnalyticAt ℂ scalar (0, 0) := by
    simpa [scalar, Function.comp_def, hliftBase] using
      hthird.comp_of_eq hlift hliftBase
  have hplaneBranch : ∀ᶠ p in nhds (0, 0), plane (p, branch p) = 0 := by
    filter_upwards
      [eventually_analyticImplicitBranch_eq
        plane ((0, 0), q) hplane hpoint] with p hp
    simpa [branch, hplaneZero] using hp
  have hmemU : ∀ᶠ p in nhds (0, 0), (p, branch p) ∈ U := by
    have htendsto : Tendsto (fun p : ℂ × ℂ ↦ (p, branch p))
        (nhds (0, 0)) (nhds (((0, 0) : ℂ × ℂ), q)) := by
      have ht := hlift.continuousAt
      change Tendsto (fun p : ℂ × ℂ ↦ (p, branch p))
        (nhds (0, 0))
          (nhds (((0, 0) : ℂ × ℂ), branch (0, 0))) at ht
      rw [hbranchBase] at ht
      exact ht
    exact htendsto.eventually hU
  have hlocal : ∀ᶠ p in nhds (0, 0),
      plane (p, branch p) = 0 ∧ (p, branch p) ∈ U :=
    hplaneBranch.and hmemU
  obtain ⟨R, hR, hlocalOnBall⟩ := Metric.mem_nhds_iff.mp hlocal
  have hfactorScalar : ∀ᶠ lambda in nhds 0,
      scalar (0, lambda) = lambda ^ m * u lambda := by
    simpa [scalar, branch] using hfactor
  obtain ⟨r, hr, hrR, hscalarZero⟩ :=
    eventually_exists_zero_of_analyticAt_of_specialFiber_factorization_lt
      scalar m u hm hscalar hu hu0 hfactorScalar R hR
  have htau : ball (0 : ℂ) (R - r) ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 (sub_pos.mpr hrR)
  filter_upwards [hscalarZero, htau] with tau hzero htau'
  obtain ⟨lambda, hlambda, hthirdZero⟩ := hzero
  have hparameterMem : ((tau, lambda) : ℂ × ℂ) ∈ ball 0 R := by
    rw [mem_ball, Prod.dist_eq]
    have htauDist : dist tau 0 < R - r := by
      simpa [mem_ball] using htau'
    have hlambdaDist : dist lambda 0 ≤ r := by
      simpa [mem_closedBall] using hlambda
    apply max_lt
    · simpa using (show dist tau 0 < R by linarith)
    · simpa using (lt_of_le_of_lt hlambdaDist hrR)
  obtain ⟨hplaneAt, hmemAt⟩ := hlocalOnBall hparameterMem
  refine ⟨lambda, ?_, ?_, ?_⟩
  · simpa [branch] using hmemAt
  · simpa [branch] using hplaneAt
  · simpa [scalar, branch] using hthirdZero

/-- A perturbed rotation collision has a zero in every neighborhood of the
initial collision. -/
theorem eventually_exists_rotationZero_mem_nhds_of_analyticPerturbation
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (modelPlane : ℂ × (Fin 2 → ℂ) → Fin 2 → ℂ)
    (pointEquiv : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
    (x zeta : ℂ) (r : ℕ) (p : ℂ[X])
    (hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]))
    (hspecialPlane : ∀ lambda v,
      rotationPlanePart Phi x ((0, lambda), v) = modelPlane (lambda, v))
    (hmodelDerivative : HasStrictFDerivAt (fun v ↦ modelPlane (0, v))
      (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) ![x, zeta])
    (hmodelZero : modelPlane (0, ![x, zeta]) = 0)
    (hmodelLocal : ∀ᶠ s in nhds (0, ![x, zeta]),
      modelPlane s = 0 ↔ explicitRotationPlaneBranch x zeta s.1 = s.2)
    (hspecialThird : ∀ lambda v,
      rotationThirdPart Phi x ((0, lambda), v) =
        residueRotationThirdDifference r p x (lambda, v))
    (hzeta : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![x, x, zeta])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ, (tau, q) ∈ U ∧ Phi (tau, q) = 0 := by
  let q : Fin 2 → ℂ := ![x, zeta]
  let plane := rotationPlanePart Phi x
  let third := rotationThirdPart Phi x
  have hreparamBase :
      rotationReparametrization x (((0, 0) : ℂ × ℂ), q) =
        (0, ![x, x, zeta]) := by
    apply Prod.ext
    · simp [rotationReparametrization, rotationAffinePoint, q]
    · funext i
      fin_cases i
      · simp [rotationReparametrization, rotationAffinePoint, q]
      · simp [rotationReparametrization, rotationAffinePoint, q]
      · simp [rotationReparametrization, rotationAffinePoint, q]
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_rotationPlanePart
    simpa [hreparamBase] using hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_rotationThirdPart
    simpa [hreparamBase] using hPhi
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) := by
    have hcomposition := hplane.hasStrictFDerivAt.comp q
      ((hasStrictFDerivAt_const (𝕜 := ℂ) ((0, 0) : ℂ × ℂ) q).prodMk
        (hasStrictFDerivAt_id q))
    have hinr :
        (0 : (Fin 2 → ℂ) →L[ℂ] (ℂ × ℂ)).prod
            (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [hinr] at hcomposition
    have hfixed :
        (fun v ↦ plane (((0, 0) : ℂ × ℂ), v)) =
          fun v ↦ modelPlane (0, v) := by
      funext v
      exact hspecialPlane 0 v
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique hmodelDerivative.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    simpa [plane, q] using hspecialPlane 0 ![x, zeta] |>.trans hmodelZero
  let branch := analyticImplicitBranch plane (((0, 0), q)) hplane hpoint
  have hbranch : AnalyticAt ℂ branch (0, 0) :=
    analyticAt_analyticImplicitBranch plane (((0, 0), q)) hplane hpoint
  have hbranchBase : branch (0, 0) = q :=
    analyticImplicitBranch_apply_base plane (((0, 0), q)) hplane hpoint
  have hparameter : Tendsto (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ))
      (nhds 0) (nhds (0, 0)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hbranchSpecial : Tendsto (fun lambda ↦ branch (0, lambda))
      (nhds 0) (nhds q) := by
    have ht := hbranch.continuousAt.tendsto.comp hparameter
    rw [hbranchBase] at ht
    simpa [Function.comp_def] using ht
  have hlift : Tendsto (fun lambda ↦ (lambda, branch (0, lambda)))
      (nhds 0) (nhds (0, q)) :=
    tendsto_id.prodMk_nhds hbranchSpecial
  have hplaneBranch : ∀ᶠ parameter in nhds (0, 0),
      plane (parameter, branch parameter) = 0 := by
    filter_upwards
      [eventually_analyticImplicitBranch_eq
        plane (((0, 0), q)) hplane hpoint] with parameter hparameter'
    simpa [hplaneZero] using hparameter'
  have hplaneBranchSpecial : ∀ᶠ lambda in nhds 0,
      modelPlane (lambda, branch (0, lambda)) = 0 := by
    filter_upwards [hparameter.eventually hplaneBranch] with lambda hlambda
    rw [← hspecialPlane lambda (branch (0, lambda))]
    exact hlambda
  have hbranchExplicit : ∀ᶠ lambda in nhds 0,
      branch (0, lambda) = explicitRotationPlaneBranch x zeta lambda := by
    filter_upwards [hplaneBranchSpecial, hlift.eventually hmodelLocal]
      with lambda hzero hlocal
    exact (hlocal.mp hzero).symm
  obtain ⟨hmultiplicity, quotient, hquotient, hfactorization⟩ :=
    exists_explicitRotationThirdDifference_factorization hzeta hp hx
  let u : ℂ → ℂ := fun lambda ↦ quotient.eval (x + lambda)
  have hu : AnalyticAt ℂ u 0 := by
    have hargument : AnalyticAt ℂ (fun lambda : ℂ ↦ x + lambda) 0 :=
      analyticAt_const.add analyticAt_id
    simpa [u, aeval_def] using hargument.aeval_polynomial quotient
  have hu0 : u 0 ≠ 0 := by
    simpa [u] using hquotient
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) =
        lambda ^ p.rootMultiplicity x * u lambda := by
    filter_upwards [hbranchExplicit] with lambda hbranch'
    change rotationThirdPart Phi x ((0, lambda), branch (0, lambda)) =
      lambda ^ p.rootMultiplicity x * quotient.eval (x + lambda)
    rw [hbranch', hspecialThird]
    exact hfactorization lambda
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    rotationReparametrization x ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have htendsto :=
      (analyticAt_rotationReparametrization x (((0, 0) : ℂ × ℂ), q)).continuousAt
    have htendsto' : Tendsto (rotationReparametrization x)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, ![x, x, zeta])) := by
      change Tendsto (rotationReparametrization x)
        (nhds (((0, 0) : ℂ × ℂ), q))
          (nhds (rotationReparametrization x (((0, 0), q)))) at htendsto
      rw [hreparamBase] at htendsto
      exact htendsto
    exact htendsto'.eventually hU
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird
      (p.rootMultiplicity x) u hmultiplicity hu hu0 hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  let v := branch (tau, lambda)
  refine ⟨rotationAffinePoint x lambda v, ?_, ?_⟩
  · exact hmem
  · funext i
    fin_cases i
    · exact congrFun hplaneAt 0
    · exact congrFun hplaneAt 1
    · exact hthirdAt

/-- The rescaled perturbation of an `E` rotation map has a zero in every
neighborhood of its initial collision. -/
theorem eventually_exists_eWeightedRotationZero_mem_nhds
    (a r : ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (x, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (x, zeta)))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![x, x, zeta])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ,
        (tau, q) ∈ U ∧
          weightedRescaledPerturbation (eResidueRotationMap a r p)
            remainder (tau, q) = 0 := by
  let Phi := weightedRescaledPerturbation (eResidueRotationMap a r p) remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_eResidueRotationMap
        a r p ![x, x, zeta]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply eventually_exists_rotationZero_mem_nhds_of_analyticPerturbation
    Phi (eResidueRotationPlaneDifference a x)
      (eResidueRotationPointDerivativeEquiv a x zeta ha hzetaA)
      x zeta r p hPhi
  · exact eRotationPlanePart_weightedRescaledPerturbation_zero
      a r p remainder x
  · simpa [eResidueRotationPointDerivativeEquiv] using
      hasStrictFDerivAt_eResidueRotationPlaneDifference_point a x zeta
  · simpa [explicitRotationPlaneBranch] using
      e_explicitRotationPlaneBranch_eq_zero a x zeta hzetaA 0
  · exact eventually_eResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA
  · exact eRotationThirdPart_weightedRescaledPerturbation_zero
      a r p remainder x
  · exact hzetaR
  · exact hp
  · exact hx
  · exact hU

/-- The rescaled perturbation of an `H` rotation map has a zero in every
neighborhood of its initial collision. -/
theorem eventually_exists_hWeightedRotationZero_mem_nhds
    (a r : ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (x, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (x, zeta)))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![x, x, zeta])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ,
        (tau, q) ∈ U ∧
          weightedRescaledPerturbation (hResidueRotationMap a r p)
            remainder (tau, q) = 0 := by
  let Phi := weightedRescaledPerturbation (hResidueRotationMap a r p) remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_hResidueRotationMap
        a r p ![x, x, zeta]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply eventually_exists_rotationZero_mem_nhds_of_analyticPerturbation
    Phi (hResidueRotationPlaneDifference a x)
      (hResidueRotationPointDerivativeEquiv a x zeta ha hzetaA)
      x zeta r p hPhi
  · exact hRotationPlanePart_weightedRescaledPerturbation_zero
      a r p remainder x
  · simpa [hResidueRotationPointDerivativeEquiv] using
      hasStrictFDerivAt_hResidueRotationPlaneDifference_point a x zeta
  · simpa [explicitRotationPlaneBranch] using
      h_explicitRotationPlaneBranch_eq_zero a x zeta hzetaA 0
  · exact eventually_hResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA
  · exact hRotationThirdPart_weightedRescaledPerturbation_zero
      a r p remainder x
  · exact hzetaR
  · exact hp
  · exact hx
  · exact hU

/-- Zeros of a rescaled rotation perturbation contradict injectivity of the
original representative on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_weightedRotationZeros
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ≠ 1)
    (hfirst : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (x, zeta))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![x, x, zeta]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              weightedRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  intro hinjective
  obtain ⟨s, hs, hsInjective⟩ := hinjective
  let base : Fin 3 → ℂ := ![x, x, zeta]
  have hfirstLift : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueFirstChartPoint t.2))
      (nhds (0, base)) (nhds (0, (x, 1))) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.1, residueFirstChartPoint t.2)) (0, base) :=
      analyticAt_fst.prod
        (AnalyticAt.comp (x := (0, base))
          (analyticAt_residueFirstChartPoint base) analyticAt_snd)
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueFirstChartPoint (0, base).2)) at ht
    simpa [base, residueFirstChartPoint] using ht
  have hsecondLift : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0, (x, zeta))) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.1, residueSecondChartPoint t.2)) (0, base) :=
      analyticAt_fst.prod
        (AnalyticAt.comp (x := (0, base))
          (analyticAt_residueSecondChartPoint base) analyticAt_snd)
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueSecondChartPoint (0, base).2)) at ht
    simpa [base, residueSecondChartPoint] using ht
  have hfirstExpansion := hfirstLift.eventually hfirst.expansion
  have hsecondExpansion := hsecondLift.eventually hsecond.expansion
  have hfirstSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueFirstChartPoint t.2))
      (0, base) := by
    have hparameter : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.1) (0, base) :=
      analyticAt_fst
    have hcoordinate (i : Fin 3) : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) :=
      by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (x := (0, base))
            ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
              analyticAt_snd)
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ a * t.2 0, t.1 * 1)) (0, base)
    exact ((hparameter.pow a).mul (hcoordinate 0)).prod
      (hparameter.mul analyticAt_const)
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueSecondChartPoint t.2))
      (0, base) := by
    have hparameter : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.1) (0, base) :=
      analyticAt_fst
    have hcoordinate (i : Fin 3) : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) :=
      by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (x := (0, base))
            ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
              analyticAt_snd)
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ a * t.2 1, t.1 * t.2 2)) (0, base)
    exact ((hparameter.pow a).mul (hcoordinate 1)).prod
      (hparameter.mul (hcoordinate 2))
  have hfirstSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueFirstChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hfirstSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds (weightedRadialSource a (0, base).1
        (residueFirstChartPoint (0, base).2))) at ht
    have hvalue : weightedRadialSource a (0, base).1
        (residueFirstChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, weightedRadialSource, residueFirstChartPoint,
          zero_pow ha.ne']
      · simp [base, weightedRadialSource, residueFirstChartPoint,
          zero_pow ha.ne']
    rw [hvalue] at ht
    exact ht
  have hsecondSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hsecondSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds (weightedRadialSource a (0, base).1
        (residueSecondChartPoint (0, base).2))) at ht
    have hvalue : weightedRadialSource a (0, base).1
        (residueSecondChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, weightedRadialSource, residueSecondChartPoint,
          zero_pow ha.ne']
      · simp [base, weightedRadialSource, residueSecondChartPoint,
          zero_pow ha.ne']
    rw [hvalue] at ht
    exact ht
  have hthirdCoordinate : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 2)
      (nhds (0, base)) (nhds zeta) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 2) (0, base) := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0, base))
          ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt
            base) analyticAt_snd)
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 2)
      (nhds (0, base)) (nhds ((0, base).2 2)) at ht
    simpa [base] using ht
  let conditions : ℂ × (Fin 3 → ℂ) → Prop := fun t ↦
      (∀ i,
        representative
            (weightedRadialSource a t.1
              (residueFirstChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueFirstChartPoint t.2) i +
              t.1 * remainder (t.1, residueFirstChartPoint t.2) i)) ∧
      (∀ i,
        representative
            (weightedRadialSource a t.1
              (residueSecondChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueSecondChartPoint t.2) i +
              t.1 * remainder (t.1, residueSecondChartPoint t.2) i)) ∧
      weightedRadialSource a t.1 (residueFirstChartPoint t.2) ∈ s ∧
      weightedRadialSource a t.1 (residueSecondChartPoint t.2) ∈ s ∧
      t.2 2 ≠ 1
  have hconditions : ∀ᶠ t in nhds (0, base), conditions t := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hs, hsecondSource.eventually hs,
      hthirdCoordinate.eventually_ne hzeta] with
      t hfirstAt hsecondAt hfirstMem hsecondMem hthirdNe
    exact ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hthirdNe⟩
  have hconditionsSet : {t | conditions t} ∈ nhds (0, base) := by
    change ∀ᶠ t in nhds (0, base), conditions t
    exact hconditions
  have hzero := hpersist {t | conditions t} (by simpa [base] using hconditionsSet)
  have hall : ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      ∃ q : Fin 3 → ℂ,
        conditions (tau, q) ∧
        weightedRescaledPerturbation initialMap remainder (tau, q) = 0 ∧
        tau ≠ 0 := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with tau htau htauMem
    obtain ⟨q, hcondition, hzeroAt⟩ := htau
    refine ⟨q, hcondition, hzeroAt, ?_⟩
    simpa using htauMem
  obtain ⟨tau, q, hcondition, hzeroAt, htau⟩ := hall.exists
  obtain ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hqNe⟩ := hcondition
  have hvalues :
      representative
          (weightedRadialSource a tau (residueFirstChartPoint q)) =
        representative
          (weightedRadialSource a tau (residueSecondChartPoint q)) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative
            (weightedRadialSource a tau (residueFirstChartPoint q)) i -
          representative
            (weightedRadialSource a tau (residueSecondChartPoint q)) i =
        tau ^ degrees i *
          weightedRescaledPerturbation initialMap remainder (tau, q) i :=
        representative_difference_eq_weightedRescaledPerturbation
          a degrees initialMap representative remainder tau q
            hfirstAt hsecondAt i
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      weightedRadialSource a tau (residueFirstChartPoint q) ≠
        weightedRadialSource a tau (residueSecondChartPoint q) := by
    intro hequal
    have hsecondCoordinate := congrArg Prod.snd hequal
    simp only [weightedRadialSource, residueFirstChartPoint,
      residueSecondChartPoint] at hsecondCoordinate
    have hqOne : q 2 = 1 := by
      apply mul_left_cancel₀ htau
      simpa [mul_comm] using hsecondCoordinate.symm
    exact hqNe hqOne
  exact hsourcesNe (hsInjective hfirstMem hsecondMem hvalues)

/-- A weighted `E` rotation collision contradicts injectivity on every
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_eWeightedRotationCollision
    (a r : ℕ) (degrees : Fin 3 → ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a degrees
      (eResidueRotationMap a r p) representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a degrees
      (eResidueRotationMap a r p) representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  have hzetaOne : zeta ≠ 1 := by
    intro hzeta
    apply hzetaR
    simp [hzeta]
  apply not_neighborhood_injective_of_weightedRotationZeros
    a degrees (eResidueRotationMap a r p) representative remainder
      x zeta ha hzetaOne hfirst hsecond
  intro U hU
  exact eventually_exists_eWeightedRotationZero_mem_nhds
    a r p x zeta remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt ha hzetaA hzetaR hp hx U hU

/-- A weighted `H` rotation collision contradicts injectivity on every
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_hWeightedRotationCollision
    (a r : ℕ) (degrees : Fin 3 → ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a degrees
      (hResidueRotationMap a r p) representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a degrees
      (hResidueRotationMap a r p) representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  have hzetaOne : zeta ≠ 1 := by
    intro hzeta
    apply hzetaR
    simp [hzeta]
  apply not_neighborhood_injective_of_weightedRotationZeros
    a degrees (hResidueRotationMap a r p) representative remainder
      x zeta ha hzetaOne hfirst hsecond
  intro U hU
  exact eventually_exists_hWeightedRotationZero_mem_nhds
    a r p x zeta remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt ha hzetaA hzetaR hp hx U hU

/-- A weighted `E` rotation collision excludes an injective representative
of the associated pointed map germ. -/
theorem eWeightedRotationCollision_not_hasInjectiveRepresentative
    (a r : ℕ) (degrees : Fin 3 → ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasWeightedRadialExpansionAt a degrees
      (eResidueRotationMap a r p) representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a degrees
      (eResidueRotationMap a r p) representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ (OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction
      representative hanalytic hzero).HasInjectiveRepresentative := by
  apply OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_eWeightedRotationCollision
    a r degrees p x zeta representative remainder hfirst hsecond
      ha hzetaA hzetaR hp hx

/-- A weighted `H` rotation collision excludes an injective representative
of the associated pointed map germ. -/
theorem hWeightedRotationCollision_not_hasInjectiveRepresentative
    (a r : ℕ) (degrees : Fin 3 → ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasWeightedRadialExpansionAt a degrees
      (hResidueRotationMap a r p) representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a degrees
      (hResidueRotationMap a r p) representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ (OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction
      representative hanalytic hzero).HasInjectiveRepresentative := by
  apply OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hWeightedRotationCollision
    a r degrees p x zeta representative remainder hfirst hsecond
      ha hzetaA hzetaR hp hx

end OnLeConjecture.DThree
