/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HomogenizedResidueRotation
public import OnLeConjecture.DThree.ResidueRotationNoninjectivity

/-!
# Persistence and noninjectivity for the homogenized rotation form

This file applies analytic persistence to the third initial coordinate
`y ^ r * H(x, y ^ a)`. On the special rotation branch, `Y ^ a = 1`, so
the third difference reduces to the dehomogenized polynomial difference.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

theorem analyticAt_weightedInitialDifference_eHomogenizedResidueRotationMap
    (a N r : ℕ) (p : ℂ[X]) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (weightedInitialDifference
        (eHomogenizedResidueRotationMap a N r p)) q := by
  change AnalyticAt ℂ
    ((fun q ↦ eHomogenizedResidueRotationMap a N r p
        (residueFirstChartPoint q)) -
      fun q ↦ eHomogenizedResidueRotationMap a N r p
        (residueSecondChartPoint q)) q
  exact
    (analyticAt_eHomogenizedResidueRotationMap a N r p
      (residueFirstChartPoint q)).fun_comp
        (analyticAt_residueFirstChartPoint q) |>.sub
      ((analyticAt_eHomogenizedResidueRotationMap a N r p
        (residueSecondChartPoint q)).fun_comp
          (analyticAt_residueSecondChartPoint q))

theorem analyticAt_weightedInitialDifference_hHomogenizedResidueRotationMap
    (a N r : ℕ) (p : ℂ[X]) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (weightedInitialDifference
        (hHomogenizedResidueRotationMap a N r p)) q := by
  change AnalyticAt ℂ
    ((fun q ↦ hHomogenizedResidueRotationMap a N r p
        (residueFirstChartPoint q)) -
      fun q ↦ hHomogenizedResidueRotationMap a N r p
        (residueSecondChartPoint q)) q
  exact
    (analyticAt_hHomogenizedResidueRotationMap a N r p
      (residueFirstChartPoint q)).fun_comp
        (analyticAt_residueFirstChartPoint q) |>.sub
      ((analyticAt_hHomogenizedResidueRotationMap a N r p
        (residueSecondChartPoint q)).fun_comp
          (analyticAt_residueSecondChartPoint q))

theorem eHomogenizedRotationPlanePart_weightedRescaledPerturbation_zero
    (a N r : ℕ) (p : ℂ[X])
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation
          (eHomogenizedResidueRotationMap a N r p) remainder)
        x ((0, lambda), v) =
      eResidueRotationPlaneDifference a x (lambda, v) := by
  funext i
  fin_cases i
  · simp [rotationPlanePart, rotationReparametrization,
      rotationAffinePoint, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, eHomogenizedResidueRotationMap,
      eResidueRotationPlaneDifference]
  · simp [rotationPlanePart, rotationReparametrization,
      rotationAffinePoint, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, eHomogenizedResidueRotationMap,
      eResidueRotationPlaneDifference]

theorem hHomogenizedRotationPlanePart_weightedRescaledPerturbation_zero
    (a N r : ℕ) (p : ℂ[X])
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation
          (hHomogenizedResidueRotationMap a N r p) remainder)
        x ((0, lambda), v) =
      hResidueRotationPlaneDifference a x (lambda, v) := by
  funext i
  fin_cases i
  · simp [rotationPlanePart, rotationReparametrization,
      rotationAffinePoint, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, hHomogenizedResidueRotationMap,
      hResidueRotationPlaneDifference]
  · simp [rotationPlanePart, rotationReparametrization,
      rotationAffinePoint, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, hHomogenizedResidueRotationMap,
      hResidueRotationPlaneDifference]

theorem eHomogenizedRotationThirdPart_explicit_zero
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x zeta lambda : ℂ) (hzeta : zeta ^ a = 1) :
    rotationThirdPart
        (weightedRescaledPerturbation
          (eHomogenizedResidueRotationMap a N r p) remainder)
        x ((0, lambda), explicitRotationPlaneBranch x zeta lambda) =
      residueRotationThirdDifference r p x
        (lambda, explicitRotationPlaneBranch x zeta lambda) := by
  rw [rotationThirdPart, rotationReparametrization,
    weightedRescaledPerturbation_zero]
  change weightedThirdInitialValue a N r p (x + lambda, 1) -
      weightedThirdInitialValue a N r p (x + lambda, zeta) =
    p.eval (x + lambda) - zeta ^ r * p.eval (x + lambda)
  rw [weightedThirdInitialValue_at_one a N r p hdegree,
    weightedThirdInitialValue_at_rootOfUnity a N r p hdegree
      (x + lambda) zeta hzeta]

theorem hHomogenizedRotationThirdPart_explicit_zero
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x zeta lambda : ℂ) (hzeta : zeta ^ a = 1) :
    rotationThirdPart
        (weightedRescaledPerturbation
          (hHomogenizedResidueRotationMap a N r p) remainder)
        x ((0, lambda), explicitRotationPlaneBranch x zeta lambda) =
      residueRotationThirdDifference r p x
        (lambda, explicitRotationPlaneBranch x zeta lambda) := by
  rw [rotationThirdPart, rotationReparametrization,
    weightedRescaledPerturbation_zero]
  change weightedThirdInitialValue a N r p (x + lambda, 1) -
      weightedThirdInitialValue a N r p (x + lambda, zeta) =
    p.eval (x + lambda) - zeta ^ r * p.eval (x + lambda)
  rw [weightedThirdInitialValue_at_one a N r p hdegree,
    weightedThirdInitialValue_at_rootOfUnity a N r p hdegree
      (x + lambda) zeta hzeta]

/-- Rotation persistence needs the third special fiber identity only on the
explicit plane branch. -/
theorem eventually_exists_rotationZero_mem_nhds_of_explicitThird
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
    (hspecialThird : ∀ lambda,
      rotationThirdPart Phi x
          ((0, lambda), explicitRotationPlaneBranch x zeta lambda) =
        residueRotationThirdDifference r p x
          (lambda, explicitRotationPlaneBranch x zeta lambda))
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
      (analyticAt_rotationReparametrization x
        (((0, 0) : ℂ × ℂ), q)).continuousAt
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

/-- The rescaled perturbation of the homogenized `E` rotation map has a
zero in every neighborhood of its initial collision. -/
theorem eventually_exists_eHomogenizedWeightedRotationZero_mem_nhds
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
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
          weightedRescaledPerturbation
            (eHomogenizedResidueRotationMap a N r p)
              remainder (tau, q) = 0 := by
  let Phi := weightedRescaledPerturbation
    (eHomogenizedResidueRotationMap a N r p) remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_eHomogenizedResidueRotationMap
        a N r p ![x, x, zeta]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply eventually_exists_rotationZero_mem_nhds_of_explicitThird
    Phi (eResidueRotationPlaneDifference a x)
      (eResidueRotationPointDerivativeEquiv a x zeta ha hzetaA)
      x zeta r p hPhi
  · exact eHomogenizedRotationPlanePart_weightedRescaledPerturbation_zero
      a N r p remainder x
  · simpa [eResidueRotationPointDerivativeEquiv] using
      hasStrictFDerivAt_eResidueRotationPlaneDifference_point a x zeta
  · simpa [explicitRotationPlaneBranch] using
      e_explicitRotationPlaneBranch_eq_zero a x zeta hzetaA 0
  · exact eventually_eResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA
  · intro lambda
    exact eHomogenizedRotationThirdPart_explicit_zero
      a N r p hdegree remainder x zeta lambda hzetaA
  · exact hzetaR
  · exact hp
  · exact hx
  · exact hU

/-- The rescaled perturbation of the homogenized `H` rotation map has a
zero in every neighborhood of its initial collision. -/
theorem eventually_exists_hHomogenizedWeightedRotationZero_mem_nhds
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
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
          weightedRescaledPerturbation
            (hHomogenizedResidueRotationMap a N r p)
              remainder (tau, q) = 0 := by
  let Phi := weightedRescaledPerturbation
    (hHomogenizedResidueRotationMap a N r p) remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_hHomogenizedResidueRotationMap
        a N r p ![x, x, zeta]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply eventually_exists_rotationZero_mem_nhds_of_explicitThird
    Phi (hResidueRotationPlaneDifference a x)
      (hResidueRotationPointDerivativeEquiv a x zeta ha hzetaA)
      x zeta r p hPhi
  · exact hHomogenizedRotationPlanePart_weightedRescaledPerturbation_zero
      a N r p remainder x
  · simpa [hResidueRotationPointDerivativeEquiv] using
      hasStrictFDerivAt_hResidueRotationPlaneDifference_point a x zeta
  · simpa [explicitRotationPlaneBranch] using
      h_explicitRotationPlaneBranch_eq_zero a x zeta hzetaA 0
  · exact eventually_hResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA
  · intro lambda
    exact hHomogenizedRotationThirdPart_explicit_zero
      a N r p hdegree remainder x zeta lambda hzetaA
  · exact hzetaR
  · exact hp
  · exact hx
  · exact hU

/-- A homogenized weighted `E` rotation collision contradicts injectivity
on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_eHomogenizedWeightedRotationCollision
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (eHomogenizedResidueRotationMap a N r p)
        representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (eHomogenizedResidueRotationMap a N r p)
        representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  have hzetaOne : zeta ≠ 1 := by
    intro hzeta
    apply hzetaR
    simp [hzeta]
  apply not_neighborhood_injective_of_weightedRotationZeros
    a (homogenizedRotationDegrees a N r)
      (eHomogenizedResidueRotationMap a N r p)
        representative remainder x zeta ha hzetaOne hfirst hsecond
  intro U hU
  exact eventually_exists_eHomogenizedWeightedRotationZero_mem_nhds
    a N r p hdegree x zeta remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt ha hzetaA hzetaR hp hx U hU

/-- A homogenized weighted `H` rotation collision contradicts injectivity
on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_hHomogenizedWeightedRotationCollision
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (hHomogenizedResidueRotationMap a N r p)
        representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (hHomogenizedResidueRotationMap a N r p)
        representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  have hzetaOne : zeta ≠ 1 := by
    intro hzeta
    apply hzetaR
    simp [hzeta]
  apply not_neighborhood_injective_of_weightedRotationZeros
    a (homogenizedRotationDegrees a N r)
      (hHomogenizedResidueRotationMap a N r p)
        representative remainder x zeta ha hzetaOne hfirst hsecond
  intro U hU
  exact eventually_exists_hHomogenizedWeightedRotationZero_mem_nhds
    a N r p hdegree x zeta remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt ha hzetaA hzetaR hp hx U hU

/-- A homogenized weighted `E` rotation collision excludes an injective
representative of the associated pointed map germ. -/
theorem eHomogenizedWeightedRotationCollision_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (eHomogenizedResidueRotationMap a N r p)
        representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (eHomogenizedResidueRotationMap a N r p)
        representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ (OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction
      representative hanalytic hzero).HasInjectiveRepresentative := by
  apply OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_eHomogenizedWeightedRotationCollision
    a N r p hdegree x zeta representative remainder hfirst hsecond
      ha hzetaA hzetaR hp hx

/-- A homogenized weighted `H` rotation collision excludes an injective
representative of the associated pointed map germ. -/
theorem hHomogenizedWeightedRotationCollision_not_hasInjectiveRepresentative
    (a N r : ℕ) (p : ℂ[X]) (hdegree : p.natDegree ≤ N)
    (x zeta : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (hHomogenizedResidueRotationMap a N r p)
        representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (homogenizedRotationDegrees a N r)
      (hHomogenizedResidueRotationMap a N r p)
        representative remainder (x, zeta))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ¬ (OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction
      representative hanalytic hzero).HasInjectiveRepresentative := by
  apply OnLeConjecture.Analytic.PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hHomogenizedWeightedRotationCollision
    a N r p hdegree x zeta representative remainder hfirst hsecond
      ha hzetaA hzetaR hp hx

end OnLeConjecture.DThree
