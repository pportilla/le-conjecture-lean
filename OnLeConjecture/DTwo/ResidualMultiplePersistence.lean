/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ResidueRotationNoninjectivity
public import OnLeConjecture.DTwo.ResidualWeightedRescaling

/-!
# Persistence of the residual collision

Analytic elimination of the first two equations reduces the perturbed
collision to persistence of the positive multiplicity zero in the third
equation.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- Zeros of the weighted perturbation occur in every neighborhood of the
certified residual collision. -/
theorem eventually_exists_residualWeightedZero_mem_nhds
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (model : Psi.BivariateModel)
    (certificate : InitialCollisionCertificate k L N c T Psi)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (certificate.x, 1)))
    (hsecond : AnalyticAt ℂ remainder
      (0, (-certificate.x, certificate.eta)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds
      (0, ![certificate.x, -certificate.x, certificate.eta])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ,
        (tau, q) ∈ U ∧
          weightedRescaledPerturbation
            (residualWeightedInitialMap k L N c T Psi) remainder
              (tau, q) = 0 := by
  let initialMap := residualWeightedInitialMap k L N c T Psi
  let Phi := weightedRescaledPerturbation initialMap remainder
  let q : Fin 2 → ℂ := ![-certificate.x, certificate.eta]
  let base : Fin 3 → ℂ :=
    ![certificate.x, -certificate.x, certificate.eta]
  let plane := rotationPlanePart Phi certificate.x
  let third := rotationThirdPart Phi certificate.x
  have hPhi : AnalyticAt ℂ Phi (0, base) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_residualWeightedInitialMap
        k L N c T Psi model base
    · simpa [base, residueFirstChartPoint] using hfirst
    · simpa [base, residueSecondChartPoint] using hsecond
  have hreparamBase :
      rotationReparametrization certificate.x
          (((0, 0) : ℂ × ℂ), q) =
        (0, base) := by
    ext i <;>
      simp [rotationReparametrization, rotationAffinePoint, q, base]
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_rotationPlanePart
    simpa [hreparamBase] using hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_rotationThirdPart
    simpa [hreparamBase] using hPhi
  have hspecialPlane : ∀ lambda v,
      rotationPlanePart Phi certificate.x ((0, lambda), v) =
        residualRotationPlaneDifference k L c T certificate.x
          (lambda, v) := by
    exact residualRotationPlanePart_weightedRescaledPerturbation_zero
      k L N c T Psi remainder certificate.x
  have hspecialThird : ∀ lambda v,
      rotationThirdPart Phi certificate.x ((0, lambda), v) =
        residualRotationThirdDifference L T certificate.x Psi
          (lambda, v) := by
    exact residualRotationThirdPart_weightedRescaledPerturbation_zero
      k L N c T Psi remainder certificate.x
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        (certificate.residualRotationPointDerivativeEquiv :
          (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) := by
    have hcomposition := hplane.hasStrictFDerivAt.comp q
      ((hasStrictFDerivAt_const (𝕜 := ℂ) ((0, 0) : ℂ × ℂ) q).prodMk
        (hasStrictFDerivAt_id q))
    have hinr :
        (0 : (Fin 2 → ℂ) →L[ℂ] (ℂ × ℂ)).prod
            (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) := by
      ext v <;> rfl
    rw [hinr] at hcomposition
    have hfixed :
        (fun v ↦ plane (((0, 0) : ℂ × ℂ), v)) =
          fun v ↦ residualRotationPlaneDifference k L c T
            certificate.x (0, v) := by
      funext v
      exact hspecialPlane 0 v
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique
      (hasStrictFDerivAt_residualRotationPlaneDifference_point
        k L c T certificate.x certificate.eta).hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    change rotationPlanePart Phi certificate.x ((0, 0), q) = 0
    rw [hspecialPlane 0 q]
    simpa [q] using certificate.residualRotationPlaneDifference_zero
  let branch := analyticImplicitBranch plane
    (((0, 0), q)) hplane hpoint
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
      residualRotationPlaneDifference k L c T certificate.x
        (lambda, branch (0, lambda)) = 0 := by
    filter_upwards [hparameter.eventually hplaneBranch] with lambda hlambda
    rw [← hspecialPlane lambda (branch (0, lambda))]
    exact hlambda
  have hbranchExplicit : ∀ᶠ lambda in nhds 0,
      branch (0, lambda) =
        residualExplicitPlaneBranch certificate.x certificate.eta lambda := by
    filter_upwards
      [hplaneBranchSpecial,
        hlift.eventually
          (eventually_residualRotationPlaneDifference_eq_zero_iff_explicitBranch
            certificate)]
      with lambda hzero hlocal
    exact (hlocal.mp hzero).symm
  have hp : Psi.polynomial T ≠ 0 := (Psi.monic T).ne_zero
  have hx : (Psi.polynomial T).IsRoot certificate.x := by
    have hzero := certificate.third_difference_zero
    rw [restrictedThirdDifference_eq_two_mul] at hzero
    simpa using hzero
  obtain ⟨hmultiplicity, quotient, hquotient, hfactorization⟩ :=
    exists_residualRotationThirdDifference_factorization
      certificate.eta_pow_L hp hx
  let u : ℂ → ℂ := fun lambda ↦ quotient.eval (certificate.x + lambda)
  have hu : AnalyticAt ℂ u 0 := by
    have hargument : AnalyticAt ℂ
        (fun lambda : ℂ ↦ certificate.x + lambda) 0 :=
      analyticAt_const.add analyticAt_id
    simpa [u, aeval_def] using hargument.aeval_polynomial quotient
  have hu0 : u 0 ≠ 0 := by
    simpa [u] using hquotient
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) =
        lambda ^ (Psi.polynomial T).rootMultiplicity certificate.x *
          u lambda := by
    filter_upwards [hbranchExplicit] with lambda hbranch'
    change rotationThirdPart Phi certificate.x
      ((0, lambda), branch (0, lambda)) = _
    rw [hbranch', hspecialThird]
    exact hfactorization lambda
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    rotationReparametrization certificate.x ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have htendsto :=
      (analyticAt_rotationReparametrization certificate.x
        (((0, 0) : ℂ × ℂ), q)).continuousAt
    have htendsto' : Tendsto (rotationReparametrization certificate.x)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, base)) := by
      change Tendsto (rotationReparametrization certificate.x)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (rotationReparametrization certificate.x (((0, 0), q))))
        at htendsto
      rw [hreparamBase] at htendsto
      exact htendsto
    exact htendsto'.eventually (by simpa [base] using hU)
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird
      ((Psi.polynomial T).rootMultiplicity certificate.x) u
        hmultiplicity hu hu0 hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  let v := branch (tau, lambda)
  refine ⟨rotationAffinePoint certificate.x lambda v, hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

end OnLeConjecture.DTwo
