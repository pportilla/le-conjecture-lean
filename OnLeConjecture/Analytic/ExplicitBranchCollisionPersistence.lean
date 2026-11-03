/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HCollisionPersistence

/-!
# Analytic collision persistence along an explicit branch

An invertible derivative in the second source point eliminates the two plane
equations. A finite positive order of the remaining equation suffices, including
multiple zeros.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DThree

theorem eventually_exists_collisionZero_mem_nhds_of_explicit_branch
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (x : ℂ → ℂ) (v : ℂ → Fin 2 → ℂ) (q : Fin 2 → ℂ)
    (hx : AnalyticAt ℂ x 0) (hv : AnalyticAt ℂ v 0) (hv0 : v 0 = q)
    (hPhi : AnalyticAt ℂ Phi (0, hCollisionAffinePoint x 0 q))
    (modelPlane : ℂ × (Fin 2 → ℂ) → Fin 2 → ℂ)
    (hspecialPlane : ∀ lambda point,
      hCollisionPlanePart Phi x ((0, lambda), point) = modelPlane (lambda, point))
    (pointDerivative : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))
    (hderivative : HasStrictFDerivAt (fun point ↦ modelPlane (0, point))
      pointDerivative q) (hinvertible : pointDerivative.IsInvertible)
    (hmodelZero : ∀ᶠ lambda in nhds 0, modelPlane (lambda, v lambda) = 0)
    (modelThird : ℂ × (Fin 2 → ℂ) → ℂ)
    (hspecialThird : ∀ lambda point,
      hCollisionThirdPart Phi x ((0, lambda), point) = modelThird (lambda, point))
    (m : ℕ) (u : ℂ → ℂ) (hm : 0 < m)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactorExplicit : ∀ᶠ lambda in nhds 0,
      modelThird (lambda, v lambda) = lambda ^ m * u lambda)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, hCollisionAffinePoint x 0 q)) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ, (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let plane := hCollisionPlanePart Phi x
  let third := hCollisionThirdPart Phi x
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_hCollisionPlanePart
    · exact hx
    · exact hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_hCollisionThirdPart
    · exact hx
    · exact hPhi
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) = pointDerivative := by
    have hcomposition := hplane.hasStrictFDerivAt.comp q
      ((hasStrictFDerivAt_const (𝕜 := ℂ) ((0, 0) : ℂ × ℂ) q).prodMk
        (hasStrictFDerivAt_id q))
    have hinr :
        (0 : (Fin 2 → ℂ) →L[ℂ] (ℂ × ℂ)).prod
            (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) := by
      ext point <;> rfl
    rw [hinr] at hcomposition
    have hfixed : (fun point ↦ plane (((0, 0) : ℂ × ℂ), point)) =
        fun point ↦ modelPlane (0, point) := by
      funext point
      exact hspecialPlane 0 point
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique hderivative.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact hinvertible
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    change hCollisionPlanePart Phi x ((0, 0), q) = 0
    rw [hspecialPlane, ← hv0]
    exact hmodelZero.self_of_nhds
  let branch := analyticImplicitBranch plane (((0, 0), q)) hplane hpoint
  have hlift : Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ), v lambda))
      (nhds 0) (nhds (((0, 0) : ℂ × ℂ), q)) := by
    have hanalytic : AnalyticAt ℂ
        (fun lambda ↦ (((0, lambda) : ℂ × ℂ), v lambda)) 0 :=
      (analyticAt_const.prod analyticAt_id).prod hv
    have ht := hanalytic.continuousAt
    change Tendsto (fun lambda ↦ (((0, lambda) : ℂ × ℂ), v lambda))
      (nhds 0) (nhds (((0, 0) : ℂ × ℂ), v 0)) at ht
    simpa only [hv0] using ht
  have hlocal := hplane.hasStrictFDerivAt
    |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint
  have hbranchExplicit : ∀ᶠ lambda in nhds 0, branch (0, lambda) = v lambda := by
    filter_upwards [hlift.eventually hlocal, hmodelZero]
      with lambda hlocalAt hzeroAt
    apply hlocalAt.mp
    change hCollisionPlanePart Phi x ((0, lambda), v lambda) = plane ((0, 0), q)
    rw [hspecialPlane, hplaneZero]
    exact hzeroAt
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) = lambda ^ m * u lambda := by
    filter_upwards [hbranchExplicit, hfactorExplicit] with lambda hbranchAt hfactorAt
    rw [hbranchAt]
    change hCollisionThirdPart Phi x ((0, lambda), v lambda) = _
    rw [hspecialThird]
    exact hfactorAt
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    hCollisionReparametrization x ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) :=
    (analyticAt_hCollisionReparametrization x
      (((0, 0) : ℂ × ℂ), q) hx).continuousAt.eventually hU
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird m u hm hu hu0 hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  refine ⟨hCollisionAffinePoint x lambda (branch (tau, lambda)), hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

end OnLeConjecture.Analytic
