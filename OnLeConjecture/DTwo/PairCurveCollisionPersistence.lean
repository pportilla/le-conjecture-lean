/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.WeightedPairNoninjectivity
public import OnLeConjecture.Analytic.ExplicitBranchCollisionPersistence

/-!
# Persistence along an analytic curve of source pairs

The first source point may be any analytic curve. The derivative in the
second source point eliminates the first two equations. A positive finite
order of the third difference then produces persistent pair collisions.
This permits ramified curves even when the first point meets the branch
axis of the ramification.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic DThree

@[expose] noncomputable def pairCurveReparametrization
    (x : ℂ → ℂ × ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) :=
  (s.1.1, (x s.1.2, orbitPointOfFinTwo s.2))

@[expose] noncomputable def pairCurvePlanePart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (x : ℂ → ℂ × ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (pairCurveReparametrization x s) 0, Phi (pairCurveReparametrization x s) 1]

@[expose] noncomputable def pairCurveThirdPart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (x : ℂ → ℂ × ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (pairCurveReparametrization x s) 2

theorem analyticAt_pairCurveReparametrization
    (x : ℂ → ℂ × ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hx : AnalyticAt ℂ x s.1.2) :
    AnalyticAt ℂ (pairCurveReparametrization x) s := by
  have ht : AnalyticAt ℂ (fun v : (ℂ × ℂ) × (Fin 2 → ℂ) => v.1.1) s :=
    analyticAt_fst.fun_comp analyticAt_fst
  have hl : AnalyticAt ℂ (fun v : (ℂ × ℂ) × (Fin 2 → ℂ) => v.1.2) s :=
    analyticAt_snd.fun_comp analyticAt_fst
  have hq (i : Fin 2) : AnalyticAt ℂ
      (fun v : (ℂ × ℂ) × (Fin 2 → ℂ) => v.2 i) s :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt s.2 |>.comp analyticAt_snd
  exact ht.prod ((hx.comp_of_eq hl rfl).prod ((hq 0).prod (hq 1)))

theorem analyticAt_pairCurvePlanePart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (x : ℂ → ℂ × ℂ) (q : Fin 2 → ℂ)
    (hx : AnalyticAt ℂ x 0)
    (hPhi : AnalyticAt ℂ Phi (0, (x 0, orbitPointOfFinTwo q))) :
    AnalyticAt ℂ (pairCurvePlanePart Phi x) (((0, 0) : ℂ × ℂ), q) := by
  have hh := hPhi.comp_of_eq (analyticAt_pairCurveReparametrization x ((0, 0), q) hx) rfl
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt _ |>.comp hh
  · exact (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt _ |>.comp hh

theorem analyticAt_pairCurveThirdPart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (x : ℂ → ℂ × ℂ) (q : Fin 2 → ℂ)
    (hx : AnalyticAt ℂ x 0)
    (hPhi : AnalyticAt ℂ Phi (0, (x 0, orbitPointOfFinTwo q))) :
    AnalyticAt ℂ (pairCurveThirdPart Phi x) (((0, 0) : ℂ × ℂ), q) := by
  exact (ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt _ |>.comp
    (hPhi.comp_of_eq (analyticAt_pairCurveReparametrization x ((0, 0), q) hx) rfl)

theorem eventually_exists_pairCurve_collisionZero_mem_nhds
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (x : ℂ → ℂ × ℂ) (v : ℂ → Fin 2 → ℂ) (q : Fin 2 → ℂ)
    (hx : AnalyticAt ℂ x 0) (hv : AnalyticAt ℂ v 0) (hv0 : v 0 = q)
    (hPhi : AnalyticAt ℂ Phi (0, (x 0, orbitPointOfFinTwo q)))
    (modelPlane : ℂ × (Fin 2 → ℂ) → Fin 2 → ℂ)
    (hspecialPlane : ∀ lambda point,
      pairCurvePlanePart Phi x ((0, lambda), point) = modelPlane (lambda, point))
    (pointDerivative : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))
    (hderivative : HasStrictFDerivAt (fun point ↦ modelPlane (0, point))
      pointDerivative q) (hinvertible : pointDerivative.IsInvertible)
    (hmodelZero : ∀ᶠ lambda in nhds 0, modelPlane (lambda, v lambda) = 0)
    (modelThird : ℂ × (Fin 2 → ℂ) → ℂ)
    (hspecialThird : ∀ lambda point,
      pairCurveThirdPart Phi x ((0, lambda), point) = modelThird (lambda, point))
    (m : ℕ) (u : ℂ → ℂ) (hm : 0 < m)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactorExplicit : ∀ᶠ lambda in nhds 0,
      modelThird (lambda, v lambda) = lambda ^ m * u lambda)
    (U : Set (ℂ × ((ℂ × ℂ) × (ℂ × ℂ))))
    (hU : U ∈ nhds (0, (x 0, orbitPointOfFinTwo q))) :
    ∀ᶠ tau in nhds 0,
      ∃ point : (ℂ × ℂ) × (ℂ × ℂ), (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let plane := pairCurvePlanePart Phi x
  let third := pairCurveThirdPart Phi x
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_pairCurvePlanePart
    · exact hx
    · exact hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_pairCurveThirdPart
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
    change pairCurvePlanePart Phi x ((0, 0), q) = 0
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
    change pairCurvePlanePart Phi x ((0, lambda), v lambda) = plane ((0, 0), q)
    rw [hspecialPlane, hplaneZero]
    exact hzeroAt
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) = lambda ^ m * u lambda := by
    filter_upwards [hbranchExplicit, hfactorExplicit] with lambda hbranchAt hfactorAt
    rw [hbranchAt]
    change pairCurveThirdPart Phi x ((0, lambda), v lambda) = _
    rw [hspecialThird]
    exact hfactorAt
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    pairCurveReparametrization x ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) :=
    (analyticAt_pairCurveReparametrization x
      (((0, 0) : ℂ × ℂ), q) hx).continuousAt.eventually hU
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird m u hm hu hu0 hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  refine ⟨(x lambda, orbitPointOfFinTwo (branch (tau, lambda))), hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

end OnLeConjecture.DTwo
