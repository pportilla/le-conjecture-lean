/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HCollisionChart
public import OnLeConjecture.DThree.ResidueRotationNoninjectivity

/-!
# Persistence in a transverse H collision chart

An explicit analytic branch of zeros of the two plane equations identifies
the implicit branch.  A positive finite order of the third equation then
persists under analytic perturbation.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A three dimensional fibre point with prescribed first coordinate. -/
@[expose]
noncomputable def hCollisionAffinePoint
    (x : ℂ → ℂ) (lambda : ℂ) (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![x lambda, v 0, v 1]

/-- Reparametrization by perturbation, curve parameter, and second point. -/
@[expose]
noncomputable def hCollisionReparametrization
    (x : ℂ → ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × (Fin 3 → ℂ) :=
  (q.1.1, hCollisionAffinePoint x q.1.2 q.2)

@[expose]
noncomputable def hCollisionPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (hCollisionReparametrization x q) 0,
    Phi (hCollisionReparametrization x q) 1]

@[expose]
noncomputable def hCollisionThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (hCollisionReparametrization x q) 2

theorem analyticAt_hCollisionReparametrization
    (x : ℂ → ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hx : AnalyticAt ℂ x q.1.2) :
    AnalyticAt ℂ (hCollisionReparametrization x) q := by
  have hparameter : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.1.1) q :=
    analyticAt_fst.fun_comp analyticAt_fst
  have hlambda : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.1.2) q :=
    analyticAt_snd.fun_comp analyticAt_fst
  have hxComp : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ x q.1.2) q :=
    AnalyticAt.fun_comp (x := q) hx hlambda
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.2 i) q := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt q.2).comp
        (analyticAt_snd : AnalyticAt ℂ
          (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.2) q)
  have hpoint : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        hCollisionAffinePoint x q.1.2 q.2) q := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact hxComp
    · exact hcoordinate 0
    · exact hcoordinate 1
  exact hparameter.prod hpoint

theorem analyticAt_hCollisionPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hx : AnalyticAt ℂ x q.1.2)
    (hPhi : AnalyticAt ℂ Phi (hCollisionReparametrization x q)) :
    AnalyticAt ℂ (hCollisionPlanePart Phi x) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (hCollisionReparametrization x u)) q :=
    hPhi.fun_comp (analyticAt_hCollisionReparametrization x q hx)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact AnalyticAt.fun_comp
      (g := fun value : Fin 3 → ℂ ↦ value 0)
      (f := fun u ↦ Phi (hCollisionReparametrization x u))
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt
        (Phi (hCollisionReparametrization x q))) hfull
  · exact AnalyticAt.fun_comp
      (g := fun value : Fin 3 → ℂ ↦ value 1)
      (f := fun u ↦ Phi (hCollisionReparametrization x u))
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt
        (Phi (hCollisionReparametrization x q))) hfull

theorem analyticAt_hCollisionThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ → ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hx : AnalyticAt ℂ x q.1.2)
    (hPhi : AnalyticAt ℂ Phi (hCollisionReparametrization x q)) :
    AnalyticAt ℂ (hCollisionThirdPart Phi x) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (hCollisionReparametrization x u)) q :=
    hPhi.fun_comp (analyticAt_hCollisionReparametrization x q hx)
  exact AnalyticAt.fun_comp
    (g := fun value : Fin 3 → ℂ ↦ value 2)
    (f := fun u ↦ Phi (hCollisionReparametrization x u))
    ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt
      (Phi (hCollisionReparametrization x q))) hfull

/-- Persistence from an explicit finite order branch in a transverse H
chart. -/
theorem eventually_exists_hCollisionZero_mem_nhds_of_explicit_branch
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (a : ℕ) (ha : 0 < a)
    (x : ℂ → ℂ) (v : ℂ → Fin 2 → ℂ) (X T : ℂ)
    (hx : AnalyticAt ℂ x 0) (hv : AnalyticAt ℂ v 0)
    (hv0 : v 0 = ![X, T]) (hT : T ≠ 0)
    (hPhi : AnalyticAt ℂ Phi (0, ![x 0, X, T]))
    (hspecialPlane : ∀ lambda point,
      hCollisionPlanePart Phi x ((0, lambda), point) =
        hCollisionPlaneDifference a x (lambda, point))
    (hmodelZero : ∀ᶠ lambda in nhds 0,
      hCollisionPlaneDifference a x (lambda, v lambda) = 0)
    (modelThird : ℂ × (Fin 2 → ℂ) → ℂ)
    (hspecialThird : ∀ lambda point,
      hCollisionThirdPart Phi x ((0, lambda), point) =
        modelThird (lambda, point))
    (m : ℕ) (u : ℂ → ℂ) (hm : 0 < m)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactorExplicit : ∀ᶠ lambda in nhds 0,
      modelThird (lambda, v lambda) = lambda ^ m * u lambda)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![x 0, X, T])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ, (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let q : Fin 2 → ℂ := ![X, T]
  let plane := hCollisionPlanePart Phi x
  let third := hCollisionThirdPart Phi x
  have hreparamBase :
      hCollisionReparametrization x (((0, 0) : ℂ × ℂ), q) =
        (0, ![x 0, X, T]) := by
    ext i <;> simp [hCollisionReparametrization,
      hCollisionAffinePoint, q]
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_hCollisionPlanePart
    · exact hx
    · simpa [hreparamBase] using hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_hCollisionThirdPart
    · exact hx
    · simpa [hreparamBase] using hPhi
  let pointEquiv := hCollisionPointDerivativeEquiv a ha X T hT
  have hmodelDerivative : HasStrictFDerivAt
      (fun point ↦ hCollisionPlaneDifference a x (0, point))
      (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) q := by
    simpa [pointEquiv, q, hCollisionPointDerivativeEquiv] using
      hasStrictFDerivAt_hCollisionPlaneDifference_point a x X T
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
      ext point <;> rfl
    rw [hinr] at hcomposition
    have hfixed : (fun point ↦
        plane (((0, 0) : ℂ × ℂ), point)) =
        fun point ↦ hCollisionPlaneDifference a x (0, point) := by
      funext point
      exact hspecialPlane 0 point
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique hmodelDerivative.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    change hCollisionPlanePart Phi x ((0, 0), q) = 0
    rw [hspecialPlane]
    have hzeroAt := hmodelZero.self_of_nhds
    rw [hv0] at hzeroAt
    simpa [q] using hzeroAt
  let branch := analyticImplicitBranch
    plane (((0, 0), q)) hplane hpoint
  have hbranchBase : branch (0, 0) = q :=
    analyticImplicitBranch_apply_base
      plane (((0, 0), q)) hplane hpoint
  have hparameter : AnalyticAt ℂ
      (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hlift : Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ), v lambda))
      (nhds 0) (nhds (((0, 0) : ℂ × ℂ), q)) := by
    have hanalytic : AnalyticAt ℂ
        (fun lambda ↦ (((0, lambda) : ℂ × ℂ), v lambda)) 0 :=
      hparameter.prod hv
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ), v lambda))
      (nhds 0)
      (nhds (((0, (0 : ℂ)) : ℂ × ℂ), v 0)) at ht
    rw [hv0] at ht
    exact ht
  have hlocal := hplane.hasStrictFDerivAt
    |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint
  have hbranchExplicit : ∀ᶠ lambda in nhds 0,
      branch (0, lambda) = v lambda := by
    filter_upwards [hlift.eventually hlocal, hmodelZero]
      with lambda hlocalAt hzeroAt
    apply hlocalAt.mp
    change hCollisionPlanePart Phi x ((0, lambda), v lambda) =
      plane ((0, 0), q)
    rw [hspecialPlane, hplaneZero]
    exact hzeroAt
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) =
        lambda ^ m * u lambda := by
    filter_upwards [hbranchExplicit, hfactorExplicit]
      with lambda hbranchAt hfactorAt
    rw [hbranchAt]
    change hCollisionThirdPart Phi x ((0, lambda), v lambda) = _
    rw [hspecialThird]
    exact hfactorAt
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    hCollisionReparametrization x ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have ht := (analyticAt_hCollisionReparametrization x
      (((0, 0) : ℂ × ℂ), q) hx).continuousAt
    have ht' : Tendsto (hCollisionReparametrization x)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, ![x 0, X, T])) := by
      change Tendsto (hCollisionReparametrization x)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (hCollisionReparametrization x (((0, 0), q)))) at ht
      rw [hreparamBase] at ht
      exact ht
    exact ht'.eventually hU
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird m u hm hu hu0 hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  let point := hCollisionAffinePoint x lambda (branch (tau, lambda))
  refine ⟨point, hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

end OnLeConjecture.DThree
