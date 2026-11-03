/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultipleZeroElimination
public import OnLeConjecture.DThree.ResidueRotationTransversality
public import OnLeConjecture.DThree.WeightedResidueRescaling
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Tactic.FinCases

/-!
# Persistence along a residual rotation component

This file combines analytic elimination of the first two residual equations
with persistence of the multiple zero in the third equation.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The affine chart point with first coordinate `x + lambda` and remaining
coordinates supplied by the second point. -/
@[expose]
noncomputable def rotationAffinePoint
    (x lambda : ℂ) (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![x + lambda, v 0, v 1]

/-- Reparametrization by the perturbation parameter, the coordinate along
the rotation component, and the second source point. -/
@[expose]
noncomputable def rotationReparametrization
    (x : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × (Fin 3 → ℂ) :=
  (s.1.1, rotationAffinePoint x s.1.2 s.2)

/-- The first two coordinates after rotation reparametrization. -/
@[expose]
noncomputable def rotationPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (rotationReparametrization x s) 0,
    Phi (rotationReparametrization x s) 1]

/-- The third coordinate after rotation reparametrization. -/
@[expose]
noncomputable def rotationThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (rotationReparametrization x s) 2

theorem analyticAt_rotationReparametrization
    (x : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (rotationReparametrization x) s := by
  have hparameter : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1.1) s := by
    have hinner : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1) s :=
      analyticAt_fst
    have houter : AnalyticAt ℂ (fun t : ℂ × ℂ ↦ t.1) s.1 :=
      analyticAt_fst
    exact houter.fun_comp hinner
  have hcomponent : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1.2) s := by
    have hinner : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1) s :=
      analyticAt_fst
    have houter : AnalyticAt ℂ (fun t : ℂ × ℂ ↦ t.2) s.1 :=
      analyticAt_snd
    exact houter.fun_comp hinner
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.2 i) s := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt s.2).comp analyticAt_snd
  have hpoint : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        rotationAffinePoint x t.1.2 t.2) s := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · change AnalyticAt ℂ (fun t ↦ x + t.1.2) s
      exact analyticAt_const.add hcomponent
    · exact hcoordinate 0
    · exact hcoordinate 1
  exact hparameter.prod hpoint

theorem analyticAt_rotationPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi (rotationReparametrization x s)) :
    AnalyticAt ℂ (rotationPlanePart Phi x) s := by
  have hfull : AnalyticAt ℂ
      (fun t ↦ Phi (rotationReparametrization x t)) s :=
    hPhi.fun_comp (analyticAt_rotationReparametrization x s)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · have hcoordinate : AnalyticAt ℂ
        (fun t ↦ (Phi (rotationReparametrization x t)) 0) s :=
      AnalyticAt.fun_comp
        (g := fun v : Fin 3 → ℂ ↦ v 0)
        (f := fun t ↦ Phi (rotationReparametrization x t))
        ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt
          (Phi (rotationReparametrization x s))) hfull
    simpa [rotationPlanePart] using hcoordinate
  · have hcoordinate : AnalyticAt ℂ
        (fun t ↦ (Phi (rotationReparametrization x t)) 1) s :=
      AnalyticAt.fun_comp
        (g := fun v : Fin 3 → ℂ ↦ v 1)
        (f := fun t ↦ Phi (rotationReparametrization x t))
        ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt
          (Phi (rotationReparametrization x s))) hfull
    simpa [rotationPlanePart] using hcoordinate

theorem analyticAt_rotationThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (x : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi (rotationReparametrization x s)) :
    AnalyticAt ℂ (rotationThirdPart Phi x) s := by
  have hfull : AnalyticAt ℂ
      (fun t ↦ Phi (rotationReparametrization x t)) s :=
    hPhi.fun_comp (analyticAt_rotationReparametrization x s)
  have hcoordinate : AnalyticAt ℂ
      (fun t ↦ (Phi (rotationReparametrization x t)) 2) s :=
    AnalyticAt.fun_comp
      (g := fun v : Fin 3 → ℂ ↦ v 2)
      (f := fun t ↦ Phi (rotationReparametrization x t))
      ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt
        (Phi (rotationReparametrization x s))) hfull
  change AnalyticAt ℂ (fun t ↦ Phi (rotationReparametrization x t) 2) s
  exact hcoordinate

theorem analyticAt_eResidueRotationMap
    (a r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    AnalyticAt ℂ (eResidueRotationMap a r p) z := by
  have hfirst : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ z.1) z :=
    analyticAt_fst
  have hsecond : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ z.2) z :=
    analyticAt_snd
  have hpolynomial : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ p.eval z.1) z := by
    simpa [aeval_def] using hfirst.aeval_polynomial p
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.1 ^ 3 + 3 * z.2 ^ (3 * a)) z
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.1 ^ 4 + 4 * z.1 * z.2 ^ (3 * a)) z
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.2 ^ r * p.eval z.1) z
    exact (hsecond.pow r).mul hpolynomial

theorem analyticAt_hResidueRotationMap
    (a r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) :
    AnalyticAt ℂ (hResidueRotationMap a r p) z := by
  have hfirst : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ z.1) z :=
    analyticAt_fst
  have hsecond : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ z.2) z :=
    analyticAt_snd
  have hpolynomial : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ p.eval z.1) z := by
    simpa [aeval_def] using hfirst.aeval_polynomial p
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.1 ^ 3 + 3 * z.1 * z.2 ^ (2 * a)) z
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        z.1 ^ 4 + 4 * z.1 ^ 2 * z.2 ^ (2 * a) + 2 * z.2 ^ (4 * a)) z
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ z.2 ^ r * p.eval z.1) z
    exact (hsecond.pow r).mul hpolynomial

theorem analyticAt_weightedInitialDifference_eResidueRotationMap
    (a r : ℕ) (p : ℂ[X]) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (weightedInitialDifference (eResidueRotationMap a r p)) q := by
  change AnalyticAt ℂ
    ((fun q ↦ eResidueRotationMap a r p (residueFirstChartPoint q)) -
      fun q ↦ eResidueRotationMap a r p (residueSecondChartPoint q)) q
  exact
    (analyticAt_eResidueRotationMap a r p (residueFirstChartPoint q)).fun_comp
      (analyticAt_residueFirstChartPoint q) |>.sub
        ((analyticAt_eResidueRotationMap a r p (residueSecondChartPoint q)).fun_comp
          (analyticAt_residueSecondChartPoint q))

theorem analyticAt_weightedInitialDifference_hResidueRotationMap
    (a r : ℕ) (p : ℂ[X]) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (weightedInitialDifference (hResidueRotationMap a r p)) q := by
  change AnalyticAt ℂ
    ((fun q ↦ hResidueRotationMap a r p (residueFirstChartPoint q)) -
      fun q ↦ hResidueRotationMap a r p (residueSecondChartPoint q)) q
  exact
    (analyticAt_hResidueRotationMap a r p (residueFirstChartPoint q)).fun_comp
      (analyticAt_residueFirstChartPoint q) |>.sub
        ((analyticAt_hResidueRotationMap a r p (residueSecondChartPoint q)).fun_comp
          (analyticAt_residueSecondChartPoint q))

theorem eRotationPlanePart_weightedRescaledPerturbation_zero
    (a r : ℕ) (p : ℂ[X])
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation (eResidueRotationMap a r p) remainder)
        x ((0, lambda), v) =
      eResidueRotationPlaneDifference a x (lambda, v) := by
  funext i
  fin_cases i <;>
    simp [rotationPlanePart, rotationReparametrization, rotationAffinePoint,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      eResidueRotationMap, eResidueRotationPlaneDifference]

theorem hRotationPlanePart_weightedRescaledPerturbation_zero
    (a r : ℕ) (p : ℂ[X])
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation (hResidueRotationMap a r p) remainder)
        x ((0, lambda), v) =
      hResidueRotationPlaneDifference a x (lambda, v) := by
  funext i
  fin_cases i <;>
    simp [rotationPlanePart, rotationReparametrization, rotationAffinePoint,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      hResidueRotationMap, hResidueRotationPlaneDifference]

theorem eRotationThirdPart_weightedRescaledPerturbation_zero
    (a r : ℕ) (p : ℂ[X])
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationThirdPart
        (weightedRescaledPerturbation (eResidueRotationMap a r p) remainder)
        x ((0, lambda), v) =
      residueRotationThirdDifference r p x (lambda, v) := by
  simp [rotationThirdPart, rotationReparametrization, rotationAffinePoint,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    eResidueRotationMap, residueRotationThirdDifference]

theorem hRotationThirdPart_weightedRescaledPerturbation_zero
    (a r : ℕ) (p : ℂ[X])
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationThirdPart
        (weightedRescaledPerturbation (hResidueRotationMap a r p) remainder)
        x ((0, lambda), v) =
      residueRotationThirdDifference r p x (lambda, v) := by
  simp [rotationThirdPart, rotationReparametrization, rotationAffinePoint,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    hResidueRotationMap, residueRotationThirdDifference]

/-- An analytic perturbation of a rotation collision has a full zero near
the rotation component when the first two special fiber equations are
transverse and the third one has positive order. -/
theorem eventually_exists_rotationZero_of_analyticPerturbation
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
    (hzeta : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∃ rho > 0, ∀ᶠ tau in nhds 0,
      ∃ lambda ∈ closedBall (0 : ℂ) rho,
        ∃ v : Fin 2 → ℂ,
          Phi (tau, rotationAffinePoint x lambda v) = 0 := by
  let q : Fin 2 → ℂ := ![x, zeta]
  let plane := rotationPlanePart Phi x
  let third := rotationThirdPart Phi x
  have hreparamBase :
      rotationReparametrization x (((0, 0) : ℂ × ℂ), q) =
        (0, ![x, x, zeta]) := by
    ext i <;> simp [rotationReparametrization, rotationAffinePoint, q]
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
      ext v <;> rfl
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
      (nhds 0) (nhds (0, 0)) := by
    exact tendsto_const_nhds.prodMk_nhds tendsto_id
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
  obtain ⟨rho, hrho, hzero⟩ :=
    eventually_exists_fullZero_of_analyticElimination
      plane third q hplane hpoint hplaneZero hthird
        (p.rootMultiplicity x) u hmultiplicity hu hu0 hfactor
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hlambda, hplane', hthird'⟩ := htau
  refine ⟨lambda, hlambda, branch (tau, lambda), ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplane' 0
  · exact congrFun hplane' 1
  · exact hthird'

/-- Persistence for an analytic perturbation whose special fiber has the
`E` plane equations. -/
theorem eventually_exists_eRotationZero_of_analyticPerturbation
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (a : ℕ) (x zeta : ℂ) (r : ℕ) (p : ℂ[X])
    (hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]))
    (hspecialPlane : ∀ lambda v,
      rotationPlanePart Phi x ((0, lambda), v) =
        eResidueRotationPlaneDifference a x (lambda, v))
    (hspecialThird : ∀ lambda v,
      rotationThirdPart Phi x ((0, lambda), v) =
        residueRotationThirdDifference r p x (lambda, v))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∃ rho > 0, ∀ᶠ tau in nhds 0,
      ∃ lambda ∈ closedBall (0 : ℂ) rho,
        ∃ v : Fin 2 → ℂ,
          Phi (tau, rotationAffinePoint x lambda v) = 0 := by
  apply eventually_exists_rotationZero_of_analyticPerturbation
    Phi (eResidueRotationPlaneDifference a x)
      (eResidueRotationPointDerivativeEquiv a x zeta ha hzetaA)
      x zeta r p hPhi hspecialPlane
  · simpa [eResidueRotationPointDerivativeEquiv] using
      hasStrictFDerivAt_eResidueRotationPlaneDifference_point a x zeta
  · simpa [explicitRotationPlaneBranch] using
      e_explicitRotationPlaneBranch_eq_zero a x zeta hzetaA 0
  · exact eventually_eResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA
  · exact hspecialThird
  · exact hzetaR
  · exact hp
  · exact hx

/-- Persistence for an analytic perturbation whose special fiber has the
`H` plane equations. -/
theorem eventually_exists_hRotationZero_of_analyticPerturbation
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (a : ℕ) (x zeta : ℂ) (r : ℕ) (p : ℂ[X])
    (hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]))
    (hspecialPlane : ∀ lambda v,
      rotationPlanePart Phi x ((0, lambda), v) =
        hResidueRotationPlaneDifference a x (lambda, v))
    (hspecialThird : ∀ lambda v,
      rotationThirdPart Phi x ((0, lambda), v) =
        residueRotationThirdDifference r p x (lambda, v))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∃ rho > 0, ∀ᶠ tau in nhds 0,
      ∃ lambda ∈ closedBall (0 : ℂ) rho,
        ∃ v : Fin 2 → ℂ,
          Phi (tau, rotationAffinePoint x lambda v) = 0 := by
  apply eventually_exists_rotationZero_of_analyticPerturbation
    Phi (hResidueRotationPlaneDifference a x)
      (hResidueRotationPointDerivativeEquiv a x zeta ha hzetaA)
      x zeta r p hPhi hspecialPlane
  · simpa [hResidueRotationPointDerivativeEquiv] using
      hasStrictFDerivAt_hResidueRotationPlaneDifference_point a x zeta
  · simpa [explicitRotationPlaneBranch] using
      h_explicitRotationPlaneBranch_eq_zero a x zeta hzetaA 0
  · exact eventually_hResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA
  · exact hspecialThird
  · exact hzetaR
  · exact hp
  · exact hx

/-- The weighted rescaled perturbation of an `E` rotation initial map has
full zeros near the rotation component. -/
theorem eventually_exists_eWeightedRotationZero
    (a r : ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (x, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (x, zeta)))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∃ rho > 0, ∀ᶠ tau in nhds 0,
      ∃ lambda ∈ closedBall (0 : ℂ) rho,
        ∃ v : Fin 2 → ℂ,
          weightedRescaledPerturbation (eResidueRotationMap a r p)
            remainder (tau, rotationAffinePoint x lambda v) = 0 := by
  let Phi := weightedRescaledPerturbation (eResidueRotationMap a r p) remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_eResidueRotationMap
        a r p ![x, x, zeta]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply eventually_exists_eRotationZero_of_analyticPerturbation
    Phi a x zeta r p hPhi
  · exact eRotationPlanePart_weightedRescaledPerturbation_zero
      a r p remainder x
  · exact eRotationThirdPart_weightedRescaledPerturbation_zero
      a r p remainder x
  · exact ha
  · exact hzetaA
  · exact hzetaR
  · exact hp
  · exact hx

/-- The weighted rescaled perturbation of an `H` rotation initial map has
full zeros near the rotation component. -/
theorem eventually_exists_hWeightedRotationZero
    (a r : ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (x, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (x, zeta)))
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∃ rho > 0, ∀ᶠ tau in nhds 0,
      ∃ lambda ∈ closedBall (0 : ℂ) rho,
        ∃ v : Fin 2 → ℂ,
          weightedRescaledPerturbation (hResidueRotationMap a r p)
            remainder (tau, rotationAffinePoint x lambda v) = 0 := by
  let Phi := weightedRescaledPerturbation (hResidueRotationMap a r p) remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_hResidueRotationMap
        a r p ![x, x, zeta]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply eventually_exists_hRotationZero_of_analyticPerturbation
    Phi a x zeta r p hPhi
  · exact hRotationPlanePart_weightedRescaledPerturbation_zero
      a r p remainder x
  · exact hRotationThirdPart_weightedRescaledPerturbation_zero
      a r p remainder x
  · exact ha
  · exact hzetaA
  · exact hzetaR
  · exact hp
  · exact hx

end OnLeConjecture.DThree
