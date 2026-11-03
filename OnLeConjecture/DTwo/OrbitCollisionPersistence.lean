/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitTransversality
public import OnLeConjecture.DThree.ResidueRotationNoninjectivity

/-!
# Persistence of the quadratic orbit collision

The first two rescaled equations are transverse in one of the two source
points.  Analytic elimination reduces the third equation to the finite chart
polynomial at its selected root.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open OnLeConjecture.Analytic
open OnLeConjecture.DThree

theorem analyticAt_orbitInitialPolynomialMap
    (R : OrbitSourceForm) (point : ℂ × ℂ) :
    AnalyticAt ℂ
      (weightedPolynomialMap (orbitInitialPolynomialMap R)) point := by
  rw [analyticAt_pi_iff]
  intro i
  have hcoordinate (j : Fin 2) : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z j) point := by
    exact (((ContinuousLinearMap.proj (R := ℂ) j).comp
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.toContinuousLinearMap)
        |>.analyticAt point)
  change AnalyticAt ℂ
    (fun z : ℂ × ℂ ↦ MvPolynomial.eval
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
        (orbitInitialPolynomialMap R i)) point
  simpa [MvPolynomial.aeval_def] using
    AnalyticAt.aeval_mvPolynomial hcoordinate
      (orbitInitialPolynomialMap R i)

theorem orbitSecondVariablePlanePart_rescaled_zero
    (delta z : ℂ) (R : OrbitSourceForm)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (lambda : ℂ) (q : Fin 2 → ℂ) :
    orbitSecondVariablePlanePart
        (orbitPairRescaledPerturbation
          (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder)
        delta z ((0, lambda), q) =
      orbitSecondVariablePlaneDifference delta z (lambda, q) := by
  funext i
  fin_cases i <;>
    simp [orbitSecondVariablePlanePart,
      orbitSecondVariableReparametrization, orbitSecondVariablePair,
      orbitSecondVariablePlaneDifference, orbitPairRescaledPerturbation,
      orbitPairInitialDifference, orbitPlaneMap, orbitPointOfFinTwo,
      orbitFinTwoOfPoint, weightedPolynomialMap_orbitInitialPolynomialMap]

theorem orbitFirstVariablePlanePart_rescaled_zero
    (delta z : ℂ) (R : OrbitSourceForm)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (lambda : ℂ) (q : Fin 2 → ℂ) :
    orbitFirstVariablePlanePart
        (orbitPairRescaledPerturbation
          (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder)
        delta z ((0, lambda), q) =
      orbitFirstVariablePlaneDifference delta z (lambda, q) := by
  funext i
  fin_cases i <;>
    simp [orbitFirstVariablePlanePart,
      orbitFirstVariableReparametrization, orbitFirstVariablePair,
      orbitFirstVariablePlaneDifference, orbitPairRescaledPerturbation,
      orbitPairInitialDifference, orbitPlaneMap, orbitPointOfFinTwo,
      orbitFinTwoOfPoint, weightedPolynomialMap_orbitInitialPolynomialMap]

theorem orbitSecondVariableThirdPart_explicitBranch_zero
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    (R : OrbitSourceForm)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z lambda : ℂ) :
    orbitSecondVariableThirdPart
        (orbitPairRescaledPerturbation
          (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder)
        delta z
        ((0, lambda), orbitSecondVariableExplicitBranch delta z lambda) =
      (orbitParameterDehomogenize
        (orbitConicDifference delta R)).eval (z + lambda) := by
  have hpair := orbitPairInitialDifference_finiteChart
    hdelta R (z + lambda)
  change orbitPairRescaledPerturbation
      (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder
      (orbitSecondVariableReparametrization delta z
        ((0, lambda), orbitSecondVariableExplicitBranch delta z lambda)) 2 = _
  simpa [orbitSecondVariableReparametrization,
    orbitSecondVariablePair, orbitSecondVariableExplicitBranch,
    orbitPointOfFinTwo, orbitFinTwoOfPoint, orbitFiniteChartPair] using
      congrFun hpair 2

theorem orbitFirstVariableThirdPart_explicitBranch_zero
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    (R : OrbitSourceForm)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z lambda : ℂ) :
    orbitFirstVariableThirdPart
        (orbitPairRescaledPerturbation
          (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder)
        delta z
        ((0, lambda), orbitFirstVariableExplicitBranch delta z lambda) =
      (orbitParameterDehomogenize
        (orbitConicDifference delta R)).eval (z + lambda) := by
  have hpair := orbitPairInitialDifference_finiteChart
    hdelta R (z + lambda)
  change orbitPairRescaledPerturbation
      (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder
      (orbitFirstVariableReparametrization delta z
        ((0, lambda), orbitFirstVariableExplicitBranch delta z lambda)) 2 = _
  simpa [orbitFirstVariableReparametrization,
    orbitFirstVariablePair, orbitFirstVariableExplicitBranch,
    orbitPointOfFinTwo, orbitFinTwoOfPoint, orbitFiniteChartPair] using
      congrFun hpair 2

theorem exists_orbitFiniteChartThirdFactorization
    {delta : ℂ} {R : OrbitSourceForm}
    (data : OrbitFiniteChartCollisionData delta R) :
    ∃ m : ℕ, 0 < m ∧ ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        ∀ lambda : ℂ,
          (orbitParameterDehomogenize
            (orbitConicDifference delta R)).eval
              (data.parameter + lambda) = lambda ^ m * u lambda := by
  obtain ⟨hm, quotient, hdecomposition, hquotient⟩ :=
    data.exists_local_factorization
  let m := (orbitParameterDehomogenize
    (orbitConicDifference delta R)).rootMultiplicity data.parameter
  let u : ℂ → ℂ := fun lambda ↦
    quotient.eval (data.parameter + lambda)
  have hu : AnalyticAt ℂ u 0 := by
    have hargument : AnalyticAt ℂ
        (fun lambda : ℂ ↦ data.parameter + lambda) 0 :=
      analyticAt_const.add analyticAt_id
    simpa [u, MvPolynomial.aeval_def] using
      hargument.aeval_polynomial quotient
  have hu0 : u 0 ≠ 0 := by
    simpa [u] using hquotient
  refine ⟨m, hm, u, hu, hu0, ?_⟩
  intro lambda
  have heval := congrArg
    (fun p : ℂ[X] ↦ p.eval (data.parameter + lambda)) hdecomposition
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at heval
  rw [heval]
  simp only [u]
  congr 1
  ring

/-- Persistence in the chart where the second source point is eliminated. -/
theorem eventually_exists_orbitSecondVariableZero_mem_nhds
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm}
    (data : OrbitFiniteChartCollisionData delta R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder
      (0, (orbitFiniteChartPair delta data.parameter).1))
    (hsecond : AnalyticAt ℂ remainder
      (0, (orbitFiniteChartPair delta data.parameter).2))
    (hcoordinate : (orbitFiniteChartPair delta data.parameter).2.2 ≠ 0)
    (U : Set (ℂ × ((ℂ × ℂ) × (ℂ × ℂ))))
    (hU : U ∈ nhds
      (0, orbitFiniteChartPair delta data.parameter)) :
    ∀ᶠ tau in nhds 0,
      ∃ pair : (ℂ × ℂ) × (ℂ × ℂ),
        (tau, pair) ∈ U ∧
          orbitPairRescaledPerturbation
            (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder
              (tau, pair) = 0 := by
  let initialMap := weightedPolynomialMap (orbitInitialPolynomialMap R)
  let Phi := orbitPairRescaledPerturbation initialMap remainder
  let z := data.parameter
  let pair := orbitFiniteChartPair delta z
  let q := orbitSecondVariableExplicitBranch delta z 0
  let plane := orbitSecondVariablePlanePart Phi delta z
  let third := orbitSecondVariableThirdPart Phi delta z
  have hPhi : AnalyticAt ℂ Phi (0, pair) := by
    apply analyticAt_orbitPairRescaledPerturbation
    · exact analyticAt_orbitInitialPolynomialMap R pair.1
    · exact analyticAt_orbitInitialPolynomialMap R pair.2
    · simpa [pair, z] using hfirst
    · simpa [pair, z] using hsecond
  have hreparamBase :
      orbitSecondVariableReparametrization delta z
          (((0, 0) : ℂ × ℂ), q) =
        (0, pair) := by
    ext <;>
      simp [orbitSecondVariableReparametrization,
        orbitSecondVariablePair, orbitSecondVariableExplicitBranch,
        orbitPointOfFinTwo, orbitFinTwoOfPoint,
        orbitFiniteChartPair, pair, q]
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_orbitSecondVariablePlanePart
    rw [hreparamBase]
    exact hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_orbitSecondVariableThirdPart
    rw [hreparamBase]
    exact hPhi
  have hspecialPlane : ∀ lambda v,
      plane ((0, lambda), v) =
        orbitSecondVariablePlaneDifference delta z (lambda, v) := by
    intro lambda v
    exact orbitSecondVariablePlanePart_rescaled_zero
      delta z R remainder lambda v
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        orbitNegativePointDerivative pair.2.1 pair.2.2 := by
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
          fun v ↦ orbitSecondVariablePlaneDifference delta z (0, v) := by
      funext v
      exact hspecialPlane 0 v
    rw [hfixed] at hcomposition
    have hstrict :=
      hasStrictFDerivAt_orbitSecondVariablePlaneDifference_point delta z
    have hpairSecond : orbitFiniteChartSecondPoint delta z = pair.2 := by
      rfl
    rw [hpairSecond] at hstrict
    exact hcomposition.hasFDerivAt.unique hstrict.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ)
          (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    simpa [orbitNegativePointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := orbitNegativePointDerivativeEquiv
          pair.2.1 pair.2.2 hcoordinate))
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    rw [hspecialPlane]
    simpa [q] using
      orbitSecondVariablePlaneDifference_explicitBranch_zero
        hdelta R z 0
  let branch := analyticImplicitBranch plane
    (((0, 0), q)) hplane hpoint
  have hparameter : AnalyticAt ℂ
      (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hexplicit := analyticAt_orbitSecondVariableExplicitBranch delta z
  have hlift : Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ),
        orbitSecondVariableExplicitBranch delta z lambda))
      (nhds 0) (nhds (((0, 0) : ℂ × ℂ), q)) := by
    have ht := (hparameter.prod hexplicit).continuousAt
    change Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ),
        orbitSecondVariableExplicitBranch delta z lambda))
      (nhds 0)
      (nhds (((0, (0 : ℂ)) : ℂ × ℂ),
        orbitSecondVariableExplicitBranch delta z 0)) at ht
    simpa [q] using ht
  have hlocal := hplane.hasStrictFDerivAt
    |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint
  have hbranchExplicit : ∀ᶠ lambda in nhds 0,
      branch (0, lambda) =
        orbitSecondVariableExplicitBranch delta z lambda := by
    filter_upwards [hlift.eventually hlocal] with lambda hlocalAt
    apply hlocalAt.mp
    rw [hspecialPlane, hplaneZero]
    exact orbitSecondVariablePlaneDifference_explicitBranch_zero
      hdelta R z lambda
  obtain ⟨m, hm, u, hu, hu0, hfactorization⟩ :=
    exists_orbitFiniteChartThirdFactorization data
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) =
        lambda ^ m * u lambda := by
    filter_upwards [hbranchExplicit] with lambda hbranchAt
    rw [hbranchAt]
    change orbitSecondVariableThirdPart Phi delta z
      ((0, lambda), orbitSecondVariableExplicitBranch delta z lambda) = _
    rw [orbitSecondVariableThirdPart_explicitBranch_zero hdelta]
    exact hfactorization lambda
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    orbitSecondVariableReparametrization delta z ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have ht :=
      (analyticAt_orbitSecondVariableReparametrization delta z
        (((0, 0) : ℂ × ℂ), q)).continuousAt
    have ht' : Tendsto (orbitSecondVariableReparametrization delta z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, pair)) := by
      change Tendsto (orbitSecondVariableReparametrization delta z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (orbitSecondVariableReparametrization delta z
          (((0, 0), q)))) at ht
      rw [hreparamBase] at ht
      exact ht
    exact ht'.eventually (by simpa [pair, z] using hU)
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird m u hm hu hu0
      hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  let variablePoint := branch (tau, lambda)
  let outputPair := orbitSecondVariablePair delta (z + lambda) variablePoint
  refine ⟨outputPair, hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

/-- Persistence in the chart where the first source point is eliminated. -/
theorem eventually_exists_orbitFirstVariableZero_mem_nhds
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm}
    (data : OrbitFiniteChartCollisionData delta R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder
      (0, (orbitFiniteChartPair delta data.parameter).1))
    (hsecond : AnalyticAt ℂ remainder
      (0, (orbitFiniteChartPair delta data.parameter).2))
    (hcoordinate : (orbitFiniteChartPair delta data.parameter).1.2 ≠ 0)
    (U : Set (ℂ × ((ℂ × ℂ) × (ℂ × ℂ))))
    (hU : U ∈ nhds
      (0, orbitFiniteChartPair delta data.parameter)) :
    ∀ᶠ tau in nhds 0,
      ∃ pair : (ℂ × ℂ) × (ℂ × ℂ),
        (tau, pair) ∈ U ∧
          orbitPairRescaledPerturbation
            (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder
              (tau, pair) = 0 := by
  let initialMap := weightedPolynomialMap (orbitInitialPolynomialMap R)
  let Phi := orbitPairRescaledPerturbation initialMap remainder
  let z := data.parameter
  let pair := orbitFiniteChartPair delta z
  let q := orbitFirstVariableExplicitBranch delta z 0
  let plane := orbitFirstVariablePlanePart Phi delta z
  let third := orbitFirstVariableThirdPart Phi delta z
  have hPhi : AnalyticAt ℂ Phi (0, pair) := by
    apply analyticAt_orbitPairRescaledPerturbation
    · exact analyticAt_orbitInitialPolynomialMap R pair.1
    · exact analyticAt_orbitInitialPolynomialMap R pair.2
    · simpa [pair, z] using hfirst
    · simpa [pair, z] using hsecond
  have hreparamBase :
      orbitFirstVariableReparametrization delta z
          (((0, 0) : ℂ × ℂ), q) =
        (0, pair) := by
    ext <;>
      simp [orbitFirstVariableReparametrization,
        orbitFirstVariablePair, orbitFirstVariableExplicitBranch,
        orbitPointOfFinTwo, orbitFinTwoOfPoint,
        orbitFiniteChartPair, pair, q]
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_orbitFirstVariablePlanePart
    rw [hreparamBase]
    exact hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_orbitFirstVariableThirdPart
    rw [hreparamBase]
    exact hPhi
  have hspecialPlane : ∀ lambda v,
      plane ((0, lambda), v) =
        orbitFirstVariablePlaneDifference delta z (lambda, v) := by
    intro lambda v
    exact orbitFirstVariablePlanePart_rescaled_zero
      delta z R remainder lambda v
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        orbitPointDerivative pair.1.1 pair.1.2 := by
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
          fun v ↦ orbitFirstVariablePlaneDifference delta z (0, v) := by
      funext v
      exact hspecialPlane 0 v
    rw [hfixed] at hcomposition
    have hstrict :=
      hasStrictFDerivAt_orbitFirstVariablePlaneDifference_point delta z
    have hpairFirst : orbitFiniteChartFirstPoint delta z = pair.1 := by
      rfl
    rw [hpairFirst] at hstrict
    exact hcomposition.hasFDerivAt.unique hstrict.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ)
          (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    simpa [orbitPointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := orbitPointDerivativeEquiv
          pair.1.1 pair.1.2 hcoordinate))
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    rw [hspecialPlane]
    simpa [q] using
      orbitFirstVariablePlaneDifference_explicitBranch_zero
        hdelta R z 0
  let branch := analyticImplicitBranch plane
    (((0, 0), q)) hplane hpoint
  have hparameter : AnalyticAt ℂ
      (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hexplicit := analyticAt_orbitFirstVariableExplicitBranch delta z
  have hlift : Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ),
        orbitFirstVariableExplicitBranch delta z lambda))
      (nhds 0) (nhds (((0, 0) : ℂ × ℂ), q)) := by
    have ht := (hparameter.prod hexplicit).continuousAt
    change Tendsto
      (fun lambda ↦ (((0, lambda) : ℂ × ℂ),
        orbitFirstVariableExplicitBranch delta z lambda))
      (nhds 0)
      (nhds (((0, (0 : ℂ)) : ℂ × ℂ),
        orbitFirstVariableExplicitBranch delta z 0)) at ht
    simpa [q] using ht
  have hlocal := hplane.hasStrictFDerivAt
    |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint
  have hbranchExplicit : ∀ᶠ lambda in nhds 0,
      branch (0, lambda) =
        orbitFirstVariableExplicitBranch delta z lambda := by
    filter_upwards [hlift.eventually hlocal] with lambda hlocalAt
    apply hlocalAt.mp
    rw [hspecialPlane, hplaneZero]
    exact orbitFirstVariablePlaneDifference_explicitBranch_zero
      hdelta R z lambda
  obtain ⟨m, hm, u, hu, hu0, hfactorization⟩ :=
    exists_orbitFiniteChartThirdFactorization data
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) =
        lambda ^ m * u lambda := by
    filter_upwards [hbranchExplicit] with lambda hbranchAt
    rw [hbranchAt]
    change orbitFirstVariableThirdPart Phi delta z
      ((0, lambda), orbitFirstVariableExplicitBranch delta z lambda) = _
    rw [orbitFirstVariableThirdPart_explicitBranch_zero hdelta]
    exact hfactorization lambda
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    orbitFirstVariableReparametrization delta z ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have ht :=
      (analyticAt_orbitFirstVariableReparametrization delta z
        (((0, 0) : ℂ × ℂ), q)).continuousAt
    have ht' : Tendsto (orbitFirstVariableReparametrization delta z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, pair)) := by
      change Tendsto (orbitFirstVariableReparametrization delta z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (orbitFirstVariableReparametrization delta z
          (((0, 0), q)))) at ht
      rw [hreparamBase] at ht
      exact ht
    exact ht'.eventually (by simpa [pair, z] using hU)
  have hzero := eventually_exists_fullZero_of_analyticElimination_mem_nhds
    plane third q hplane hpoint hplaneZero hthird m u hm hu hu0
      hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  let variablePoint := branch (tau, lambda)
  let outputPair := orbitFirstVariablePair delta (z + lambda) variablePoint
  refine ⟨outputPair, hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

/-- The finite chart collision persists through every analytic radial
remainder. -/
theorem eventually_exists_orbitPairRescaledZero_mem_nhds
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm}
    (data : OrbitFiniteChartCollisionData delta R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder
      (0, (orbitFiniteChartPair delta data.parameter).1))
    (hsecond : AnalyticAt ℂ remainder
      (0, (orbitFiniteChartPair delta data.parameter).2))
    (U : Set (ℂ × ((ℂ × ℂ) × (ℂ × ℂ))))
    (hU : U ∈ nhds
      (0, orbitFiniteChartPair delta data.parameter)) :
    ∀ᶠ tau in nhds 0,
      ∃ pair : (ℂ × ℂ) × (ℂ × ℂ),
        (tau, pair) ∈ U ∧
          orbitPairRescaledPerturbation
            (weightedPolynomialMap (orbitInitialPolynomialMap R)) remainder
              (tau, pair) = 0 := by
  rcases data.second_coordinates_ne with hfirstCoordinate | hsecondCoordinate
  · exact eventually_exists_orbitFirstVariableZero_mem_nhds
      hdelta data remainder hfirst hsecond hfirstCoordinate U hU
  · exact eventually_exists_orbitSecondVariableZero_mem_nhds
      hdelta data remainder hfirst hsecond hsecondCoordinate U hU

end OnLeConjecture.DTwo
