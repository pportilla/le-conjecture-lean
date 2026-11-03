/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ExplicitBranchCollisionPersistence
public import OnLeConjecture.Analytic.TwoWeightRotationNoninjectivity
public import OnLeConjecture.DTwo.ResidualWeightedOrderExpansion
public import OnLeConjecture.DThree.PairRepresentativeComponents

/-!
# Residual collisions with equal second coordinates

The points `(x,1)` and `(-x,1)` are distinct when `x≠0`. A nonzero root
of the prepared odd polynomial therefore gives a collision without a
nontrivial subgroup of roots of unity. The argument includes repeated
roots of the third equation.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.Analytic.Germ OnLeConjecture.DThree

theorem PreparedOddFamily.exists_nonzero_root
    {N : ℕ} (Ψ : PreparedOddFamily N) (hN : 3 ≤ N)
    (T : ℂ) (hT : T ≠ 0) :
    ∃ x : ℂ, x ≠ 0 ∧ (Ψ.polynomial T).IsRoot x := by
  apply OnLeConjecture.Polynomial.exists_nonzero_root_of_monic_coeff_ne_zero
    (Ψ.polynomial T) N (Ψ.monic T) (Ψ.natDegree_eq T) (by omega)
  rw [Ψ.coeff_sub_two]
  exact mul_ne_zero
    (div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (by norm_num)) hT

/-- At equal second coordinates the two plane equations still have
invertible derivative in the second point. -/
theorem residual_sameCoordinate_pointDerivative_invertible
    (k L : ℕ) (hk : 0 < k) (c T x : ℂ) (hc : c ≠ 0) (hx : x ≠ 0) :
    (residualRotationPointDerivative k L c T x 1).IsInvertible := by
  have hdet : (residualRotationPointDerivative k L c T x 1).det ≠ 0 := by
    rw [det_residualRotationPointDerivative]
    exact neg_ne_zero.mpr (mul_ne_zero
      (firstInitialDifference_derivative_ne_zero hk (by simp))
      (secondInitialDifference_derivative_ne_zero hc hx))
  exact ⟨(residualRotationPointDerivative k L c T x 1
    ).toContinuousLinearEquivOfDetNeZero hdet,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩

/-- Every nonzero root gives persistent zeros of the full analytic
rescaled difference, including roots of arbitrary finite multiplicity. -/
theorem eventually_exists_residual_sameCoordinate_zero
    (k L N : ℕ) (hk : 0 < k) (c T x : ℂ) (hc : c ≠ 0) (hx : x ≠ 0)
    (Ψ : PreparedOddFamily N) (model : Ψ.BivariateModel)
    (hroot : (Ψ.polynomial T).IsRoot x)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (x, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (-x, 1)))
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, ![x, -x, 1])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ, (tau, q) ∈ U ∧
        weightedRescaledPerturbation (residualWeightedInitialMap k L N c T Ψ)
          remainder (tau, q) = 0 := by
  let Phi := weightedRescaledPerturbation (residualWeightedInitialMap k L N c T Ψ) remainder
  let first : ℂ → ℂ := fun lambda => x + lambda
  let branch : ℂ → Fin 2 → ℂ := residualExplicitPlaneBranch x 1
  have hfirstAnalytic : AnalyticAt ℂ first 0 := analyticAt_const.add analyticAt_id
  have hbranch : AnalyticAt ℂ branch 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact hfirstAnalytic.neg
    · exact analyticAt_const
  have hbranchzero : branch 0 = ![-x, 1] := by
    ext i
    fin_cases i <;> simp [branch, residualExplicitPlaneBranch]
  have hPhi : AnalyticAt ℂ Phi (0, ![x, -x, 1]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_residualWeightedInitialMap
        k L N c T Ψ model _
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  obtain ⟨hm, quotient, hquotient, hfactor⟩ :=
    exists_residualRotationThirdDifference_factorization
      (L := L) (T := T) (x := x) (eta := 1) (Psi := Ψ) (by simp) (Ψ.monic T).ne_zero hroot
  let unit : ℂ → ℂ := fun lambda => quotient.eval (x + lambda)
  have hunit : AnalyticAt ℂ unit 0 := by
    simpa [unit, Polynomial.aeval_def] using hfirstAnalytic.aeval_polynomial quotient
  have hunitzero : unit 0 ≠ 0 := by simpa [unit] using hquotient
  apply eventually_exists_collisionZero_mem_nhds_of_explicit_branch Phi first branch ![-x, 1]
    hfirstAnalytic hbranch hbranchzero
    (by simpa [first, hCollisionAffinePoint] using hPhi)
    (residualRotationPlaneDifference k L c T x) _
    (residualRotationPointDerivative k L c T x 1)
    (hasStrictFDerivAt_residualRotationPlaneDifference_point k L c T x 1)
    (residual_sameCoordinate_pointDerivative_invertible k L hk c T x hc hx) _
    (residualRotationThirdDifference L T x Ψ) _
    ((Ψ.polynomial T).rootMultiplicity x) unit hm hunit hunitzero _ U
    (by simpa [first, hCollisionAffinePoint] using hU)
  · intro lambda point
    exact residualRotationPlanePart_weightedRescaledPerturbation_zero
      k L N c T Ψ remainder x lambda point
  · exact Filter.Eventually.of_forall fun lambda =>
      residualExplicitPlaneBranch_eq_zero k L c T x 1 lambda (by simp) (by simp)
  · intro lambda point
    exact residualRotationThirdPart_weightedRescaledPerturbation_zero
      k L N c T Ψ remainder x lambda point
  · exact Filter.Eventually.of_forall hfactor

/-- A prepared odd residual initial form excludes injectivity for every
positive pair of radial weights. No nontrivial root of unity is needed. -/
theorem residual_sameCoordinate_orderTails_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (k L N : ℕ) (hk : 0 < k) (hL : 0 < L) (hN : 3 ≤ N)
    (c T : ℂ) (hc : c ≠ 0) (hT : T ≠ 0)
    (Ψ : PreparedOddFamily N) (model : Ψ.BivariateModel)
    (htail : ∀ i, g.1.component i - Germ.coordinatePolynomialAlgHom 2
      (residualWeightedInitialPolynomials k L c T Ψ model i) ∈
        Germ.twoWeightOrderIdeal L 2 (residualWeightedDegrees k L N i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨x, hx, hroot⟩ := Ψ.exists_nonzero_root hN T hT
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
      L 2 hL (by omega) (residualWeightedDegrees k L N)
      (residualWeightedInitialPolynomials k L c T Ψ model)
      (residualWeightedInitialPolynomials_isWeightedHomogeneous k L c T Ψ model)
      representative hanalytic (fun i => by rw [hcomponents i]; exact htail i)
  simp only [weightedPolynomialMap_residualWeightedInitialPolynomials] at hexpansion
  have hseparate : x ≠ -x ∨ (1 : ℂ) ≠ 1 := by
    left
    intro h
    apply hx
    linear_combination (1 / 2 : ℂ) * h
  rw [heq]
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_twoWeightSeparatedChartZeros
    L 2 (residualWeightedDegrees k L N) (residualWeightedInitialMap k L N c T Ψ)
    representative remainder x (-x) 1 hL (by omega) hseparate
    (hexpansion (x, 1)) (hexpansion (-x, 1))
  exact eventually_exists_residual_sameCoordinate_zero
    k L N hk c T x hc hx Ψ model hroot remainder
    (hexpansion (x, 1)).remainder_analyticAt
    (hexpansion (-x, 1)).remainder_analyticAt

end OnLeConjecture.DTwo
