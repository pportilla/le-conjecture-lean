/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HRegularProfileCollision
public import OnLeConjecture.DThree.EInvariantRegularNoninjectivity

/-!
# Noninjectivity from a regular H profile root

The isolated collision in the regular profile chart persists through every
analytic weighted order tail.  The resulting source points are distinguished
by their first coordinates.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

theorem analyticAt_weightedPolynomialMap_hQuadratic
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) (point : ℂ × ℂ) :
    AnalyticAt ℂ
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)) point := by
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
        (hQuadraticWeightedPolynomialMap a R i)) point
  simpa [MvPolynomial.aeval_def] using
    AnalyticAt.aeval_mvPolynomial hcoordinate
      (hQuadraticWeightedPolynomialMap a R i)

theorem analyticAt_weightedInitialDifference_hQuadratic
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (weightedInitialDifference
        (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))) q := by
  change AnalyticAt ℂ
    ((fun q ↦ weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)
        (residueFirstChartPoint q)) -
      fun q ↦ weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)
        (residueSecondChartPoint q)) q
  exact
    (analyticAt_weightedPolynomialMap_hQuadratic a R
      (residueFirstChartPoint q)).fun_comp
        (analyticAt_residueFirstChartPoint q) |>.sub
      ((analyticAt_weightedPolynomialMap_hQuadratic a R
        (residueSecondChartPoint q)).fun_comp
          (analyticAt_residueSecondChartPoint q))

theorem hCollisionPlanePart_weightedRescaledPerturbation_zero
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x : ℂ → ℂ) (lambda : ℂ) (point : Fin 2 → ℂ) :
    hCollisionPlanePart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
            remainder)
        x ((0, lambda), point) =
      hCollisionPlaneDifference a x (lambda, point) := by
  funext i
  fin_cases i
  all_goals simp [hCollisionPlanePart, hCollisionReparametrization,
    hCollisionAffinePoint, hCollisionPlaneDifference,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    weightedPolynomialMap_hQuadraticWeightedPolynomialMap]

theorem hCollisionThirdPart_weightedRescaledPerturbation_zero
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x : ℂ → ℂ) (lambda : ℂ) (point : Fin 2 → ℂ) :
    hCollisionThirdPart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
            remainder)
        x ((0, lambda), point) =
      hFormEval (x lambda) 1 R -
        hFormEval (point 0) (point 1 ^ (2 * a)) R := by
  simp [hCollisionThirdPart, hCollisionReparametrization,
    hCollisionAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint,
    weightedPolynomialMap_hQuadraticWeightedPolynomialMap]

/-- The rescaled perturbation has a zero in every neighborhood of a regular
profile collision. -/
theorem eventually_exists_hWeightedRegularProfileZero_mem_nhds
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (data : HRegularSourceBranchData a N R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder
      (0, (data.firstX 0, 1)))
    (hsecond : AnalyticAt ℂ remainder
      (0, (data.secondX, data.secondT)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds
      (0, ![data.firstX 0, data.secondX, data.secondT])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
              remainder (tau, point) = 0 := by
  let initialMap :=
    weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)
  let Phi := weightedRescaledPerturbation initialMap remainder
  have hPhi : AnalyticAt ℂ Phi
      (0, ![data.firstX 0, data.secondX, data.secondT]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_hQuadratic a R _
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  exact eventually_exists_hCollisionZero_mem_nhds_of_explicit_branch
    Phi a ha data.firstX data.secondPoint data.secondX data.secondT
      data.firstX_analyticAt data.secondPoint_analyticAt
        data.secondPoint_zero data.secondT_ne_zero hPhi
      (hCollisionPlanePart_weightedRescaledPerturbation_zero
        a R remainder data.firstX)
      data.plane_zero
      (fun q : ℂ × (Fin 2 → ℂ) ↦
        hFormEval (data.firstX q.1) 1 R -
          hFormEval (q.2 0) (q.2 1 ^ (2 * a)) R)
      (hCollisionThirdPart_weightedRescaledPerturbation_zero
        a R remainder data.firstX)
      data.order data.unit data.order_pos data.unit_analyticAt
        data.unit_zero_ne data.third_factor U hU

/-- A regular profile collision excludes injectivity on every neighborhood
of the origin. -/
theorem not_neighborhood_injective_of_hWeightedRegularProfileCollision
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (data : HRegularSourceBranchData a N R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.firstX 0, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.secondX, data.secondT)) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_first
    a (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.firstX 0) data.secondX
          data.secondT ha data.firstX_zero_ne_secondX hfirst hsecond
  intro U hU
  exact eventually_exists_hWeightedRegularProfileZero_mem_nhds
    a N ha R data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- Weighted order tails exclude an injective representative at a regular
profile root. -/
theorem hRegularProfileWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (data : HRegularSourceBranchData a N R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (hQuadraticWeightedDegrees a N)
        (hQuadraticWeightedPolynomialMap a R)
          (hQuadraticWeightedPolynomialMap_isWeightedHomogeneous a N R hR)
            representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hWeightedRegularProfileCollision
    a N ha R data representative remainder
      (hexpansion (data.firstX 0, 1))
      (hexpansion (data.secondX, data.secondT))

/-- A regular root of the profile numerator, together with weighted order
tails, excludes an injective representative. -/
theorem hRegularProfileRootWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) (hz : p.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hX : hRegularProfileX z 0 ≠ 1)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  have hprofile :
      (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval z ≠ 0 := by
    simp only [hPoleProfileDenominator, Polynomial.eval_mul,
      Polynomial.eval_pow]
    have hlinearScaled : (3 : ℂ) * (z + 1) ≠ 0 :=
      mul_ne_zero (by norm_num) hlinear
    apply mul_ne_zero
    · apply pow_ne_zero
      simpa using hlinearScaled
    · exact pow_ne_zero N hden
  obtain ⟨data⟩ := exists_hRegularSourceBranchData_of_profile_root
    a N (N / 2) N ha R hR p hp z hz hlinear hden hprofile
      hW hCapitalW hX hrepresentation
  exact hRegularProfileWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R hR data representative hanalytic hzero htail

/-- The finite numerator root alternative away from the two points above
`X = 1` gives the regular endpoint when both weighted second coordinates
are nonzero. -/
theorem
    hRegularProfileNumeratorRootWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0)
    (alpha beta z : ℂ)
    (halpha : alpha ^ 2 + 2 * alpha + 4 = 0)
    (hbeta : beta ^ 2 + 2 * beta + 4 = 0)
    (halphaBeta : alpha ≠ beta)
    (hzAlpha : z ≠ alpha) (hzBeta : z ≠ beta)
    (hz : p.IsRoot z)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨hlinear, hden⟩ := h_pole_profile_factors_ne_zero
    (N / 2) N (by omega) (by omega) z hprofile
  have hX : hRegularProfileX z 0 ≠ 1 := by
    rw [h_regular_profile_X_eq_eval z 0 (by simpa using hden)]
    simpa using h_conic_param_eval_x_ne_one
      halpha hbeta halphaBeta hzAlpha hzBeta hden
  exact
    hRegularProfileRootWeightedOrderTails_not_hasInjectiveRepresentative
      a N ha R hR p hp z hz hlinear hden hW hCapitalW hX
        hrepresentation representative hanalytic hzero htail

end OnLeConjecture.DThree
