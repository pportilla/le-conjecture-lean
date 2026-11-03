/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HExceptionalProfileNoninjectivity
public import OnLeConjecture.DThree.HFiniteBoundaryCollision
public import OnLeConjecture.DThree.HReciprocalCollision

/-!
# Weighted tail noninjectivity from the complete H profile alternative

The projective profile alternative is retained until its chart is known.
Degree drop uses the reciprocal chart.  A finite numerator root uses the pole
chart, the rescaled denominator chart, or one of the regular charts.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- Every alternative in the fixed H pole profile excludes an injective
representative through weighted order tails. -/
theorem hProfileAlternativeWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (halternative :
      p.natDegree < N / 2 + 2 * N ∨
        ∃ z : ℂ,
          z ≠ hConicOneRootPlus ∧ z ≠ hConicOneRootMinus ∧
            p.IsRoot z)
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
  rcases halternative with hdegree | ⟨z, hzPlus, hzMinus, hroot⟩
  · exact
      hReciprocalDegreeDropWeightedOrderTails_not_hasInjectiveRepresentative
        a N ha R hR p hp hdegree hrepresentation representative
          hanalytic hzero htail
  · by_cases hprofile :
      (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval z = 0
    · rcases h_pole_profile_denominator_root_classification
        (N / 2) N z hprofile with hzPole | hden
      · subst z
        exact hPoleWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR p hp hroot hrepresentation representative
            hanalytic hzero htail
      · have hzBoundary : z ^ 2 + 2 = 0 := by
          simpa [hConicParamDenominator] using hden
        exact
          hFiniteBoundaryWeightedOrderTails_not_hasInjectiveRepresentative
            a N ha R hR p hp z hzBoundary hroot hrepresentation
              representative hanalytic hzero htail
    · exact
        hEveryRegularProfileNumeratorRootWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha hN R hR p hp hConicOneRootPlus hConicOneRootMinus z
            h_conic_one_roots_equations.1 h_conic_one_roots_equations.2
              h_conic_one_roots_ne hzPlus hzMinus hroot hprofile
                hrepresentation representative hanalytic hzero htail

/-- The certified projective profile count and the exact local derivative
orders imply failure of every injective representative under weighted order
tails. -/
theorem hProjectiveProfileWeightedOrderTails_not_hasInjectiveRepresentative
    (a N kOne kTwo : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    (hdifferencePlus :
      hFiniteOrderAt hConicOneRootPlus (hConicDifference R) =
        WithZero.exp (kOne : ℤ))
    (hdifferenceMinus :
      hFiniteOrderAt hConicOneRootMinus (hConicDifference R) =
        WithZero.exp (kTwo : ℤ))
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
  have hderivativePlus := h_finite_order_hDerivativeRatFunc_at_one
    hConicOneRootPlus h_conic_one_roots_equations.1 R LambdaP LambdaQ
      hLambdaP hLambdaQ kOne (by omega) hdifferencePlus
  have hderivativeMinus := h_finite_order_hDerivativeRatFunc_at_one
    hConicOneRootMinus h_conic_one_roots_equations.2 R LambdaP LambdaQ
      hLambdaP hLambdaQ kTwo (by omega) hdifferenceMinus
  obtain ⟨p, hp, _, hrepresentation, halternative⟩ :=
    exists_hConicDifference_numerator_zero_away_from_one_fibre
      N kOne kTwo hN hkOne hkTwo R LambdaP LambdaQ hR
        hLambdaP hLambdaQ hdifferencePlus hdifferenceMinus
          hderivativePlus hderivativeMinus
  exact hProfileAlternativeWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha hN R hR p hp hrepresentation halternative representative
      hanalytic hzero htail

end OnLeConjecture.DThree
