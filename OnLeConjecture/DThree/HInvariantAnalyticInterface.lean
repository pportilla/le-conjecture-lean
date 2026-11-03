/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HAllProfileNoninjectivity
public import OnLeConjecture.DThree.HInvariantDescent
public import OnLeConjecture.DThree.HPositiveLocalOrders

/-!
# The invariant H collision from analytic tails

This module joins the algebraic descent, the literal Jacobian divisibilities,
the local orders on the residual conic, and the weighted analytic collision
theorem.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A homogeneous `H` form outside the base ring excludes an injective
representative when the analytic corrections have larger weighted order. -/
theorem hInvariantWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hnotbase : R ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R))
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
  have hdifference : hConicDifference R ≠ 0 :=
    hConicDifference_ne_zero_of_not_mem_base R N hR hnotbase
  obtain ⟨LambdaP, LambdaQ, hLambdaP, hLambdaQ⟩ :=
    exists_h_jacobian_quotients_of_literal_divisibilities R hPdiv hQdiv
  obtain ⟨kOne, hkOne, horderOne⟩ :=
    exists_h_positive_local_order_at_one
      h_conic_one_roots_equations.1 R hR hdifference
  obtain ⟨kTwo, hkTwo, horderTwo⟩ :=
    exists_h_positive_local_order_at_one
      h_conic_one_roots_equations.2 R hR hdifference
  exact hProjectiveProfileWeightedOrderTails_not_hasInjectiveRepresentative
    a N kOne kTwo ha hN hkOne hkTwo R LambdaP LambdaQ hR
      hLambdaP hLambdaQ horderOne horderTwo representative
        hanalytic hzero htail

end OnLeConjecture.DThree
