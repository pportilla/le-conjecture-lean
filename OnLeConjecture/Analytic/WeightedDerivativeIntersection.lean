/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedIntersectionExact
public import OnLeConjecture.Analytic.WeightedJacobianBound
public import Mathlib.FieldTheory.Perfect

/-!
# Intersection with the first derivative at a squarefree initial chart

A squarefree first initial chart is coprime to its derivative. The exact
weighted intersection theorem therefore computes the intersection with
the first-coordinate derivative of the actual analytic germ, including
its preparation unit.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- A squarefree initial chart gives finite intersection with the actual
first-coordinate derivative and the exact number `m r (m-1)`. -/
theorem weighted_intersection_first_derivative_eq_of_squarefree_chart
    (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1 ^ (r * (m - j)))
    (U : Germ 2) (hU : IsUnit U) (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hPtail : U * firstCoordinatePolynomialEvaluation P - coordinatePolynomialAlgHom 2 P₀ ∈
      weightedOrderIdeal r (r * m + 1))
    (hsquarefree : Squarefree (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀)) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)),
      PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hfinite =
          m * (r * (m - 1)) := by
  let f := U * firstCoordinatePolynomialEvaluation P
  have hdegree : r * (m - 1) + r = r * m := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ m from hm)]
  have hderivative : (MvPolynomial.pderiv (0 : Fin 2) P₀).IsWeightedHomogeneous
      ![r, 1] (r * (m - 1)) := hP₀.pderiv hdegree
  have htail : partialDerivative (0 : Fin 2) f -
      coordinatePolynomialAlgHom 2 (MvPolynomial.pderiv (0 : Fin 2) P₀) ∈
        weightedOrderIdeal r (r * (m - 1) + 1) := by
    rw [← partialDerivative_coordinatePolynomialAlgHom, ← partialDerivative_sub]
    apply partialDerivative_zero_mem_weightedOrderIdeal r (r * (m - 1) + 1) hr
    simpa only [show r * (m - 1) + 1 + r = r * m + 1 by omega] using hPtail
  have hno : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] P₀ = 0 ∧
      MvPolynomial.eval ![z, 1] (MvPolynomial.pderiv (0 : Fin 2) P₀) = 0) := by
    intro z hz
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀
    have hSep : p.Separable := PerfectField.separable_iff_squarefree.mpr hsquarefree
    have hpz : p.eval z = 0 := by
      rw [OnLeConjecture.Polynomial.eval_weighted_chart]
      exact hz.1
    have hdz : p.derivative.eval z = 0 := by
      rw [← OnLeConjecture.Polynomial.weighted_chart_pderiv_zero,
        OnLeConjecture.Polynomial.eval_weighted_chart]
      exact hz.2
    obtain ⟨A, B, hAB⟩ := hSep
    have heval := congrArg (fun q : ℂ[X] ↦ q.eval z) hAB
    simp only [eval_add, eval_mul, hpz, hdz, mul_zero, zero_add, eval_one, zero_ne_one] at heval
  exact weighted_intersection_unit_eq_any_order_of_no_common_initial_root
    r (r * (m - 1)) m hr hm P hP hPm hcoeff U (partialDerivative 0 f) hU
    P₀ (MvPolynomial.pderiv 0 P₀) hP₀ hP₀ne hderivative hPtail htail hno

end OnLeConjecture.Analytic.Germ
