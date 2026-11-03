/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedChartDegree
public import OnLeConjecture.Analytic.WeightedInitialFormFactor
public import OnLeConjecture.Polynomial.WeightedInitialPair

/-!
# The degree bound from an analytic Jacobian divisor

The second-coordinate divisor of an analytic Jacobian passes to its
weighted initial form. The degree of the dehomogenized Jacobian consequently
satisfies the inequality used by the weighted initial-pair argument.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

/-- Differentiation in the first variable commutes with setting the
second variable equal to one. -/
theorem weighted_chart_pderiv_zero (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) (MvPolynomial.pderiv 0 P) =
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    fin_cases i
    · simp [hP]
      ring
    · simp [hP]

/-- The weighted Euler identity computes the other derivative on the
chart where the second variable is one. -/
theorem weighted_chart_pderiv_one
    (a D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) :
    MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) (MvPolynomial.pderiv 1 P) =
      C (D : ℂ) * MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P -
        C (a : ℂ) * X *
          (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).derivative := by
  have heuler := congrArg (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]))
    hP.sum_weight_X_mul_pderiv
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_add, map_mul, MvPolynomial.aeval_X,
    one_mul, weighted_chart_pderiv_zero, nsmul_eq_mul, map_natCast,
    Nat.cast_one] at heuler
  simp only [map_natCast]
  linear_combination heuler

/-- The chart of a homogeneous Jacobian is the weighted derivative
polynomial, with the actual weighted degrees as coefficients. -/
theorem weighted_chart_jacobian
    (a D L : ℕ) (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] L) :
    MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) (jacobian P Q) =
      C (L : ℂ) * (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).derivative *
        MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q -
      C (D : ℂ) * MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P *
        (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q).derivative := by
  rw [jacobian, map_sub, map_mul, map_mul, weighted_chart_pderiv_zero,
    weighted_chart_pderiv_zero, weighted_chart_pderiv_one a D P hP,
    weighted_chart_pderiv_one a L Q hQ]
  ring

end OnLeConjecture.Polynomial

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- The degree inequality follows from the actual analytic divisibility
and strict weighted tails, provided the polynomial Jacobian is nonzero. -/
theorem weighted_jacobian_chart_degree_bound
    (a D L T : ℕ) (ha : 0 < a) (haD : a ≤ D) (haL : a ≤ L)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] L)
    (f g : Germ 2)
    (hf : f - coordinatePolynomialAlgHom 2 P ∈ weightedOrderIdeal a (D + 1))
    (hg : g - coordinatePolynomialAlgHom 2 Q ∈ weightedOrderIdeal a (L + 1))
    (hdiv : coordinate (1 : Fin 2) ^ T ∣ jacobian f g)
    (hJac : OnLeConjecture.Polynomial.jacobian P Q ≠ 0) :
    a * (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X])
      (OnLeConjecture.Polynomial.jacobian P Q)).natDegree + T ≤ D + L - a - 1 := by
  have hhom : (OnLeConjecture.Polynomial.jacobian P Q).IsWeightedHomogeneous
      ![a, 1] (D + L - a - 1) := by
    convert OnLeConjecture.Polynomial.isWeightedHomogeneous_jacobian
      ![a, 1] P Q D L hP hQ haD (by dsimp; omega)
        haL (by dsimp; omega) using 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have htail := jacobian_sub_coordinatePolynomial_mem_weightedOrderIdeal
    a D L ha haD haL P Q hP hQ f g hf hg
  have htail' : jacobian f g - coordinatePolynomialAlgHom 2
      (OnLeConjecture.Polynomial.jacobian P Q) ∈
        weightedOrderIdeal a (D + L - a - 1 + 1) := by
    simpa only [show D + L - a - 1 + 1 = D + L - a by omega] using htail
  have hfactor := secondVariable_pow_dvd_of_dvd_weighted_initial_form
    a (D + L - a - 1) T (jacobian f g)
      (OnLeConjecture.Polynomial.jacobian P Q) hhom htail' hdiv
  exact OnLeConjecture.Polynomial.weighted_chart_degree_inequality_of_second_power_dvd
    a (D + L - a - 1) T ha (OnLeConjecture.Polynomial.jacobian P Q) hhom hJac hfactor

/-- The analytic divisor bounds the degree of the one-variable polynomial
`Omega` used in the manuscript's initial-pair argument. -/
theorem weightedPairOmega_degree_bound_of_analytic_divisibility
    (a m L T : ℕ) (ha : 0 < a) (hm : 0 < m) (haL : a ≤ L)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] (a * m))
    (hQ : Q.IsWeightedHomogeneous ![a, 1] L)
    (f g : Germ 2)
    (hf : f - coordinatePolynomialAlgHom 2 P ∈ weightedOrderIdeal a (a * m + 1))
    (hg : g - coordinatePolynomialAlgHom 2 Q ∈ weightedOrderIdeal a (L + 1))
    (hdiv : coordinate (1 : Fin 2) ^ T ∣ jacobian f g)
    (hOmega : OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (a : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q) ≠ 0) :
    a * (OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (a : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q)).natDegree + T ≤
        a * m + L - a - 1 := by
  have hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X])
      (OnLeConjecture.Polynomial.jacobian P Q) =
        OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (a : ℂ)
          (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P)
          (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q) := by
    rw [OnLeConjecture.Polynomial.weighted_chart_jacobian a (a * m) L P Q hP hQ]
    simp only [OnLeConjecture.Polynomial.weightedPairOmega, Nat.cast_mul, map_mul]
    ring
  have hJac : OnLeConjecture.Polynomial.jacobian P Q ≠ 0 := by
    intro hzero
    apply hOmega
    rw [← hchart, hzero, map_zero]
  rw [← hchart]
  exact weighted_jacobian_chart_degree_bound a (a * m) L T ha
    (by nlinarith) haL P Q hP hQ f g hf hg hdiv hJac

/-- The same analytic bound without a lower bound on `L`. Multiplication
of the second germ by the first reduces to the preceding degree range. -/
theorem weightedPairOmega_degree_bound_unrestricted
    (a m L T : ℕ) (ha : 0 < a) (hm : 0 < m)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] (a * m))
    (hQ : Q.IsWeightedHomogeneous ![a, 1] L)
    (hPchart : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).natDegree = m)
    (f g : Germ 2)
    (hf : f - coordinatePolynomialAlgHom 2 P ∈ weightedOrderIdeal a (a * m + 1))
    (hg : g - coordinatePolynomialAlgHom 2 Q ∈ weightedOrderIdeal a (L + 1))
    (hdiv : coordinate (1 : Fin 2) ^ T ∣ jacobian f g)
    (hOmega : OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (a : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q) ≠ 0) :
    a * (OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (a : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q)).natDegree + T ≤
        a * m + L - a - 1 := by
  by_cases haL : a ≤ L
  · exact weightedPairOmega_degree_bound_of_analytic_divisibility
      a m L T ha hm haL P Q hP hQ f g hf hg hdiv hOmega
  let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P
  let omegaPoly := OnLeConjecture.Polynomial.weightedPairOmega m (L : ℂ) (a : ℂ)
    p (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q)
  have hp : p ≠ 0 := by
    intro hzero
    change p.natDegree = m at hPchart
    rw [hzero, natDegree_zero] at hPchart
    omega
  have hgOrder : g ∈ weightedOrderIdeal a L := by
    have htail := weightedOrderIdeal_antitone a L (L + 1) ha (by omega) hg
    have hpoly := coordinatePolynomial_mem_weightedOrderIdeal a L ha hQ
    have hsum := (weightedOrderIdeal a L).add_mem htail hpoly
    simpa only [sub_add_cancel] using hsum
  have hproductTail : f * g - coordinatePolynomialAlgHom 2 (P * Q) ∈
      weightedOrderIdeal a (a * m + L + 1) := by
    have hfirst := weightedOrderIdeal_mul_mem a (a * m + 1) L ha hf hgOrder
    have hsecond := weightedOrderIdeal_mul_mem a (a * m) (L + 1) ha
      (coordinatePolynomial_mem_weightedOrderIdeal a (a * m) ha hP) hg
    have heq : f * g - coordinatePolynomialAlgHom 2 (P * Q) =
        (f - coordinatePolynomialAlgHom 2 P) * g +
          coordinatePolynomialAlgHom 2 P * (g - coordinatePolynomialAlgHom 2 Q) := by
      rw [map_mul]
      ring
    rw [heq]
    apply Ideal.add_mem
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst
    · simpa [Nat.add_assoc] using hsecond
  have hdiv' : coordinate (1 : Fin 2) ^ T ∣ jacobian f (f * g) := by
    rw [jacobian_mul_right, jacobian_self]
    simpa only [mul_zero, add_zero, zero_mul, zero_add] using dvd_mul_of_dvd_right hdiv f
  have hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X])
      (OnLeConjecture.Polynomial.jacobian P (P * Q)) = p * omegaPoly := by
    rw [OnLeConjecture.Polynomial.weighted_chart_jacobian
      a (a * m) (a * m + L) P (P * Q) hP (hP.mul hQ)]
    simp only [p, omegaPoly, OnLeConjecture.Polynomial.weightedPairOmega,
      map_mul, Nat.cast_add, Nat.cast_mul, map_add, derivative_mul]
    ring
  have hJac : OnLeConjecture.Polynomial.jacobian P (P * Q) ≠ 0 := by
    intro hzero
    have hprod : p * omegaPoly = 0 := by rw [← hchart, hzero, map_zero]
    exact mul_ne_zero hp hOmega hprod
  have hbound := weighted_jacobian_chart_degree_bound
    a (a * m) (a * m + L) T ha (by nlinarith) (by nlinarith)
      P (P * Q) hP (hP.mul hQ) f (f * g) hf hproductTail hdiv' hJac
  rw [hchart, natDegree_mul hp hOmega, hPchart, Nat.mul_add] at hbound
  change a * omegaPoly.natDegree + T ≤ a * m + L - a - 1
  dsimp only [omegaPoly, p] at ⊢
  omega

end OnLeConjecture.Analytic.Germ
