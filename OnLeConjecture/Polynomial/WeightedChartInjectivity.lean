/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedChartDegree

/-!
# Injectivity on forms of a fixed weighted degree

Setting the second coordinate equal to one preserves each coefficient
of a polynomial homogeneous for weights `(r,1)`, because its first
exponent determines its second exponent.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

/-- A coefficient of a weighted homogeneous form is recovered from the
coefficient of the corresponding first exponent in its chart polynomial. -/
theorem weighted_chart_coeff_eq
    (r D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![r, 1] D)
    (d : Fin 2 →₀ ℕ) (hd : r * d 0 + d 1 = D) :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).coeff (d 0) =
      MvPolynomial.coeff d P := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, finsetSum_coeff]
  rw [Finset.sum_eq_single d]
  · simp [MvPolynomial.monomial_fin_two]
  · intro e he hne
    have heweight : r * e 0 + e 1 = D := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using
        hP (MvPolynomial.mem_support_iff.mp he)
    have hfirst : d 0 ≠ e 0 := by
      intro heq
      apply hne
      ext i
      fin_cases i
      · exact heq.symm
      · change e 1 = d 1
        rw [heq] at hd
        omega
    simp [MvPolynomial.monomial_fin_two, coeff_X_pow, hfirst]
  · intro hnot
    have hzero : MvPolynomial.coeff d P = 0 := by
      simpa only [MvPolynomial.mem_support_iff, not_not] using hnot
    simp [hzero]

/-- Dehomogenization is injective on forms of one specified weighted
degree, including degrees not divisible by the first weight. -/
theorem eq_of_weighted_chart_eq
    (r D : ℕ) (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![r, 1] D)
    (hQ : Q.IsWeightedHomogeneous ![r, 1] D)
    (hchart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P =
      MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) Q) :
    P = Q := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : r * d 0 + d 1 = D
  · rw [← weighted_chart_coeff_eq r D P hP d hd,
      ← weighted_chart_coeff_eq r D Q hQ d hd, hchart]
  · have hdweight : Finsupp.weight ![r, 1] d ≠ D := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
    rw [hP.coeff_eq_zero d hdweight, hQ.coeff_eq_zero d hdweight]

/-- A nonzero form remains nonzero in the weighted chart. -/
theorem weighted_chart_ne_zero
    (r D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![r, 1] D) (hPne : P ≠ 0) :
    MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P ≠ 0 := by
  intro hzero
  apply hPne
  exact eq_of_weighted_chart_eq r D P 0 hP
    (MvPolynomial.isWeightedHomogeneous_zero ℂ ![r, 1] D) (by simpa using hzero)

/-- Evaluation of the chart polynomial at `z` is evaluation of the
original form at `(z,1)`. -/
theorem eval_weighted_chart (P : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).eval z =
      MvPolynomial.eval ![z, 1] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    fin_cases i <;> simp [hP]

end OnLeConjecture.Polynomial
