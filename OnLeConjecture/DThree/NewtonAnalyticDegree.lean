/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedInitialFormDivisibility
public import OnLeConjecture.DThree.NewtonPolynomialCore
public import OnLeConjecture.DThree.WeightedResidueChartPolynomial

/-!
# The analytic degree bound in the cubic Newton argument

The weighted Jacobian of a depressed cubic initial form and an arbitrary
weighted homogeneous second initial form dehomogenizes to the polynomial
`newtonOmega`. Divisibility of the analytic Jacobian by a sufficiently high
power of the second coordinate then forces this polynomial to have degree at
most one.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A weighted homogeneous polynomial of degree smaller than the first
weight is independent of the first variable. -/
theorem pderiv_zero_eq_zero_of_isWeightedHomogeneous_degree_lt
    (a ell : ℕ) (Q : MvPolynomial (Fin 2) ℂ)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] ell) (hella : ell < a) :
    MvPolynomial.pderiv (0 : Fin 2) Q = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_pderiv]
  have hcoefficient :
      MvPolynomial.coeff
          (d + Finsupp.single (0 : Fin 2) 1) Q = 0 := by
    apply hQ.coeff_eq_zero
    intro hweight
    have hweight' :
        (d 0 + 1) * a + d 1 = ell := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
        Fin.sum_univ_two] using hweight
    have hle : a ≤ ell := by
      calc
        a = 1 * a := by simp
        _ ≤ (d 0 + 1) * a := Nat.mul_le_mul_right a (Nat.le_add_left 1 _)
        _ ≤ (d 0 + 1) * a + d 1 := Nat.le_add_right _ _
        _ = ell := hweight'
    exact (not_lt_of_ge hle) hella
  rw [hcoefficient, zero_mul]

/-- Dehomogenization commutes with differentiation in the first variable. -/
theorem weightedDehomogenize_pderiv_zero
    (Q : MvPolynomial (Fin 2) ℂ) :
    weightedDehomogenize (MvPolynomial.pderiv (0 : Fin 2) Q) =
      (weightedDehomogenize Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      rw [map_add, map_add, hP, hQ,
        map_add, derivative_add]
  | mul_X P i hP =>
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
        map_mul, hP, derivative_mul]
      fin_cases i
      · simp [weightedDehomogenize_X_zero]
      · simp [weightedDehomogenize_X_one]

/-- The weighted Euler identity determines the dehomogenization of the
derivative in the second variable. -/
theorem weightedDehomogenize_pderiv_one_of_isWeightedHomogeneous
    (a ell : ℕ) (Q : MvPolynomial (Fin 2) ℂ)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] ell) :
    weightedDehomogenize (MvPolynomial.pderiv (1 : Fin 2) Q) =
      (ell : ℂ[X]) * weightedDehomogenize Q -
        (a : ℂ[X]) * (X * (weightedDehomogenize Q).derivative) := by
  have hEuler := hQ.sum_weight_X_mul_pderiv
  have hEval := congrArg weightedDehomogenize hEuler
  simp only [map_sum, map_nsmul, map_mul] at hEval
  rw [Fin.sum_univ_two, weightedDehomogenize_X_zero,
    weightedDehomogenize_X_one, one_mul,
    weightedDehomogenize_pderiv_zero] at hEval
  norm_num at hEval
  apply eq_sub_of_add_eq
  rw [add_comm]
  exact hEval

/-- The weighted Jacobian of the cubic form and a weighted homogeneous form
dehomogenizes to the Newton differential polynomial. -/
theorem weightedDehomogenize_jacobian_weightedCubicPolynomial
    (a ell : ℕ) (A B : ℂ) (Q : MvPolynomial (Fin 2) ℂ)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] ell) :
    weightedDehomogenize
        (OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B) Q) =
      newtonOmega ell a A B (weightedDehomogenize Q) := by
  rw [OnLeConjecture.Polynomial.jacobian, map_sub, map_mul, map_mul,
    weightedDehomogenize_pderiv_zero,
    weightedDehomogenize_pderiv_one_of_isWeightedHomogeneous a ell Q hQ,
    weightedDehomogenize_weightedCubicPolynomial]
  simp_rw [weightedDehomogenize_pderiv_zero]
  simp [weightedCubicPolynomial, weightedDehomogenize,
    newtonOmega, cubic]
  simp only [C_ofNat]
  ring

/-- The Jacobian of a cubic weighted initial form and a positive degree
weighted initial form has the polynomial Jacobian as its strict weighted
initial form. No comparison between `a` and `ell` is required. -/
theorem jacobian_sub_weightedCubicPolynomial_mem_weightedOrderIdeal
    (a ell : ℕ) (ha : 0 < a) (hell : 0 < ell)
    (A B : ℂ) (Q : MvPolynomial (Fin 2) ℂ)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] ell)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (ell + 1)) :
    Germ.jacobian f g - Germ.coordinatePolynomialAlgHom 2
        (OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B) Q) ∈
      Germ.weightedOrderIdeal a (ell + 2 * a) := by
  let P := weightedCubicPolynomial a A B
  let PGerm := Germ.coordinatePolynomialAlgHom 2 P
  let QGerm := Germ.coordinatePolynomialAlgHom 2 Q
  have hP : P.IsWeightedHomogeneous ![a, 1] (3 * a) := by
    exact weightedCubicPolynomial_isWeightedHomogeneous a A B
  have hfzero :
      Germ.partialDerivative (0 : Fin 2) f -
          Germ.partialDerivative 0 PGerm ∈
        Germ.weightedOrderIdeal a (2 * a + 1) := by
    rw [← Germ.partialDerivative_sub]
    have hraw :=
      Germ.partialDerivative_zero_mem_weightedOrderIdeal_sub
        a (3 * a + 1) ha hf
    simpa only [show 3 * a + 1 - a = 2 * a + 1 by omega] using hraw
  have hfone :
      Germ.partialDerivative (1 : Fin 2) f -
          Germ.partialDerivative 1 PGerm ∈
        Germ.weightedOrderIdeal a (3 * a) := by
    rw [← Germ.partialDerivative_sub]
    exact Germ.partialDerivative_one_mem_weightedOrderIdeal
      a (3 * a) ha hf
  have hgzero :
      Germ.partialDerivative (0 : Fin 2) g -
          Germ.partialDerivative 0 QGerm ∈
        Germ.weightedOrderIdeal a (ell + 1 - a) := by
    rw [← Germ.partialDerivative_sub]
    exact Germ.partialDerivative_zero_mem_weightedOrderIdeal_sub
      a (ell + 1) ha hg
  have hgone :
      Germ.partialDerivative (1 : Fin 2) g -
          Germ.partialDerivative 1 QGerm ∈
        Germ.weightedOrderIdeal a ell := by
    rw [← Germ.partialDerivative_sub]
    exact Germ.partialDerivative_one_mem_weightedOrderIdeal a ell ha hg
  have hPzero : Germ.partialDerivative (0 : Fin 2) PGerm ∈
      Germ.weightedOrderIdeal a (2 * a) := by
    change Germ.partialDerivative (0 : Fin 2)
      (Germ.coordinatePolynomialAlgHom 2 P) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
      a (2 * a) ha (hP.pderiv (by
        norm_num
        omega))
  have hPone : Germ.partialDerivative (1 : Fin 2) PGerm ∈
      Germ.weightedOrderIdeal a (3 * a - 1) := by
    change Germ.partialDerivative (1 : Fin 2)
      (Germ.coordinatePolynomialAlgHom 2 P) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
      a (3 * a - 1) ha (hP.pderiv (by
        norm_num
        omega))
  have hQzero : Germ.partialDerivative (0 : Fin 2) QGerm ∈
      Germ.weightedOrderIdeal a (ell - a) := by
    by_cases haell : a ≤ ell
    · change Germ.partialDerivative (0 : Fin 2)
        (Germ.coordinatePolynomialAlgHom 2 Q) ∈ _
      rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
      exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
        a (ell - a) ha (hQ.pderiv (Nat.sub_add_cancel haell))
    · have hsub : ell - a = 0 := by omega
      rw [hsub, Germ.weightedOrderIdeal_zero_eq_top]
      exact Submodule.mem_top
  have hQone : Germ.partialDerivative (1 : Fin 2) QGerm ∈
      Germ.weightedOrderIdeal a (ell - 1) := by
    change Germ.partialDerivative (1 : Fin 2)
      (Germ.coordinatePolynomialAlgHom 2 Q) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
      a (ell - 1) ha (hQ.pderiv (Nat.sub_add_cancel hell))
  have hfzeroOrder : Germ.partialDerivative (0 : Fin 2) f ∈
      Germ.weightedOrderIdeal a (2 * a) := by
    have htail := Germ.weightedOrderIdeal_antitone
      a (2 * a) (2 * a + 1) ha (by omega) hfzero
    have hsum := (Germ.weightedOrderIdeal a (2 * a)).add_mem
      htail hPzero
    convert hsum using 1
    ring
  have hgoneOrder : Germ.partialDerivative (1 : Fin 2) g ∈
      Germ.weightedOrderIdeal a (ell - 1) := by
    have htail := Germ.weightedOrderIdeal_antitone
      a (ell - 1) ell ha (by omega) hgone
    have hsum := (Germ.weightedOrderIdeal a (ell - 1)).add_mem
      htail hQone
    convert hsum using 1
    ring
  have hgzeroOrder : Germ.partialDerivative (0 : Fin 2) g ∈
      Germ.weightedOrderIdeal a (ell - a) := by
    have hthreshold : ell - a ≤ ell + 1 - a := by omega
    have htail := Germ.weightedOrderIdeal_antitone
      a (ell - a) (ell + 1 - a) ha hthreshold hgzero
    have hsum := (Germ.weightedOrderIdeal a (ell - a)).add_mem
      htail hQzero
    convert hsum using 1
    ring
  have hfirstTail := Germ.weightedOrderIdeal_mul_mem
    a (2 * a + 1) (ell - 1) ha hfzero hgoneOrder
  have hfirstPolynomial := Germ.weightedOrderIdeal_mul_mem
    a (2 * a) ell ha hPzero hgone
  have hfirst :
      Germ.partialDerivative (0 : Fin 2) f *
            Germ.partialDerivative (1 : Fin 2) g -
          Germ.partialDerivative 0 PGerm *
            Germ.partialDerivative 1 QGerm ∈
        Germ.weightedOrderIdeal a (ell + 2 * a) := by
    have htail :
        (Germ.partialDerivative (0 : Fin 2) f -
              Germ.partialDerivative 0 PGerm) *
            Germ.partialDerivative (1 : Fin 2) g ∈
          Germ.weightedOrderIdeal a (ell + 2 * a) := by
      simpa only [show 2 * a + 1 + (ell - 1) = ell + 2 * a by omega] using
        hfirstTail
    have hpolynomial :
        Germ.partialDerivative (0 : Fin 2) PGerm *
            (Germ.partialDerivative (1 : Fin 2) g -
              Germ.partialDerivative 1 QGerm) ∈
          Germ.weightedOrderIdeal a (ell + 2 * a) := by
      simpa only [show 2 * a + ell = ell + 2 * a by omega] using
        hfirstPolynomial
    have hsum := (Germ.weightedOrderIdeal a (ell + 2 * a)).add_mem
      htail hpolynomial
    convert hsum using 1
    ring
  have hsecondTailRaw := Germ.weightedOrderIdeal_mul_mem
    a (3 * a) (ell - a) ha hfone hgzeroOrder
  have hsecondPolynomialRaw := Germ.weightedOrderIdeal_mul_mem
    a (3 * a - 1) (ell + 1 - a) ha hPone hgzero
  have hsecondTail :
      (Germ.partialDerivative (1 : Fin 2) f -
          Germ.partialDerivative 1 PGerm) *
        Germ.partialDerivative (0 : Fin 2) g ∈
          Germ.weightedOrderIdeal a (ell + 2 * a) := by
    apply Germ.weightedOrderIdeal_antitone
      a (ell + 2 * a) (3 * a + (ell - a)) ha (by omega)
    exact hsecondTailRaw
  have hsecondPolynomial :
      Germ.partialDerivative (1 : Fin 2) PGerm *
        (Germ.partialDerivative (0 : Fin 2) g -
          Germ.partialDerivative 0 QGerm) ∈
          Germ.weightedOrderIdeal a (ell + 2 * a) := by
    apply Germ.weightedOrderIdeal_antitone
      a (ell + 2 * a) (3 * a - 1 + (ell + 1 - a)) ha (by omega)
    exact hsecondPolynomialRaw
  have hsecond :
      Germ.partialDerivative (1 : Fin 2) f *
            Germ.partialDerivative (0 : Fin 2) g -
          Germ.partialDerivative 1 PGerm *
            Germ.partialDerivative 0 QGerm ∈
        Germ.weightedOrderIdeal a (ell + 2 * a) := by
    have hsum := (Germ.weightedOrderIdeal a (ell + 2 * a)).add_mem
      hsecondTail hsecondPolynomial
    convert hsum using 1
    ring
  have hdifference :=
    (Germ.weightedOrderIdeal a (ell + 2 * a)).sub_mem hfirst hsecond
  rw [← Germ.jacobian_coordinatePolynomialAlgHom]
  simp only [Germ.jacobian_eq]
  convert hdifference using 1
  ring

/-- Strict weighted initial forms and analytic divisibility of the Jacobian
force the Newton differential polynomial to have degree at most one. -/
theorem newtonOmega_natDegree_le_one_of_analytic_jacobian_divisibility
    (a ell m : ℕ) (ha : 0 < a) (hell : 0 < ell) (hm : ell < m)
    (A B : ℂ) (Q : MvPolynomial (Fin 2) ℂ)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] ell)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (ell + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian f g) :
    (newtonOmega ell a A B (weightedDehomogenize Q)).natDegree ≤ 1 := by
  let P := weightedCubicPolynomial a A B
  let R := OnLeConjecture.Polynomial.jacobian P Q
  let D := ell + 2 * a - 1
  have hP : P.IsWeightedHomogeneous ![a, 1] (3 * a) := by
    exact weightedCubicPolynomial_isWeightedHomogeneous a A B
  have hR : R.IsWeightedHomogeneous ![a, 1] D := by
    by_cases haell : a ≤ ell
    · have hraw :=
        OnLeConjecture.Polynomial.isWeightedHomogeneous_jacobian
          ![a, 1] P Q (3 * a) ell hP hQ
            (by
              norm_num
              omega)
            (by
              norm_num
              omega)
            (by
              norm_num
              exact haell)
            (by
              norm_num
              omega)
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, D,
        show 3 * a - a + (ell - 1) = ell + 2 * a - 1 by omega] using hraw
    · have hQzero : MvPolynomial.pderiv (0 : Fin 2) Q = 0 :=
        pderiv_zero_eq_zero_of_isWeightedHomogeneous_degree_lt
          a ell Q hQ (Nat.lt_of_not_ge haell)
      dsimp only [R]
      rw [OnLeConjecture.Polynomial.jacobian, hQzero,
        mul_zero, sub_zero]
      have hPzero := hP.pderiv
        (show 2 * a + ![a, 1] (0 : Fin 2) = 3 * a by
          norm_num
          omega)
      have hQone := hQ.pderiv
        (show ell - 1 + ![a, 1] (1 : Fin 2) = ell by
          norm_num
          omega)
      have hproduct := hPzero.mul hQone
      simpa only [D,
        show 2 * a + (ell - 1) = ell + 2 * a - 1 by omega] using hproduct
  have htail :
      Germ.jacobian f g - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1) := by
    have hraw :=
      jacobian_sub_weightedCubicPolynomial_mem_weightedOrderIdeal
        a ell ha hell A B Q hQ f g hf hg
    change Germ.jacobian f g - Germ.coordinatePolynomialAlgHom 2
        (OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B) Q) ∈
      Germ.weightedOrderIdeal a ((ell + 2 * a - 1) + 1)
    convert hraw using 1
    exact congrArg (Germ.weightedOrderIdeal a)
      (Nat.sub_add_cancel (Nat.succ_le_iff.mpr
        (Nat.add_pos_left hell (2 * a))))
  have hchart : (weightedDehomogenize R).natDegree ≤ 1 := by
    rw [weightedDehomogenize_eq_map_finSuccEquiv,
      Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [Polynomial.coeff_map]
    have hkTwo : 2 ≤ k := by omega
    by_cases hak : a * k ≤ D
    · have hexponent : D - a * k < m - 1 := by
        have hTwo : 2 * a ≤ a * k := by
          simpa only [mul_comm] using Nat.mul_le_mul_left a hkTwo
        dsimp only [D] at hak ⊢
        omega
      have hzero :=
        Germ.finSuccEquiv_coeff_eq_zero_of_dvd_weighted_initial_form
          a D (m - 1) (Germ.jacobian f g) R hR htail hdiv
            k hak hexponent
      rw [hzero, map_zero]
    · have hzero :=
        Germ.finSuccEquiv_coeff_eq_zero_of_weight_exceeds_degree
          a D R hR k (Nat.lt_of_not_ge hak)
      rw [hzero, map_zero]
  rw [← weightedDehomogenize_jacobian_weightedCubicPolynomial
    a ell A B Q hQ]
  exact hchart

/-- The analytic Jacobian divisibility supplies the degree hypothesis in the
polynomial Newton theorem. The target power exclusion and the numerical
inequalities remain explicit. -/
theorem analytic_newton_lower_coefficient_and_estimates_force_equalities
    (a ell mu : ℕ) (ha : 0 < a) (hell : 0 < ell) (hellmu : ell < mu)
    (A B : ℂ) (Q : MvPolynomial (Fin 2) ℂ)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] ell)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (ell + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (mu - 1) ∣
      Germ.jacobian f g)
    (A₃ b S m M : ℤ)
    (hUDegree : 3 ≤ (weightedDehomogenize Q).natDegree)
    (hlower : A ≠ 0 ∨ B ≠ 0)
    (hnotPower :
      ∀ (s : ℕ) (c : ℂ), 0 < s → c ≠ 0 →
        weightedDehomogenize Q ≠ C c * cubic A B ^ s)
    (hA₃ : A₃ ≤ (a : ℤ))
    (hdegree :
      (((weightedDehomogenize Q).natDegree : ℤ) - 4 +
          2 * ((newtonOmega ell a A B
            (weightedDehomogenize Q)).natDegree : ℤ)) *
        (a : ℤ) ≤ A₃)
    (hb : 1 ≤ b)
    (hbthree : b ≤ 3)
    (hS :
      S = 3 * (a : ℤ) *
        (((weightedDehomogenize Q).natDegree : ℤ) - 2) - b + 3)
    (hSm : S ≤ m)
    (hm :
      m ≤ (a : ℤ) *
        (((weightedDehomogenize Q).natDegree : ℤ) + 2 -
          ((newtonOmega ell a A B
            (weightedDehomogenize Q)).natDegree : ℤ)))
    (hM : M = 3 * ((weightedDehomogenize Q).natDegree : ℤ) * (a : ℤ)) :
    ell = 4 * a ∧
      newtonOmega ell a A B (weightedDehomogenize Q) ≠ 0 ∧
      (newtonOmega ell a A B
        (weightedDehomogenize Q)).natDegree = 0 ∧
      (weightedDehomogenize Q).natDegree = 4 ∧ b = 3 ∧
      S = 6 * (a : ℤ) ∧ m = 6 * (a : ℤ) ∧ M = 12 * (a : ℤ) := by
  have homegaDegree :=
    newtonOmega_natDegree_le_one_of_analytic_jacobian_divisibility
      a ell mu ha hell hellmu A B Q hQ f g hf hg hdiv
  exact newton_lower_coefficient_and_estimates_force_equalities
    ell a A B (weightedDehomogenize Q) A₃ b S m M ha hUDegree
      homegaDegree hlower hnotPower hA₃ hdegree hb hbthree hS hSm hm hM

end OnLeConjecture.DThree
