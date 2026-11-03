/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedInitialFormDivisibility

/-!
# Factors of weighted polynomial initial forms

Divisibility of an analytic germ by a power of the second coordinate passes
to every weighted homogeneous polynomial initial form with a strict weighted
tail.
-/

public section

namespace OnLeConjecture.Analytic

open scoped BigOperators

namespace Germ

/-- Each coefficient in the first coordinate of a weighted homogeneous
binary polynomial is the monomial forced by its weighted degree. -/
theorem finSuccEquiv_coeff_eq_forced_monomial
    (a D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) (k : ℕ) :
    (MvPolynomial.finSuccEquiv ℂ 1 P).coeff k =
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 1) (D - a * k))
        ((MvPolynomial.finSuccEquiv ℂ 1 P).coeff k |>.coeff
          (Finsupp.single (0 : Fin 1) (D - a * k))) := by
  apply MvPolynomial.eq_monomial_of_support_subset_singleton
  intro d hd
  have hdne :
      MvPolynomial.coeff d
          ((MvPolynomial.finSuccEquiv ℂ 1 P).coeff k) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hfullne : MvPolynomial.coeff (Finsupp.cons k d) P ≠ 0 := by
    rwa [← MvPolynomial.finSuccEquiv_coeff_coeff]
  have hweight := hP hfullne
  apply Finsupp.ext
  intro i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rw [Finsupp.single_eq_same]
  have hweight' :
      k * a + (Finsupp.cons k d) (1 : Fin 2) = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_two] using hweight
  have hcons : (Finsupp.cons k d) (1 : Fin 2) = d (0 : Fin 1) := by
    rfl
  rw [hcons] at hweight'
  apply Nat.eq_sub_of_add_eq
  calc
    d 0 + a * k = k * a + d 0 := by ac_rfl
    _ = D := hweight'

/-- Divisibility of a germ by a power of the second coordinate passes to a
weighted homogeneous polynomial initial form with a strict weighted tail. -/
theorem secondVariable_pow_dvd_of_dvd_weighted_initial_form
    (a D N : ℕ) (h : Germ 2) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (htail : h - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (D + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ N ∣ h) :
    MvPolynomial.X (1 : Fin 2) ^ N ∣ P := by
  rw [← map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 1)]
  rw [map_pow, show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl,
    MvPolynomial.finSuccEquiv_X_succ,
    ← map_pow, Polynomial.C_dvd_iff_dvd_coeff]
  intro k
  by_cases hak : a * k ≤ D
  · by_cases hNe : N ≤ D - a * k
    · rw [finSuccEquiv_coeff_eq_forced_monomial a D P hP k]
      rw [← MvPolynomial.C_mul_X_pow_eq_monomial]
      exact dvd_mul_of_dvd_right (pow_dvd_pow _ hNe) _
    · have hzero := finSuccEquiv_coeff_eq_zero_of_dvd_weighted_initial_form
          a D N h P hP htail hdiv k hak (Nat.lt_of_not_ge hNe)
      rw [hzero]
      exact dvd_zero _
  · have hzero := finSuccEquiv_coeff_eq_zero_of_weight_exceeds_degree
        a D P hP k (Nat.lt_of_not_ge hak)
    rw [hzero]
    exact dvd_zero _

end Germ

end OnLeConjecture.Analytic
