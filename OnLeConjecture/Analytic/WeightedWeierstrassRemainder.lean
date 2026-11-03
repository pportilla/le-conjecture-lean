/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.WeightedMonicRemainder
public import OnLeConjecture.Analytic.WeierstrassPairQuotient
public import OnLeConjecture.Analytic.WeightedOrderIdealAlgebra
public import OnLeConjecture.Analytic.PlaneElimination

/-!
# Weighted bounds for analytic Weierstrass remainders

The coefficient-order assumptions on a monic Weierstrass polynomial imply
that analytic division preserves weighted order in its polynomial remainder.
The proof replaces the analytic multipliers of the finitely many weighted
ideal generators by polynomial classes, then applies the proved weighted
monic division theorem. No bound on an analytic remainder is assumed.
-/

public section

namespace OnLeConjecture.Analytic

open _root_.Polynomial
open OnLeConjecture.Polynomial

namespace Germ

/-- The polynomial representing one of the finite generators of the plane
weighted order ideal. -/
@[expose] noncomputable def weightedOrderGeneratorPolynomial
    (r L : ℕ) (k : Fin (L + 1)) : Polynomial (Germ 1) :=
  C (Germ.coordinate (0 : Fin 1) ^ (L - r * k.1)) * X ^ k.1

/-- Evaluation of the generator polynomial is the analytic weighted
monomial generator. -/
@[simp] theorem eval_weightedOrderGeneratorPolynomial
    (r L : ℕ) (k : Fin (L + 1)) :
    firstCoordinatePolynomialEvaluation (weightedOrderGeneratorPolynomial r L k) =
      weightedOrderGenerator r L k := by
  simp only [weightedOrderGeneratorPolynomial, firstCoordinatePolynomialEvaluation,
    eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_pow,
    hyperplaneExtension_coordinate_plane, weightedOrderGenerator]
  exact mul_comm _ _

/-- An arbitrary polynomial multiple of a weighted ideal generator obeys
the same weighted coefficient bounds. -/
theorem mul_weightedOrderGeneratorPolynomial_mem
    (r L : ℕ) (k : Fin (L + 1)) (S : Polynomial (Germ 1)) :
    S * weightedOrderGeneratorPolynomial r L k ∈
      weightedCoefficientSubmodule (maximalIdeal 1) r L := by
  have hS : S ∈ weightedCoefficientSubmodule (maximalIdeal 1) r 0 := by
    intro i
    simp
  have hc : Germ.coordinate (0 : Fin 1) ^ (L - r * k.1) ∈
      maximalIdeal 1 ^ (L - r * k.1) :=
    Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (0 : Fin 1)) _
  have h := mul_C_mul_X_pow_mem_weightedCoefficientSubmodule
    (maximalIdeal 1) r 0 (L - r * k.1) k.1 S
    (Germ.coordinate (0 : Fin 1) ^ (L - r * k.1)) hS hc
  exact weightedCoefficientSubmodule_antitone (maximalIdeal 1) r L _ (by omega) h

/-- Positive weighted coefficient orders below the monic degree imply
the distinguished coefficient condition required for analytic division. -/
theorem coeff_mem_maximalIdeal_of_weighted_bounds
    (r m : ℕ) (hr : 0 < r) (P : Polynomial (Germ 1))
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i))) :
    ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 := by
  intro i hi
  have hpower : 1 ≤ r * (m - i) := Nat.mul_pos hr (Nat.sub_pos_of_lt hi)
  have h := Ideal.pow_le_pow_right hpower (hcoeff i hi)
  simpa only [pow_one] using h

/-- An analytic germ in the weighted order ideal has an analytic
Weierstrass division whose remainder satisfies the weighted coefficient
bounds. -/
theorem exists_weightedWeierstrassRemainder
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (H : Germ 2) (hH : H ∈ weightedOrderIdeal r L) :
    ∃ q : Germ 2, ∃ R : Polynomial (Germ 1),
      H = firstCoordinatePolynomialEvaluation P * q + firstCoordinatePolynomialEvaluation R ∧
      R.degree < (m : ℕ) ∧
      ∀ i, R.coeff i ∈ maximalIdeal 1 ^ (L - r * i) := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hdist := coeff_mem_maximalIdeal_of_weighted_bounds r (d + 1) hr P hcoeff
  obtain ⟨c, hc⟩ := (mem_weightedOrderIdeal_iff r L H).mp hH
  choose S hS using fun k : Fin (L + 1) ↦
    exists_polynomial_mod_distinguished d P hP hPm hdist (c k)
  let T : Polynomial (Germ 1) :=
    ∑ k : Fin (L + 1), S k * weightedOrderGeneratorPolynomial r L k
  have hT : T ∈ weightedCoefficientSubmodule (maximalIdeal 1) r L := by
    apply (weightedCoefficientSubmodule (maximalIdeal 1) r L).sum_mem
    intro k _
    exact mul_weightedOrderGeneratorPolynomial_mem r L k (S k)
  let J : Ideal (Germ 2) := Ideal.span {firstCoordinatePolynomialEvaluation P}
  have hTeval : firstCoordinatePolynomialEvaluation T =
      ∑ k, firstCoordinatePolynomialEvaluation (S k) * weightedOrderGenerator r L k := by
    change firstCoordinatePolynomialEvaluationRingHom T = _
    simp only [T, map_sum, map_mul, firstCoordinatePolynomialEvaluationRingHom_apply,
      eval_weightedOrderGeneratorPolynomial]
  have hHT : H - firstCoordinatePolynomialEvaluation T ∈ J := by
    have heq : H - firstCoordinatePolynomialEvaluation T =
        ∑ k, (c k - firstCoordinatePolynomialEvaluation (S k)) *
          weightedOrderGenerator r L k := by
      rw [← hc, hTeval, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [heq]
    apply J.sum_mem
    intro k _
    exact Ideal.mul_mem_right _ J (hS k)
  let R := T %ₘ P
  have hRcoeff : R ∈ weightedCoefficientSubmodule (maximalIdeal 1) r L := by
    apply modByMonic_mem_weightedCoefficientSubmodule (maximalIdeal 1) r L P hP
      (by simpa only [hPm] using hcoeff) T hT
  have hRdegree : R.degree < (d + 1 : ℕ) := by
    simpa only [degree_eq_natDegree hP.ne_zero, hPm] using degree_modByMonic_lt T hP
  have hTR : firstCoordinatePolynomialEvaluation T -
      firstCoordinatePolynomialEvaluation R ∈ J := by
    rw [Ideal.mem_span_singleton]
    refine ⟨firstCoordinatePolynomialEvaluation (T /ₘ P), ?_⟩
    have h := congrArg firstCoordinatePolynomialEvaluationRingHom
      (modByMonic_add_div T P)
    simp only [map_add, map_mul, firstCoordinatePolynomialEvaluationRingHom_apply] at h
    change firstCoordinatePolynomialEvaluation T -
      firstCoordinatePolynomialEvaluation (T %ₘ P) = _
    rw [← h]
    ring
  have hHR : H - firstCoordinatePolynomialEvaluation R ∈ J := by
    simpa only [sub_add_sub_cancel] using J.add_mem hHT hTR
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hHR
  exact ⟨q, R, sub_eq_iff_eq_add.mp hq, hRdegree, hRcoeff⟩

/-- Every analytic Weierstrass remainder, not just the one constructed
above, satisfies the weighted coefficient bounds. -/
theorem weightedWeierstrassRemainder_coeff_mem
    (r L m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hcoeff : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)))
    (H : Germ 2) (hH : H ∈ weightedOrderIdeal r L)
    (q : Germ 2) (R : Polynomial (Germ 1)) (hRdegree : R.degree < (m : ℕ))
    (hdivision : H = firstCoordinatePolynomialEvaluation P * q +
      firstCoordinatePolynomialEvaluation R) :
    ∀ i, R.coeff i ∈ maximalIdeal 1 ^ (L - r * i) := by
  obtain ⟨q', R', hdivision', hR'degree, hR'coeff⟩ :=
    exists_weightedWeierstrassRemainder r L m hr hm P hP hPm hcoeff H hH
  have heq := (distinguishedWeierstrass_division_unique hP hPm
    (coeff_mem_maximalIdeal_of_weighted_bounds r m hr P hcoeff)
    hRdegree hR'degree (hdivision.symm.trans hdivision')).2
  rw [heq]
  exact hR'coeff

end Germ

end OnLeConjecture.Analytic
