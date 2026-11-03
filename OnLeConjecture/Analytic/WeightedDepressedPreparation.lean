/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParameterTranslationFreeChain
public import OnLeConjecture.Analytic.WeightedIntersectionStrict

/-!
# Convergent depressed preparation preserving a free-chain weight

The ordinary Weierstrass polynomial is constructed from regularity.
Its weighted coefficient orders determine a Tschirnhausen translation
of order at least the first weight. The translation is lifted through
the free chain by the preceding analytic construction. The depressed
polynomial retains every weighted coefficient bound.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

private theorem coeff_next_after_translation
    {R : Type*} [CommRing R] (P : R[X]) (n : ℕ) (hP : P.Monic)
    (hdegree : P.natDegree = n + 1) (a : R) :
    (P.comp (X + C a)).coeff n = P.coeff n + a * (n + 1 : ℕ) := by
  have htop : P.coeff (n + 1) = 1 := by rw [← hdegree, coeff_natDegree, hP]
  rw [comp, eval₂_eq_sum_range, hdegree, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_add_C_pow]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum : ∑ j ∈ Finset.range n, P.coeff j * (a ^ (j - n) * (j.choose n : R)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj), Nat.cast_zero, mul_zero, mul_zero]
  rw [hsum, zero_add, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one,
    one_mul, mul_one, htop, one_mul, Nat.add_sub_cancel_left, pow_one,
    Nat.choose_succ_self_right]

/-- Analytic parameter translations act on the polynomial preparation
by the same polynomial substitution in its first indeterminate. -/
theorem parameterTranslation_pullback_polynomialEvaluation
    (a : Germ 1) (e : PointedEquivGerm 2)
    (hex : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate 0 + hyperplaneExtension 1 a)
    (hea : ∀ q : Germ 1, e.forward.pullbackRingHom (hyperplaneExtension 1 q) =
      hyperplaneExtension 1 q) (P : Polynomial (Germ 1)) :
    e.forward.pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation (P.comp (X + C a)) := by
  rw [firstCoordinatePolynomialEvaluation, hom_eval₂]
  have hcomp : e.forward.pullbackRingHom.comp (hyperplaneExtension 1) =
      hyperplaneExtension 1 := by
    apply RingHom.ext
    intro q
    exact hea q
  rw [hcomp, hex, firstCoordinatePolynomialEvaluation, eval₂_comp, eval₂_add, eval₂_X, eval₂_C]

/-- In every positive degree, convergent depressed preparation and
coherent analytic chart lifts are constructed from regularity and the
first member's weighted order. -/
theorem exists_weighted_depressed_preparation_with_chain_lifts
    (A m : ℕ) (hA : 0 < A) (hm : 0 < m) (f : Germ 2)
    (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (hf : f ∈ weightedOrderIdeal A (A * m)) :
    ∃ a : Germ 1, ∃ S : ParameterTranslationChain a A,
      ∃ P : Polynomial (Germ 1), ∃ U : Germ 2,
      a ∈ maximalIdeal 1 ^ A ∧ P.Monic ∧ P.natDegree = m ∧ P.coeff (m - 1) = 0 ∧
      IsUnit U ∧ (S.coordinates 0).forward.pullbackRingHom f =
        firstCoordinatePolynomialEvaluation P * U ∧
      ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)) := by
  obtain ⟨Q, V, hQ, hdegree, hV, hfactor, hcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients A m hm f hregular hf
  let c : ℂ := -(m : ℂ)⁻¹
  let a : Germ 1 := constRingHom 1 c * Q.coeff (m - 1)
  have ha : a ∈ maximalIdeal 1 ^ A := by
    apply (maximalIdeal 1 ^ A).mul_mem_left
    simpa only [show m - (m - 1) = 1 by omega, mul_one] using hcoeff (m - 1)
  obtain ⟨S⟩ := exists_parameterTranslationChain A hA a ha
  let e := S.coordinates 0
  let P := Q.comp (X + C a)
  let U := e.forward.pullbackRingHom V
  have hex : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate 0 + hyperplaneExtension 1 a := by
    simpa only [S.shift_zero] using S.first_coordinate 0
  have hea := S.coefficients 0
  have hP : P.Monic := hQ.comp_X_add_C a
  have hPm : P.natDegree = m := (natDegree_taylor Q a).trans hdegree
  have hc : constRingHom 1 c * (m : Germ 1) = -1 := by
    rw [← map_natCast (constRingHom 1) m, ← map_mul]
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [c, neg_mul, inv_mul_cancel₀ hmC, map_neg, map_one]
  have hdepressed : P.coeff (m - 1) = 0 := by
    have h := coeff_next_after_translation Q (m - 1) hQ (by omega) a
    change P.coeff (m - 1) = _ at h
    rw [show m - 1 + 1 = m by omega] at h
    rw [h]
    dsimp only [a]
    rw [mul_right_comm, hc, neg_one_mul, add_neg_cancel]
  have hU : IsUnit U := hV.map _
  have hprepared : e.forward.pullbackRingHom f = firstCoordinatePolynomialEvaluation P * U := by
    rw [hfactor, map_mul, parameterTranslation_pullback_polynomialEvaluation a e hex hea]
  have hweighted : e.forward.pullbackRingHom f ∈ weightedOrderIdeal A (A * m) :=
    (parameterTranslation_mem_weightedOrderIdeal_iff A (A * m) hA a ha e hex hea f).mpr hf
  exact ⟨a, S, P, U, ha, hP, hPm, hdepressed, hU, hprepared,
    coefficient_mem_pow_of_prepared_weighted_order A m _ U P hU hprepared hweighted⟩

/-- The weighted order needed for depressed preparation follows from
the analytic transform identities along a zero-center free chain.
No polynomial preparation or coefficient bound is an input. -/
theorem exists_depressed_preparation_of_free_chain
    (A m : ℕ) (hA : 0 < A) (hm : 0 < m) (f : ℕ → Germ 2)
    (hregular : IsRegularInFirstCoordinateOfOrder (f 0) m)
    (hsteps : ∀ j, j + 1 < A →
      (pointBlowupChartGerm 0).pullbackRingHom (f j) =
        coordinate (1 : Fin 2) ^ m * f (j + 1))
    (hfinal : f (A - 1) ∈ maximalIdeal 2 ^ m) :
    ∃ a : Germ 1, ∃ S : ParameterTranslationChain a A,
      ∃ P : Polynomial (Germ 1), ∃ U : Germ 2,
      a ∈ maximalIdeal 1 ^ A ∧ P.Monic ∧ P.natDegree = m ∧ P.coeff (m - 1) = 0 ∧
      IsUnit U ∧ (S.coordinates 0).forward.pullbackRingHom (f 0) =
        firstCoordinatePolynomialEvaluation P * U ∧
      ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)) := by
  obtain ⟨Q, V, hQ, hdegree, _, hV, hfactor⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_of_pos hm hregular
  have hcoeff (j : ℕ) : Q.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)) := by
    by_cases hj : j ≤ m
    · have h := coefficient_mem_pow_of_prepared_freeChain (A - 1) m Q f V hV
        hfactor (fun k hk ↦ hsteps k (by omega)) hfinal j hj
      simpa only [Nat.sub_add_cancel hA] using h
    · simp [Nat.sub_eq_zero_of_le (by omega : m ≤ j)]
  have hweighted : firstCoordinatePolynomialEvaluation Q ∈ weightedOrderIdeal A (A * m) := by
    apply firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal A (A * m) hA Q
    intro j
    simpa only [← Nat.mul_sub_left_distrib] using hcoeff j
  apply exists_weighted_depressed_preparation_with_chain_lifts A m hA hm (f 0) hregular
  rw [hfactor]
  exact Ideal.mul_mem_right _ _ hweighted

end OnLeConjecture.Analytic.Germ
