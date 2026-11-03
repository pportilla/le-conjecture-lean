/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableLeadingTerm
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Coefficientwise construction of weighted polynomial scaling

The prescribed one-variable orders divide each polynomial coefficient by
the corresponding coordinate power. The resulting polynomial has the same
degree and satisfies the exact weighted scaling identity. In the monic
case the common scalar factor disappears and the scaled polynomial remains
monic. Its coefficients at the origin are determined by the initial
coefficient congruences.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Coefficientwise weighted divisibility constructs a polynomial of the
same degree with the exact weighted scaling identity. -/
theorem exists_weighted_polynomial_scaling
    (P : Polynomial (Germ 1)) (r L : ℕ) (hL : r * P.natDegree ≤ L)
    (hcoeff : ∀ i, P.coeff i ∈ maximalIdeal 1 ^ (L - r * i)) :
    ∃ Q : Polynomial (Germ 1), Q.natDegree = P.natDegree ∧
      P = C (coordinate (0 : Fin 1) ^ (L - r * Q.natDegree)) *
        Q.scaleRoots (coordinate (0 : Fin 1) ^ r) ∧
      ∀ i, P.coeff i = coordinate (0 : Fin 1) ^ (L - r * i) * Q.coeff i := by
  classical
  by_cases hP : P = 0
  · subst P
    exact ⟨0, by simp, by simp, by intro i; simp⟩
  have hdiv (i : ℕ) : coordinate (0 : Fin 1) ^ (L - r * i) ∣ P.coeff i := by
    rw [← Ideal.mem_span_singleton, ← maximalIdeal_one_pow_eq_span_coordinate_pow]
    exact hcoeff i
  choose c hc using hdiv
  let Q : Polynomial (Germ 1) :=
    ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (c i)
  have hQcoeff (i : ℕ) : Q.coeff i = if i ≤ P.natDegree then c i else 0 := by
    simp [Q, finsetSum_coeff, coeff_monomial]
  have hfactor (i : ℕ) :
      P.coeff i = coordinate (0 : Fin 1) ^ (L - r * i) * Q.coeff i := by
    by_cases hi : i ≤ P.natDegree
    · simpa [hQcoeff, hi] using hc i
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), hQcoeff, if_neg hi, mul_zero]
  have hQbound : Q.natDegree ≤ P.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    simp [hQcoeff, show ¬ i ≤ P.natDegree by omega]
  have hQdegree : Q.natDegree = P.natDegree := by
    apply le_antisymm hQbound
    apply le_natDegree_of_ne_zero
    intro hzero
    have htop := hfactor P.natDegree
    rw [hzero, mul_zero, coeff_natDegree] at htop
    exact (leadingCoeff_ne_zero.mpr hP) htop
  refine ⟨Q, hQdegree, ?_, hfactor⟩
  apply Polynomial.ext
  intro i
  rw [coeff_C_mul, coeff_scaleRoots, hQdegree]
  by_cases hi : i ≤ P.natDegree
  · have hexponent : L - r * P.natDegree + r * (P.natDegree - i) = L - r * i := by
      rw [Nat.mul_sub_left_distrib]
      have hri : r * i ≤ r * P.natDegree := Nat.mul_le_mul_left r hi
      omega
    rw [hfactor i, ← pow_mul]
    calc
      coordinate (0 : Fin 1) ^ (L - r * i) * Q.coeff i =
          coordinate (0 : Fin 1) ^ (L - r * P.natDegree + r * (P.natDegree - i)) *
            Q.coeff i := by rw [hexponent]
      _ = _ := by rw [pow_add]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), hQcoeff, if_neg hi,
      zero_mul, mul_zero]

/-- A monic polynomial with the weighted coefficient orders is obtained
by root scaling from a monic polynomial of the same degree. -/
theorem exists_monic_weighted_polynomial_scaling
    (P : Polynomial (Germ 1)) (m r : ℕ) (hmonic : P.Monic) (hdegree : P.natDegree = m)
    (hcoeff : ∀ i, P.coeff i ∈ maximalIdeal 1 ^ (r * (m - i))) :
    ∃ Q : Polynomial (Germ 1), Q.Monic ∧ Q.natDegree = m ∧
      P = Q.scaleRoots (coordinate (0 : Fin 1) ^ r) ∧
      ∀ i, P.coeff i = coordinate (0 : Fin 1) ^ (r * (m - i)) * Q.coeff i := by
  obtain ⟨Q, hQdegree, hscaling, hfactor⟩ :=
    exists_weighted_polynomial_scaling P r (r * m) (by rw [hdegree])
      (by intro i; simpa [Nat.mul_sub_left_distrib] using hcoeff i)
  have hQm : Q.natDegree = m := hQdegree.trans hdegree
  have hscaling' : P = Q.scaleRoots (coordinate (0 : Fin 1) ^ r) := by
    simpa [hQm] using hscaling
  refine ⟨Q, ?_, hQm, hscaling', ?_⟩
  · apply (monic_scaleRoots_iff _).mp
    rwa [← hscaling']
  · intro i
    simpa [Nat.mul_sub_left_distrib] using hfactor i

/-- The quotient by a coordinate power has the scalar specified by the
initial coefficient congruence as its value at the origin. -/
theorem value_divided_coefficient_eq_of_initial_congruence
    (f q : Germ 1) (d : ℕ) (c : ℂ)
    (hfactor : f = coordinate (0 : Fin 1) ^ d * q)
    (hinitial : f - constRingHom 1 c * coordinate (0 : Fin 1) ^ d ∈
      maximalIdeal 1 ^ (d + 1)) :
    valueRingHom 1 q = c := by
  have hdiv : coordinate (0 : Fin 1) ^ (d + 1) ∣
      coordinate (0 : Fin 1) ^ d * (q - constRingHom 1 c) := by
    rw [← Ideal.mem_span_singleton, ← maximalIdeal_one_pow_eq_span_coordinate_pow]
    convert hinitial using 1
    rw [hfactor]
    ring
  rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero d coordinate_zero_ne_zero)] at hdiv
  have hmax : q - constRingHom 1 c ∈ maximalIdeal 1 := by
    rwa [maximalIdeal_one_eq_span_coordinate, Ideal.mem_span_singleton]
  rw [mem_maximalIdeal_iff, map_sub, valueRingHom_const] at hmax
  exact sub_eq_zero.mp hmax

/-- The residue polynomial of a coefficientwise scaled polynomial is the
polynomial specified by the weighted initial coefficient congruences. -/
theorem map_weighted_scaled_polynomial_eq_of_initial_coefficients
    (P Q : Polynomial (Germ 1)) (r L : ℕ) (B : ℂ[X])
    (hfactor : ∀ i,
      P.coeff i = coordinate (0 : Fin 1) ^ (L - r * i) * Q.coeff i)
    (hinitial : ∀ i,
      P.coeff i - constRingHom 1 (B.coeff i) * coordinate (0 : Fin 1) ^ (L - r * i) ∈
        maximalIdeal 1 ^ (L - r * i + 1)) :
    Q.map (valueRingHom 1) = B := by
  ext i
  rw [coeff_map]
  exact value_divided_coefficient_eq_of_initial_congruence
    (P.coeff i) (Q.coeff i) (L - r * i) (B.coeff i) (hfactor i) (hinitial i)

end OnLeConjecture.Analytic.Germ
