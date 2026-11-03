/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

/-!
# Weighted coefficients under monic division

If the coefficient of degree `i` of a monic polynomial of degree `m`
belongs to `I^(r*(m-i))`, monic division preserves the coefficient bounds
`coeff_i ∈ I^(L-r*i)`. The proof follows the degree-decreasing polynomial
division algorithm.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

variable {A : Type*} [CommRing A]

/-- Polynomials with weighted coefficient order at least `L`. -/
@[expose] def weightedCoefficientSubmodule (I : Ideal A) (r L : ℕ) :
    Submodule A A[X] where
  carrier := {F | ∀ i, F.coeff i ∈ I ^ (L - r * i)}
  zero_mem' := by intro i; simp
  add_mem' hF hG := by
    intro i
    rw [coeff_add]
    exact (I ^ (L - r * i)).add_mem (hF i) (hG i)
  smul_mem' c F hF := by
    intro i
    rw [coeff_smul]
    exact (I ^ (L - r * i)).smul_mem c (hF i)

@[simp] theorem mem_weightedCoefficientSubmodule
    (I : Ideal A) (r L : ℕ) (F : A[X]) :
    F ∈ weightedCoefficientSubmodule I r L ↔ ∀ i, F.coeff i ∈ I ^ (L - r * i) :=
  Iff.rfl

/-- Raising the weighted threshold decreases the coefficient submodule. -/
theorem weightedCoefficientSubmodule_antitone
    (I : Ideal A) (r D E : ℕ) (hDE : D ≤ E) :
    weightedCoefficientSubmodule I r E ≤ weightedCoefficientSubmodule I r D := by
  intro F hF i
  exact Ideal.pow_le_pow_right (Nat.sub_le_sub_right hDE _) (hF i)

/-- Multiplication by a scalar monomial adds its scalar order and its
weighted polynomial degree to the threshold. -/
theorem mul_C_mul_X_pow_mem_weightedCoefficientSubmodule
    (I : Ideal A) (r D s k : ℕ) (F : A[X]) (c : A)
    (hF : F ∈ weightedCoefficientSubmodule I r D) (hc : c ∈ I ^ s) :
    F * (C c * X ^ k) ∈ weightedCoefficientSubmodule I r (D + r * k + s) := by
  intro j
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with hkj
  · rw [coeff_mul_C]
    have hprod : F.coeff (j - k) * c ∈ I ^ ((D - r * (j - k)) + s) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hF (j - k)) hc
    have hrj : r * j = r * (j - k) + r * k := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hkj]
    exact Ideal.pow_le_pow_right (by omega) hprod
  · exact (I ^ (D + r * k + s - r * j)).zero_mem

/-- Coefficient bounds below the index `m` give the full weighted bound
with threshold `r*m`. The bounds at higher indices are automatic. -/
theorem mem_weightedCoefficientSubmodule_of_lower_coefficients
    (I : Ideal A) (r m : ℕ) (P : A[X])
    (hcoeff : ∀ i, i < m → P.coeff i ∈ I ^ (r * (m - i))) :
    P ∈ weightedCoefficientSubmodule I r (r * m) := by
  intro i
  by_cases hi : i < m
  · simpa only [Nat.mul_sub] using hcoeff i hi
  · have hle : r * m ≤ r * i := Nat.mul_le_mul_left r (by omega)
    simp only [Nat.sub_eq_zero_of_le hle, pow_zero, Ideal.one_eq_top, Submodule.mem_top]

/-- Monic division preserves weighted coefficient bounds. -/
theorem modByMonic_mem_weightedCoefficientSubmodule [Nontrivial A]
    (I : Ideal A) (r L : ℕ) (P : A[X]) (hP : P.Monic)
    (hcoeff : ∀ i, i < P.natDegree →
      P.coeff i ∈ I ^ (r * (P.natDegree - i)))
    (F : A[X]) (hF : F ∈ weightedCoefficientSubmodule I r L) :
    F %ₘ P ∈ weightedCoefficientSubmodule I r L := by
  classical
  by_cases h : P.degree ≤ F.degree ∧ F ≠ 0
  · have _wf := div_wf_lemma h hP
    have hPm : P.natDegree ≤ F.natDegree := natDegree_le_natDegree h.1
    have hPweight := mem_weightedCoefficientSubmodule_of_lower_coefficients
      I r P.natDegree P hcoeff
    have hlc : F.leadingCoeff ∈ I ^ (L - r * F.natDegree) := by
      simpa only [coeff_natDegree] using hF F.natDegree
    have hcorrection := mul_C_mul_X_pow_mem_weightedCoefficientSubmodule
      I r (r * P.natDegree) (L - r * F.natDegree)
      (F.natDegree - P.natDegree) P F.leadingCoeff hPweight hlc
    have hweight : L ≤ r * P.natDegree + r * (F.natDegree - P.natDegree) +
        (L - r * F.natDegree) := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hPm]
      omega
    have hnext : F - P * (C F.leadingCoeff * X ^ (F.natDegree - P.natDegree)) ∈
        weightedCoefficientSubmodule I r L :=
      (weightedCoefficientSubmodule I r L).sub_mem hF
        (weightedCoefficientSubmodule_antitone I r _ _ hweight hcorrection)
    have hmod : F %ₘ P =
        (F - P * (C F.leadingCoeff * X ^ (F.natDegree - P.natDegree))) %ₘ P := by
      apply modByMonic_eq_of_dvd_sub hP
      refine ⟨C F.leadingCoeff * X ^ (F.natDegree - P.natDegree), ?_⟩
      ring
    rw [hmod]
    exact modByMonic_mem_weightedCoefficientSubmodule I r L P hP hcoeff _ hnext
  · by_cases hFzero : F = 0
    · simp [hFzero]
    · have hdegree : F.degree < P.degree := lt_of_not_ge fun hle ↦ h ⟨hle, hFzero⟩
      rw [(modByMonic_eq_self_iff hP).mpr hdegree]
      exact hF
termination_by F

end OnLeConjecture.Polynomial
