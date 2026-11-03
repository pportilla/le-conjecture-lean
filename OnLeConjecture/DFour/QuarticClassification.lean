/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Ring

/-!
# The polynomial classification in the case `d = 4`

This file proves the factorization of the initial polynomials used in the
case `d = 4` of the article *On Lê's conjecture*.  The proof takes place in
`Complex[X]` and records the scalar factors explicitly.
-/

public section

namespace OnLeConjecture.DFour

open Polynomial

private lemma associates_out_pow {a : Associates ℂ[X]} (n : ℕ) :
    (a ^ n).out = a.out ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Associates.out_mul, ih, pow_succ]

private lemma monic_eq_pow_of_associates_eq_pow
    {P : ℂ[X]} (hPmonic : P.Monic) {a : Associates ℂ[X]} {n : ℕ}
    (h : Associates.mk P = a ^ n) :
    P = a.out ^ n := by
  have hout := congrArg Associates.out h
  rw [Associates.out_mk, hPmonic.normalize_eq_self, associates_out_pow] at hout
  exact hout

private lemma associates_power_identity
    {P R : ℂ[X]} {k : ℕ} {κ : ℂ} (hκ : κ ≠ 0)
    (hpower : R ^ 4 = C κ * P ^ k) :
    Associates.mk R ^ 4 = Associates.mk P ^ k := by
  have hCunit : IsUnit (C κ : ℂ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hκ)
  calc
    Associates.mk R ^ 4 = Associates.mk (R ^ 4) := (Associates.mk_pow R 4).symm
    _ = Associates.mk (C κ * P ^ k) := congrArg Associates.mk hpower
    _ = Associates.mk (C κ) * Associates.mk (P ^ k) := Associates.mk_mul_mk.symm
    _ = 1 * Associates.mk (P ^ k) := by rw [Associates.mk_eq_one.mpr hCunit]
    _ = Associates.mk P ^ k := by rw [one_mul, Associates.mk_pow]

private lemma nonzero_of_power_identity
    {P R : ℂ[X]} {k : ℕ} {κ : ℂ} (hP0 : P ≠ 0) (hκ : κ ≠ 0)
    (hpower : R ^ 4 = C κ * P ^ k) :
    R ≠ 0 := by
  intro hR
  subst R
  have hrhs : C κ * P ^ k ≠ (0 : ℂ[X]) :=
    mul_ne_zero (C_ne_zero.mpr hκ) (pow_ne_zero k hP0)
  exact hrhs (by simpa using hpower.symm)

private lemma monic_is_fourth_power_of_associates_identity_of_odd
    {P R : ℂ[X]} {k : ℕ}
    (hPmonic : P.Monic) (hR0 : R ≠ 0)
    (hidentity : Associates.mk R ^ 4 = Associates.mk P ^ k)
    (hkodd : Odd k) :
    ∃ Q : ℂ[X], P = Q ^ 4 := by
  classical
  have hPmk0 : Associates.mk P ≠ 0 := Associates.mk_ne_zero.mpr hPmonic.ne_zero
  have hRmk0 : Associates.mk R ≠ 0 := Associates.mk_ne_zero.mpr hR0
  have hcoprime : Nat.Coprime 4 k := by
    simpa using hkodd.coprime_two_left.pow_left 2
  obtain ⟨a, ha⟩ := Associates.is_pow_of_dvd_count hPmk0 (k := 4) (fun p hp => by
    have hcount := congrArg (fun b : Associates ℂ[X] => p.count b.factors) hidentity
    rw [Associates.count_pow hRmk0 hp, Associates.count_pow hPmk0 hp] at hcount
    apply hcoprime.dvd_of_dvd_mul_left
    exact ⟨p.count (Associates.mk R).factors, hcount.symm⟩)
  exact ⟨a.out, monic_eq_pow_of_associates_eq_pow hPmonic ha⟩

private lemma monic_is_square_of_associates_identity
    {P R : ℂ[X]} {e : ℕ}
    (hPmonic : P.Monic) (hR0 : R ≠ 0)
    (hidentity : Associates.mk R ^ 4 = Associates.mk P ^ (2 * e))
    (heodd : Odd e) :
    ∃ Q : ℂ[X], Q.Monic ∧ P = Q ^ 2 := by
  classical
  have hPmk0 : Associates.mk P ≠ 0 := Associates.mk_ne_zero.mpr hPmonic.ne_zero
  have hRmk0 : Associates.mk R ≠ 0 := Associates.mk_ne_zero.mpr hR0
  obtain ⟨a, ha⟩ := Associates.is_pow_of_dvd_count hPmk0 (k := 2) (fun p hp => by
    have hcount := congrArg (fun b : Associates ℂ[X] => p.count b.factors) hidentity
    rw [Associates.count_pow hRmk0 hp, Associates.count_pow hPmk0 hp] at hcount
    have hcancel :
        2 * p.count (Associates.mk R).factors =
          e * p.count (Associates.mk P).factors := by
      apply Nat.mul_left_cancel (by norm_num : 0 < 2)
      calc
        2 * (2 * p.count (Associates.mk R).factors) =
            4 * p.count (Associates.mk R).factors := by ring
        _ = (2 * e) * p.count (Associates.mk P).factors := hcount
        _ = 2 * (e * p.count (Associates.mk P).factors) := by ring
    apply heodd.coprime_two_left.dvd_of_dvd_mul_left
    exact ⟨p.count (Associates.mk R).factors, hcancel.symm⟩)
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hPmk0
    rw [ha, ha0, zero_pow (by norm_num : 2 ≠ 0)]
  have haout0 : a.out ≠ (0 : ℂ[X]) := Associates.out_eq_zero_iff.not.mpr ha0
  have haoutMonic := Polynomial.monic_normalize haout0
  rw [Associates.normalize_out] at haoutMonic
  exact ⟨a.out, haoutMonic, monic_eq_pow_of_associates_eq_pow hPmonic ha⟩

/-- A monic depressed quartic satisfying the fourth power identity and the
normalization condition on `R` has the square factorization used in the
case `d = 4`. -/
theorem quartic_power_identity_classification
    {P R : ℂ[X]} {k : ℕ} {κ : ℂ}
    (hPmonic : P.Monic)
    (hPdegree : P.natDegree = 4)
    (hPdepressed : P.coeff 3 = 0)
    (hPnotFourth : ∀ Q : ℂ[X], P ≠ Q ^ 4)
    (hkpos : 0 < k)
    (hκ : κ ≠ 0)
    (hpower : R ^ 4 = C κ * P ^ k)
    (hRnormalized : ∀ (s : ℕ) (γ : ℂ),
      0 < s → γ ≠ 0 → R ≠ C γ * P ^ s) :
    ∃ (e : ℕ) (η μ : ℂ),
      k % 4 = 2 ∧ k = 2 * e ∧ Odd e ∧ η * μ ≠ 0 ∧
        P = (X ^ 2 + C η) ^ 2 ∧
        R = C μ * (X ^ 2 + C η) ^ e := by
  classical
  have hP0 : P ≠ 0 := hPmonic.ne_zero
  have hR0 : R ≠ 0 := nonzero_of_power_identity hP0 hκ hpower
  have hidentity := associates_power_identity hκ hpower
  have hRdegree : R.natDegree = k := by
    have hdegree := congrArg Polynomial.natDegree hpower
    rw [Polynomial.natDegree_pow R 4,
      Polynomial.natDegree_mul (C_ne_zero.mpr hκ) (pow_ne_zero k hP0),
      natDegree_C, hPmonic.natDegree_pow, hPdegree] at hdegree
    omega
  have hfourNotDvd : ¬ 4 ∣ k := by
    intro hfour
    obtain ⟨s, hs⟩ := hfour
    have hpowers : Associates.mk R ^ 4 = (Associates.mk P ^ s) ^ 4 := by
      calc
        Associates.mk R ^ 4 = Associates.mk P ^ k := hidentity
        _ = Associates.mk P ^ (4 * s) := by rw [hs]
        _ = Associates.mk P ^ (s * 4) := by rw [Nat.mul_comm]
        _ = (Associates.mk P ^ s) ^ 4 := pow_mul _ _ _
    have hassociatedPowers : Associated (R ^ 4) ((P ^ s) ^ 4) := by
      apply Associates.mk_eq_mk_iff_associated.mp
      simpa only [Associates.mk_pow] using hpowers
    have hassociated : Associated R (P ^ s) :=
      (Associated.pow_iff (by norm_num : 4 ≠ 0)).mp hassociatedPowers
    have hdegree : R.natDegree ≤ (P ^ s).natDegree := by
      rw [hRdegree, hPmonic.natDegree_pow, hPdegree, hs]
      omega
    have hscalar := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
      (hPmonic.pow s) hassociated.dvd' hdegree
    have hlead : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR0
    have hspos : 0 < s := by omega
    exact hRnormalized s R.leadingCoeff hspos hlead hscalar
  have hkNotOdd : ¬ Odd k := by
    intro hkodd
    obtain ⟨Q, hQ⟩ :=
      monic_is_fourth_power_of_associates_identity_of_odd hPmonic hR0 hidentity hkodd
    exact hPnotFourth Q hQ
  have hkmod : k % 4 = 2 := by
    have hlt := Nat.mod_lt k (by omega : 0 < 4)
    have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
      omega
    rcases hcases with h | h | h | h
    · exact False.elim (hfourNotDvd (Nat.dvd_of_mod_eq_zero h))
    · exact False.elim
        (hkNotOdd (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one h)))
    · exact h
    · exact False.elim
        (hkNotOdd (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three h)))
  let e := k / 2
  have hkEven : k = 2 * e := by
    have hk2 := Nat.mod_add_div k 2
    have hkmod2 : k % 2 = 0 := by
      rw [show k % 2 = k % 4 % 2 from
        (Nat.mod_mod_of_dvd k (by decide : 2 ∣ 4)).symm, hkmod]
    omega
  have heOdd : Odd e := by
    rw [Nat.odd_iff]
    have hk4 := Nat.mod_add_div k 4
    have heFormula : e = 1 + 2 * (k / 4) := by
      dsimp [e]
      omega
    rw [heFormula]
    omega
  have hidentityE : Associates.mk R ^ 4 = Associates.mk P ^ (2 * e) := by
    rw [← hkEven]
    exact hidentity
  obtain ⟨Q, hQmonic, hPsquare⟩ :=
    monic_is_square_of_associates_identity hPmonic hR0 hidentityE heOdd
  have hQdegree : Q.natDegree = 2 := by
    have hdegree := congrArg Polynomial.natDegree hPsquare
    rw [hPdegree, hQmonic.natDegree_pow] at hdegree
    omega
  have hPnext : P.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (hPdegree ▸ by norm_num), hPdegree]
    exact hPdepressed
  have hQnext : Q.nextCoeff = 0 := by
    have hnext := hQmonic.nextCoeff_pow 2
    rw [← hPsquare, hPnext] at hnext
    apply add_self_eq_zero.mp
    simpa only [two_nsmul] using hnext.symm
  let η := Q.coeff 0
  have hQform : Q = X ^ 2 + C η := by
    apply Polynomial.ext
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [η]
    by_cases hn1 : n = 1
    · subst n
      have hcoeff : Q.coeff 1 = 0 := by
        rw [← hQnext, nextCoeff_of_natDegree_pos (hQdegree ▸ by norm_num), hQdegree]
      simp [hcoeff]
    by_cases hn2 : n = 2
    · subst n
      have hcoeff : Q.coeff 2 = 1 := by
        rw [← hQdegree, coeff_natDegree, hQmonic.leadingCoeff]
      simp [hcoeff]
    · have hn : Q.natDegree < n := by omega
      rw [coeff_eq_zero_of_natDegree_lt hn]
      simp [coeff_add, coeff_X_pow, coeff_C, hn0, hn2]
  have hη0 : η ≠ 0 := by
    intro hη
    apply hPnotFourth X
    rw [hPsquare, hQform, hη]
    simp only [C_0, add_zero, ← pow_mul]
  have hassociatedPowers : Associated (R ^ 4) ((Q ^ e) ^ 4) := by
    apply Associates.mk_eq_mk_iff_associated.mp
    calc
      Associates.mk (R ^ 4) = Associates.mk R ^ 4 := Associates.mk_pow R 4
      _ = Associates.mk P ^ k := hidentity
      _ = Associates.mk (Q ^ 2) ^ (2 * e) := by rw [hkEven, hPsquare]
      _ = Associates.mk Q ^ (4 * e) := by
        rw [Associates.mk_pow, ← pow_mul]
        congr 1
        ring
      _ = Associates.mk Q ^ (e * 4) := by rw [Nat.mul_comm]
      _ = (Associates.mk Q ^ e) ^ 4 := pow_mul _ _ _
      _ = Associates.mk ((Q ^ e) ^ 4) := by
        rw [Associates.mk_pow, Associates.mk_pow]
  have hassociated : Associated R (Q ^ e) :=
    (Associated.pow_iff (by norm_num : 4 ≠ 0)).mp hassociatedPowers
  have hdegree : R.natDegree ≤ (Q ^ e).natDegree := by
    rw [hRdegree, hQmonic.natDegree_pow, hQdegree, hkEven]
    omega
  have hRform := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (hQmonic.pow e) hassociated.dvd' hdegree
  let μ := R.leadingCoeff
  have hμ0 : μ ≠ 0 := leadingCoeff_ne_zero.mpr hR0
  refine ⟨e, η, μ, hkmod, hkEven, heOdd, mul_ne_zero hη0 hμ0, ?_, ?_⟩
  · rw [hPsquare, hQform]
  · simpa [μ, hQform] using hRform

end OnLeConjecture.DFour
