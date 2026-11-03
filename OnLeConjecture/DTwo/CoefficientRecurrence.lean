/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Ring

/-!
# Coefficient recurrences in the case of order two

This file isolates the finite algebraic part of the coefficient argument for
the quadratic normal form `g = x^2 + y^k`.  A coefficient `b j` is represented
by a polynomial in `g`.  The variable `Polynomial.X` therefore represents
`g`.  The recurrence is imposed only through index `m - 1`, exactly as in the
analytic argument.
-/

public section

namespace OnLeConjecture.DTwo

open Polynomial

/-- The finite recurrence over a commutative ring with a distinguished
element `g`. -/
@[expose]
def SatisfiesCoefficientRecurrenceOver
    {R : Type*} [CommRing R] (g : R) (b : ℕ → R) (k m : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j < m →
    ((2 * j : ℕ) : R) * g * b j =
      if k ≤ j then ((2 * j - k : ℕ) : R) * b (j - k) else 0

/-- The polynomial expression

`2 (g-y^k) B_y - k y^(k-1) B`.

The polynomial variable represents `y`. -/
@[expose]
noncomputable def quadraticCoefficientDifferential
    {R : Type*} [CommRing R] (g : R) (k : ℕ) (B : R[X]) : R[X] :=
  C (2 * g) * B.derivative -
    (X ^ k * B.derivative) * C 2 - (X ^ (k - 1) * B) * C (k : R)

/-- The coefficient of `y^(j-1)` in the quadratic coefficient differential
is the difference of the two sides of the recurrence. -/
theorem coeff_quadraticCoefficientDifferential
    {R : Type*} [CommRing R]
    (g : R) (k j : ℕ) (B : R[X]) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (quadraticCoefficientDifferential g k B).coeff (j - 1) =
      ((2 * j : ℕ) : R) * g * B.coeff j -
        if k ≤ j then ((2 * j - k : ℕ) : R) * B.coeff (j - k) else 0 := by
  by_cases hkj : k ≤ j
  · by_cases heq : j = k
    · subst j
      have hnot : ¬ k ≤ k - 1 := by omega
      have hidx : k - 1 - (k - 1) = 0 := by omega
      have hsucc : k - 1 + 1 = k := by omega
      simp only [quadraticCoefficientDifferential, coeff_sub, coeff_C_mul, coeff_mul_C,
        coeff_X_pow_mul', coeff_derivative, hnot, if_false, hidx, hsucc, hkj, if_true,
        if_pos (le_refl (k - 1)), Nat.sub_self]
      have hcastSucc : ((k - 1 : ℕ) : R) + 1 = (k : R) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : R)) hsucc
      have hscalarNat : 2 * k - k = k := by omega
      rw [hcastSucc, hscalarNat]
      push_cast
      ring
    · have hlt : k < j := lt_of_le_of_ne hkj (Ne.symm heq)
      have hkpred : k ≤ j - 1 := by omega
      have hkone : k - 1 ≤ j - 1 := by omega
      have hidxOne : j - 1 - k + 1 = j - k := by omega
      have hidxTwo : j - 1 - (k - 1) = j - k := by omega
      simp only [quadraticCoefficientDifferential, coeff_sub, coeff_C_mul, coeff_mul_C,
        coeff_X_pow_mul', coeff_derivative, hkj, if_true, hkpred, hkone, hidxOne, hidxTwo]
      have hindexZero : j - 1 + 1 = j := by omega
      have hcastSucc : ((j - 1 : ℕ) : R) + 1 = (j : R) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : R)) hindexZero
      have hcastShift : ((j - 1 - k : ℕ) : R) + 1 = ((j - k : ℕ) : R) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : R)) hidxOne
      have hscalarNat : 2 * j - k = 2 * (j - k) + k := by omega
      rw [hindexZero, hcastSucc, hcastShift, hscalarNat]
      push_cast
      ring
  · have hnotPred : ¬ k ≤ j - 1 := by omega
    have hnotOne : ¬ k - 1 ≤ j - 1 := by omega
    have hsucc : j - 1 + 1 = j := by omega
    simp only [quadraticCoefficientDifferential, coeff_sub, coeff_C_mul, coeff_mul_C,
      coeff_X_pow_mul', coeff_derivative, hkj, if_false, hnotPred, hnotOne, hsucc]
    have hcastSucc : ((j - 1 : ℕ) : R) + 1 = (j : R) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : R)) hsucc
    rw [hcastSucc]
    push_cast
    ring

/-- Divisibility of the quadratic coefficient differential by `y^(m-1)`
implies the finite recurrence for the coefficients of `B`. -/
theorem satisfiesCoefficientRecurrenceOver_of_differential_dvd
    {R : Type*} [CommRing R] {g : R} {B : R[X]} {k m : ℕ}
    (hk : 1 ≤ k)
    (hdifferential : X ^ (m - 1) ∣ quadraticCoefficientDifferential g k B) :
    SatisfiesCoefficientRecurrenceOver g (fun j => B.coeff j) k m := by
  intro j hj hjm
  have hdegree : j - 1 < m - 1 := by omega
  have hzero := (X_pow_dvd_iff.mp hdifferential) (j - 1) hdegree
  rw [coeff_quadraticCoefficientDifferential g k j B hk hj] at hzero
  exact sub_eq_zero.mp hzero

/-- Over a domain of characteristic zero, the abstract recurrence forces
every controlled coefficient outside the zero residue class to vanish. -/
theorem coefficient_eq_zero_of_not_dvd_over
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {g : R} {b : ℕ → R} {k m n : ℕ}
    (hk : 1 ≤ k) (hg : g ≠ 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hnm : n < m) (hndvd : ¬ k ∣ n) :
    b n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn : 1 ≤ n := by
        by_contra hnpos
        have : n = 0 := by omega
        subst n
        exact hndvd (dvd_zero k)
      have hrelation := hrec n hn hnm
      by_cases hkn : k ≤ n
      · have hnk : k < n := by
          by_contra hnot
          have : n = k := by omega
          subst n
          exact hndvd (dvd_refl k)
        have hsub : n - k < n := Nat.sub_lt (by omega) (by omega)
        have hsubNotDvd : ¬ k ∣ n - k := by
          intro hdiv
          apply hndvd
          have hsum : n - k + k = n := Nat.sub_add_cancel hkn
          obtain ⟨q, hq⟩ := hdiv
          refine ⟨q + 1, ?_⟩
          calc
            n = n - k + k := hsum.symm
            _ = k * q + k := by rw [hq]
            _ = k * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
        have hzero := ih (n - k) hsub (by omega) hsubNotDvd
        rw [if_pos hkn, hzero, mul_zero] at hrelation
        have hscalar : (((2 * n : ℕ) : R)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (by omega)
        rcases mul_eq_zero.mp hrelation with hleft | hzero
        · rcases mul_eq_zero.mp hleft with hscalarZero | hgzero
          · exact (hscalar hscalarZero).elim
          · exact (hg hgzero).elim
        · exact hzero
      · rw [if_neg hkn] at hrelation
        have hscalar : (((2 * n : ℕ) : R)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (by omega)
        rcases mul_eq_zero.mp hrelation with hleft | hzero
        · rcases mul_eq_zero.mp hleft with hscalarZero | hgzero
          · exact (hscalar hscalarZero).elim
          · exact (hg hgzero).elim
        · exact hzero

/-- The abstract recurrence on the index `jk`. -/
theorem residue_coefficient_recurrence_over
    {R : Type*} [CommRing R] {g : R} {b : ℕ → R} {k m j : ℕ}
    (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hjm : j * k < m) :
    (((2 * (j * k) : ℕ) : R)) * g * b (j * k) =
      (((2 * (j * k) - k : ℕ) : R)) * b ((j - 1) * k) := by
  have hkj : k ≤ j * k := by
    calc
      k = 1 * k := by simp
      _ ≤ j * k := Nat.mul_le_mul_right k hj
  have hindex : j * k - k = (j - 1) * k := by
    rw [Nat.sub_mul]
    simp
  simpa [if_pos hkj, hindex] using hrec (j * k) (by
    exact Nat.mul_pos (by omega) (by omega)) hjm

/-- A ring homomorphism that sends `g` to zero sends each earlier controlled
residue coefficient to zero. -/
theorem residue_coefficient_map_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [CharZero S]
    {g : R} {b : ℕ → R} {k m j : ℕ} (specialize : R →+* S)
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hg : specialize g = 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hjm : j * k < m) :
    specialize (b ((j - 1) * k)) = 0 := by
  have hrelation := residue_coefficient_recurrence_over hk hj hrec hjm
  have himage := congrArg specialize hrelation
  have hpositive : 0 < 2 * (j * k) - k := by
    have hjk : 0 < j * k := Nat.mul_pos (by omega) (by omega)
    have hkj : k ≤ j * k := by
      calc
        k = 1 * k := by simp
        _ ≤ j * k := Nat.mul_le_mul_right k hj
    omega
  simp only [map_mul, map_natCast, hg, mul_zero, zero_mul] at himage
  exact (mul_eq_zero.mp himage.symm).resolve_left
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpositive))

/-- Suppose the coefficient ring is a domain and a specialization sends `g`
to zero.  Any polynomial agreeing with the specialized coefficients through
degree `m-1` is divisible by the last controlled multiple of `k`. -/
theorem mapped_coefficients_divisible
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {g : R} {b : ℕ → R} {B : ℂ[X]} {k m : ℕ}
    (specialize : R →+* ℂ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hg : g ≠ 0) (hmapg : specialize g = 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hcoeff : ∀ n < m, B.coeff n = specialize (b n)) :
    X ^ (((m - 1) / k) * k) ∣ B := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hbound : ((m - 1) / k) * k ≤ m - 1 := Nat.div_mul_le_self (m - 1) k
  have hnm : n < m := by omega
  rw [hcoeff n hnm]
  by_cases hdiv : k ∣ n
  · obtain ⟨q, rfl⟩ := hdiv
    have hq : q < (m - 1) / k := by
      apply (Nat.mul_lt_mul_left (by omega : 0 < k)).mp
      simpa [Nat.mul_comm] using hn
    have hqk : (q + 1) * k < m := by
      have hle : (q + 1) * k ≤ ((m - 1) / k) * k :=
        Nat.mul_le_mul_right k (by omega)
      omega
    simpa [Nat.mul_comm] using residue_coefficient_map_eq_zero
      specialize hk (by omega) hmapg hrec hqk
  · rw [coefficient_eq_zero_of_not_dvd_over hk hg hrec hnm hdiv, map_zero]

/-- If `(m-1)/k` is zero and the specialized constant coefficient vanishes,
the polynomial in the preceding theorem is divisible by `X^m`. -/
theorem mapped_coefficients_divisible_of_div_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {g : R} {b : ℕ → R} {B : ℂ[X]} {k m : ℕ}
    (specialize : R →+* ℂ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hg : g ≠ 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hcoeff : ∀ n < m, B.coeff n = specialize (b n))
    (hdivzero : (m - 1) / k = 0) (hconstant : specialize (b 0) = 0) :
    X ^ m ∣ B := by
  rw [X_pow_dvd_iff]
  intro n hnm
  rw [hcoeff n hnm]
  by_cases hnzero : n = 0
  · simpa [hnzero] using hconstant
  · have hmk : m ≤ k := by
      have : m - 1 < k := Nat.lt_of_div_eq_zero (by omega) hdivzero
      omega
    have hndvd : ¬ k ∣ n :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [coefficient_eq_zero_of_not_dvd_over hk hg hrec hnm hndvd, map_zero]

/-- The finite coefficient recurrence

`2 g j b_j = (2j-k) b_{j-k}`

with coefficients of negative index equal to zero.  The second branch in the
definition records this convention without introducing integer indices. -/
@[expose]
def SatisfiesCoefficientRecurrence
    (b : ℕ → ℂ[X]) (k m : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j < m →
    C (2 * (j : ℂ)) * X * b j =
      if k ≤ j then C ((2 * j - k : ℕ) : ℂ) * b (j - k) else 0

/-- The polynomial consisting of the coefficients of `b` through index
`m-1`, after setting `g` equal to zero. -/
@[expose]
noncomputable def specializedCoefficientTruncation
    (b : ℕ → ℂ[X]) (m : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range m, monomial j ((b j).eval 0)

theorem coeff_specializedCoefficientTruncation
    (b : ℕ → ℂ[X]) {m n : ℕ} (hnm : n < m) :
    (specializedCoefficientTruncation b m).coeff n = (b n).eval 0 := by
  classical
  unfold specializedCoefficientTruncation
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · rw [coeff_monomial, if_pos rfl]
  · intro j hj hne
    rw [coeff_monomial, if_neg hne]
  · intro hnnot
    exact (hnnot (Finset.mem_range.mpr hnm)).elim

/-- Away from the zero residue class modulo `k`, every coefficient controlled
by the recurrence vanishes. -/
theorem coefficient_eq_zero_of_not_dvd
    {b : ℕ → ℂ[X]} {k m n : ℕ}
    (hk : 1 ≤ k) (hrec : SatisfiesCoefficientRecurrence b k m)
    (hnm : n < m) (hndvd : ¬ k ∣ n) :
    b n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn : 1 ≤ n := by
        by_contra hnpos
        have : n = 0 := by omega
        subst n
        exact hndvd (dvd_zero k)
      have hrelation := hrec n hn hnm
      by_cases hkn : k ≤ n
      · have hnk : k < n := by
          by_contra hnot
          have : n = k := by omega
          subst n
          exact hndvd (dvd_refl k)
        have hsub : n - k < n := Nat.sub_lt (by omega) (by omega)
        have hsubNotDvd : ¬ k ∣ n - k := by
          intro hdiv
          apply hndvd
          have hsum : n - k + k = n := Nat.sub_add_cancel hkn
          obtain ⟨q, hq⟩ := hdiv
          refine ⟨q + 1, ?_⟩
          calc
            n = n - k + k := hsum.symm
            _ = k * q + k := by rw [hq]
            _ = k * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
        have hzero := ih (n - k) hsub (by omega) hsubNotDvd
        rw [if_pos hkn, hzero, mul_zero] at hrelation
        have hscalar : C (2 * (n : ℂ)) ≠ (0 : ℂ[X]) := by
          simp [show n ≠ 0 by omega]
        rcases mul_eq_zero.mp hrelation with hleft | hzero
        · rcases mul_eq_zero.mp hleft with hscalarZero | hXZero
          · exact (hscalar hscalarZero).elim
          · exact (X_ne_zero hXZero).elim
        · exact hzero
      · rw [if_neg hkn] at hrelation
        have hscalar : C (2 * (n : ℂ)) ≠ (0 : ℂ[X]) := by
          simp [show n ≠ 0 by omega]
        rcases mul_eq_zero.mp hrelation with hleft | hzero
        · rcases mul_eq_zero.mp hleft with hscalarZero | hXZero
          · exact (hscalar hscalarZero).elim
          · exact (X_ne_zero hXZero).elim
        · exact hzero

/-- The recurrence on an index divisible by `k`, in a form that does not use
division by a scalar. -/
theorem residue_coefficient_recurrence
    {b : ℕ → ℂ[X]} {k m j : ℕ}
    (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hjm : j * k < m) :
    C (2 * ((j * k : ℕ) : ℂ)) * X * b (j * k) =
      C ((2 * (j * k) - k : ℕ) : ℂ) * b ((j - 1) * k) := by
  have hkj : k ≤ j * k := by
    calc
      k = 1 * k := by simp
      _ ≤ j * k := Nat.mul_le_mul_right k hj
  have hindex : j * k - k = (j - 1) * k := by
    rw [Nat.sub_mul]
    simp
  simpa [if_pos hkj, hindex] using hrec (j * k) (by
    exact Nat.mul_pos (by omega) (by omega)) hjm

/-- Every residue coefficient before the last controlled multiple of `k`
vanishes after setting `g` equal to zero. -/
theorem residue_coefficient_eval_zero
    {b : ℕ → ℂ[X]} {k m j : ℕ}
    (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hjm : j * k < m) :
    (b ((j - 1) * k)).eval 0 = 0 := by
  have hrelation := residue_coefficient_recurrence hk hj hrec hjm
  have heval := congrArg (Polynomial.eval (0 : ℂ)) hrelation
  have hpositive : 0 < 2 * (j * k) - k := by
    have hjk : 0 < j * k := Nat.mul_pos (by omega) (by omega)
    have hkj : k ≤ j * k := by
      calc
        k = 1 * k := by simp
        _ ≤ j * k := Nat.mul_le_mul_right k hj
    omega
  simp only [eval_mul, eval_C, eval_X, mul_zero, zero_mul] at heval
  exact (mul_eq_zero.mp heval.symm).resolve_left (by
    exact_mod_cast (Nat.ne_of_gt hpositive))

/-- Every controlled residue coefficient before `b_(jk)` contains a positive
power of `g`. -/
theorem X_dvd_residue_coefficient
    {b : ℕ → ℂ[X]} {k m j : ℕ}
    (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hjm : j * k < m) :
    X ∣ b ((j - 1) * k) := by
  rw [X_dvd_iff]
  rw [coeff_zero_eq_eval_zero]
  exact residue_coefficient_eval_zero hk hj hrec hjm

/-- Let `B` agree through degree `m-1` with the specialization at `g = 0` of
the coefficient series.  It is divisible by the largest controlled power of
`y` that is a multiple of `k`. -/
theorem specialized_coefficients_divisible
    {b : ℕ → ℂ[X]} {B : ℂ[X]} {k m : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0) :
    X ^ (((m - 1) / k) * k) ∣ B := by
  rw [X_pow_dvd_iff]
  intro n hn
  have hbound : ((m - 1) / k) * k ≤ m - 1 := Nat.div_mul_le_self (m - 1) k
  have hnm : n < m := by omega
  rw [hcoeff n hnm]
  by_cases hdiv : k ∣ n
  · obtain ⟨q, rfl⟩ := hdiv
    have hq : q < (m - 1) / k := by
      apply (Nat.mul_lt_mul_left (by omega : 0 < k)).mp
      simpa [Nat.mul_comm] using hn
    have hqk : (q + 1) * k < m := by
      have hle : (q + 1) * k ≤ ((m - 1) / k) * k :=
        Nat.mul_le_mul_right k (by omega)
      omega
    simpa [Nat.mul_comm] using
      residue_coefficient_eval_zero hk (by omega) hrec hqk
  · rw [coefficient_eq_zero_of_not_dvd hk hrec hnm hdiv, eval_zero]

/-- The concrete finite truncation satisfies the preceding divisibility
conclusion. -/
theorem specializedCoefficientTruncation_divisible
    {b : ℕ → ℂ[X]} {k m : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m) :
    X ^ (((m - 1) / k) * k) ∣ specializedCoefficientTruncation b m := by
  exact specialized_coefficients_divisible hk hm hrec
    (fun _ hn => coeff_specializedCoefficientTruncation b hn)

/-- If no positive multiple of `k` is controlled and the constant
coefficient vanishes at `g = 0`, then the specialization is divisible by
`y^m`. -/
theorem specialized_coefficients_divisible_of_div_eq_zero
    {b : ℕ → ℂ[X]} {B : ℂ[X]} {k m : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0)
    (hdivzero : (m - 1) / k = 0) (hconstant : (b 0).eval 0 = 0) :
    X ^ m ∣ B := by
  rw [X_pow_dvd_iff]
  intro n hnm
  rw [hcoeff n hnm]
  by_cases hnzero : n = 0
  · simpa [hnzero] using hconstant
  · have hmk : m ≤ k := by
      have : m - 1 < k := Nat.lt_of_div_eq_zero (by omega) hdivzero
      omega
    have hndvd : ¬ k ∣ n := by
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [coefficient_eq_zero_of_not_dvd hk hrec hnm hndvd, eval_zero]

/-- Under the extra constant coefficient condition, the concrete finite
truncation is divisible by `X^m`. -/
theorem specializedCoefficientTruncation_divisible_of_div_eq_zero
    {b : ℕ → ℂ[X]} {k m : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hdivzero : (m - 1) / k = 0) (hconstant : (b 0).eval 0 = 0) :
    X ^ m ∣ specializedCoefficientTruncation b m := by
  exact specialized_coefficients_divisible_of_div_eq_zero hk hm hrec
    (fun _ hn => coeff_specializedCoefficientTruncation b hn) hdivzero hconstant

/-- If the derivative of `A` is divisible by `X^(m-1)`, subtracting the
constant term makes `A` divisible by `X^m`. -/
theorem sub_constant_divisible_of_derivative
    {A : ℂ[X]} {m : ℕ} (hm : 1 ≤ m)
    (hderivative : X ^ (m - 1) ∣ A.derivative) :
    X ^ m ∣ A - C (A.coeff 0) := by
  rw [X_pow_dvd_iff]
  intro n hnm
  by_cases hnzero : n = 0
  · simp [hnzero]
  · have hpred : n - 1 < m - 1 := by omega
    have hcoefficient := (X_pow_dvd_iff.mp hderivative) (n - 1) hpred
    rw [coeff_derivative] at hcoefficient
    have hcast : ((n - 1 : ℕ) : ℂ) + 1 = n := by
      norm_cast
      omega
    rw [hcast] at hcoefficient
    have hindex : n - 1 + 1 = n := by omega
    rw [hindex] at hcoefficient
    have hscalar : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hnzero
    have hAn : A.coeff n = 0 :=
      (mul_eq_zero.mp hcoefficient).resolve_right hscalar
    rw [coeff_sub, hAn, coeff_C_of_ne_zero hnzero, sub_zero]

/-- Divisibility by a power of `X` is multiplied by `q` after substitution
of `X^q` for `X`. -/
theorem X_pow_dvd_comp_X_pow
    {P : ℂ[X]} {n q : ℕ} (hP : X ^ n ∣ P) :
    X ^ (q * n) ∣ P.comp (X ^ q) := by
  obtain ⟨R, hR⟩ := hP
  refine ⟨R.comp (X ^ q), ?_⟩
  rw [hR, mul_comp, X_pow_comp, ← pow_mul]

/-- The two summands obtained from the substitutions `y = t^q` and
`x = epsilon t^r` have the expected common power of `t`. -/
theorem weighted_substitution_divisible
    {A B : ℂ[X]} {m n q r : ℕ} (epsilon : ℂ)
    (hA : X ^ m ∣ A) (hB : X ^ n ∣ B) :
    X ^ min (q * m) (r + q * n) ∣
      A.comp (X ^ q) + C epsilon * X ^ r * B.comp (X ^ q) := by
  have hAcomp : X ^ (q * m) ∣ A.comp (X ^ q) :=
    X_pow_dvd_comp_X_pow hA
  have hBcomp : X ^ (q * n) ∣ B.comp (X ^ q) :=
    X_pow_dvd_comp_X_pow hB
  obtain ⟨R, hR⟩ := hBcomp
  have hshift : X ^ (r + q * n) ∣ C epsilon * X ^ r * B.comp (X ^ q) := by
    refine ⟨C epsilon * R, ?_⟩
    rw [hR, pow_add]
    ring
  have hleft : X ^ min (q * m) (r + q * n) ∣ A.comp (X ^ q) :=
    (pow_dvd_pow X (min_le_left _ _)).trans hAcomp
  have hright : X ^ min (q * m) (r + q * n) ∣
      C epsilon * X ^ r * B.comp (X ^ q) :=
    (pow_dvd_pow X (min_le_right _ _)).trans hshift
  exact dvd_add hleft hright

/-- The abstract coefficient recurrence gives the odd branch order estimate
after specialization of the coefficient ring. -/
theorem odd_branch_mapped_coefficients_divisible
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {g : R} {b : ℕ → R} {A B : ℂ[X]} {k m : ℕ}
    (specialize : R →+* ℂ) (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hg : g ≠ 0)
    (hmapg : specialize g = 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hcoeff : ∀ n < m, B.coeff n = specialize (b n))
    (hA : X ^ m ∣ A) :
    X ^ min (2 * m) ((2 * ((m - 1) / k) + 1) * k) ∣
      A.comp (X ^ 2) + C epsilon * X ^ k * B.comp (X ^ 2) := by
  have hB := mapped_coefficients_divisible specialize hk hm hg hmapg hrec hcoeff
  have hweighted :=
    weighted_substitution_divisible epsilon hA hB (q := 2) (r := k)
  have hexponent :
      k + 2 * (((m - 1) / k) * k) =
        (2 * ((m - 1) / k) + 1) * k := by
    ring
  simpa [hexponent] using hweighted

/-- When `(m-1)/k` is zero, vanishing of the specialized constant coefficient
gives order at least `2m` on the odd branch. -/
theorem odd_branch_mapped_coefficients_divisible_of_div_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {g : R} {b : ℕ → R} {A B : ℂ[X]} {k m : ℕ}
    (specialize : R →+* ℂ) (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hg : g ≠ 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hcoeff : ∀ n < m, B.coeff n = specialize (b n))
    (hdivzero : (m - 1) / k = 0) (hconstant : specialize (b 0) = 0)
    (hA : X ^ m ∣ A) :
    X ^ (2 * m) ∣
      A.comp (X ^ 2) + C epsilon * X ^ k * B.comp (X ^ 2) := by
  have hB := mapped_coefficients_divisible_of_div_eq_zero
    specialize hk hm hg hrec hcoeff hdivzero hconstant
  have hweighted := weighted_substitution_divisible epsilon hA hB (q := 2) (r := k)
  have hmin : min (2 * m) (k + 2 * m) = 2 * m := min_eq_left (by omega)
  simpa [hmin] using hweighted

/-- The abstract coefficient recurrence gives the even branch order estimate
after specialization of the coefficient ring. -/
theorem even_branch_mapped_coefficients_divisible
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {g : R} {b : ℕ → R} {A B : ℂ[X]} {k m a : ℕ}
    (specialize : R →+* ℂ) (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hg : g ≠ 0)
    (hmapg : specialize g = 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hcoeff : ∀ n < m, B.coeff n = specialize (b n))
    (hA : X ^ m ∣ A) :
    X ^ min m (a + ((m - 1) / k) * k) ∣
      A + C epsilon * X ^ a * B := by
  have hB := mapped_coefficients_divisible specialize hk hm hg hmapg hrec hcoeff
  simpa using
    (weighted_substitution_divisible epsilon hA hB (q := 1) (r := a))

/-- When `(m-1)/k` is zero, vanishing of the specialized constant coefficient
gives order at least `m` on either even branch. -/
theorem even_branch_mapped_coefficients_divisible_of_div_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {g : R} {b : ℕ → R} {A B : ℂ[X]} {k m a : ℕ}
    (specialize : R →+* ℂ) (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hg : g ≠ 0)
    (hrec : SatisfiesCoefficientRecurrenceOver g b k m)
    (hcoeff : ∀ n < m, B.coeff n = specialize (b n))
    (hdivzero : (m - 1) / k = 0) (hconstant : specialize (b 0) = 0)
    (hA : X ^ m ∣ A) :
    X ^ m ∣ A + C epsilon * X ^ a * B := by
  have hB := mapped_coefficients_divisible_of_div_eq_zero
    specialize hk hm hg hrec hcoeff hdivzero hconstant
  have hweighted := weighted_substitution_divisible epsilon hA hB (q := 1) (r := a)
  have hmin : min m (a + m) = m := min_eq_left (by omega)
  simpa [hmin] using hweighted

/-- The finite polynomial form of the order estimate on the branch
`y = t^2`, `x = epsilon t^k`. -/
theorem odd_branch_polynomial_divisible
    {b : ℕ → ℂ[X]} {A B : ℂ[X]} {k m : ℕ} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0)
    (hA : X ^ m ∣ A) :
    X ^ min (2 * m) ((2 * ((m - 1) / k) + 1) * k) ∣
      A.comp (X ^ 2) + C epsilon * X ^ k * B.comp (X ^ 2) := by
  have hB := specialized_coefficients_divisible hk hm hrec hcoeff
  have hweighted :=
    weighted_substitution_divisible epsilon hA hB (q := 2) (r := k)
  have hexponent :
      k + 2 * (((m - 1) / k) * k) =
        (2 * ((m - 1) / k) + 1) * k := by
    ring
  simpa [hexponent] using hweighted

/-- The derivative condition on `A` and the coefficient recurrence together
give the odd branch order estimate after subtracting the constant term of
`A`. -/
theorem odd_branch_polynomial_divisible_of_derivative
    {b : ℕ → ℂ[X]} {A B : ℂ[X]} {k m : ℕ} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0)
    (hderivative : X ^ (m - 1) ∣ A.derivative) :
    X ^ min (2 * m) ((2 * ((m - 1) / k) + 1) * k) ∣
      (A - C (A.coeff 0)).comp (X ^ 2) +
        C epsilon * X ^ k * B.comp (X ^ 2) := by
  exact odd_branch_polynomial_divisible epsilon hk hm hrec hcoeff
    (sub_constant_divisible_of_derivative hm hderivative)

/-- When the quotient `(m-1)/k` is zero, the extra vanishing of `b_0(0)`
gives the stronger order `2m` on the branch `y = t^2`. -/
theorem odd_branch_polynomial_divisible_of_div_eq_zero
    {b : ℕ → ℂ[X]} {A B : ℂ[X]} {k m : ℕ} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0)
    (hdivzero : (m - 1) / k = 0) (hconstant : (b 0).eval 0 = 0)
    (hA : X ^ m ∣ A) :
    X ^ (2 * m) ∣
      A.comp (X ^ 2) + C epsilon * X ^ k * B.comp (X ^ 2) := by
  have hB := specialized_coefficients_divisible_of_div_eq_zero
    hk hm hrec hcoeff hdivzero hconstant
  have hweighted := weighted_substitution_divisible epsilon hA hB (q := 2) (r := k)
  have hmin : min (2 * m) (k + 2 * m) = 2 * m := min_eq_left (by omega)
  simpa [hmin] using hweighted

/-- The finite polynomial form of the order estimate on either branch
`y = t`, `x = epsilon t^a` when `k = 2a`. -/
theorem even_branch_polynomial_divisible
    {b : ℕ → ℂ[X]} {A B : ℂ[X]} {k m a : ℕ} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0)
    (hA : X ^ m ∣ A) :
    X ^ min m (a + ((m - 1) / k) * k) ∣
      A + C epsilon * X ^ a * B := by
  have hB := specialized_coefficients_divisible hk hm hrec hcoeff
  simpa using
    (weighted_substitution_divisible epsilon hA hB (q := 1) (r := a))

/-- The derivative condition on `A` and the coefficient recurrence together
give the even branch order estimate after subtracting the constant term of
`A`. -/
theorem even_branch_polynomial_divisible_of_derivative
    {b : ℕ → ℂ[X]} {A B : ℂ[X]} {k m a : ℕ} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0)
    (hderivative : X ^ (m - 1) ∣ A.derivative) :
    X ^ min m (a + ((m - 1) / k) * k) ∣
      A - C (A.coeff 0) + C epsilon * X ^ a * B := by
  exact even_branch_polynomial_divisible epsilon hk hm hrec hcoeff
    (sub_constant_divisible_of_derivative hm hderivative)

/-- If `(m-1)/k` is zero and `b_0(0)` vanishes, both polynomial branch
restrictions in the even case have order at least `m`. -/
theorem even_branch_polynomial_divisible_of_div_eq_zero
    {b : ℕ → ℂ[X]} {A B : ℂ[X]} {k m a : ℕ} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrence b k m)
    (hcoeff : ∀ n < m, B.coeff n = (b n).eval 0)
    (hdivzero : (m - 1) / k = 0) (hconstant : (b 0).eval 0 = 0)
    (hA : X ^ m ∣ A) :
    X ^ m ∣ A + C epsilon * X ^ a * B := by
  have hB := specialized_coefficients_divisible_of_div_eq_zero
    hk hm hrec hcoeff hdivzero hconstant
  have hweighted := weighted_substitution_divisible epsilon hA hB (q := 1) (r := a)
  have hmin : min m (a + m) = m := min_eq_left (by omega)
  simpa [hmin] using hweighted

end OnLeConjecture.DTwo
