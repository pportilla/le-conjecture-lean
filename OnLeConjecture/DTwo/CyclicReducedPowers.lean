/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicReducedNormRoots

/-!
# Reduction and compatibility of cyclic powers

The degree identity determines the reduced exponents. Coprime powers
with a compatible relation admit a simultaneous root by Bezout's identity.
-/

public section

namespace OnLeConjecture.DTwo

/-- Exact reduced exponents for the unreduced degree identity. -/
theorem exists_cyclic_reduced_exponents
    (k p j d : ℕ) (_hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : p * j = k * d) :
    ∃ h q r : ℕ, 0 < h ∧ 3 ≤ q ∧ Odd q ∧ 0 < r ∧ Nat.Coprime q r ∧
      p = h * q ∧ d % p = h * r ∧ ¬ q ∣ r ∧
      k < k + j ∧ ¬ k ∣ k + j ∧ k ∣ q * (k + j) ∧
      q * Nat.gcd k (k + j) = k := by
  let h := Nat.gcd p d
  let q := p / h
  let b := d / h
  have hh : 0 < h := Nat.gcd_pos_of_pos_left d hp.pos
  have hfactorP : p = h * q := (Nat.mul_div_cancel' (Nat.gcd_dvd_left p d)).symm
  have hfactorD : d = h * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right p d)).symm
  have hcoprime : Nat.Coprime q b := Nat.coprime_div_gcd_div_gcd hh
  have hqodd : Odd q := by rw [hfactorP] at hp; exact (Nat.odd_mul.mp hp).2
  have hnotD : ¬ p ∣ d := by
    rintro ⟨a, ha⟩
    apply hj
    refine ⟨a, ?_⟩
    rw [ha] at hdegree
    nlinarith [hp.pos]
  have hqone : q ≠ 1 := by
    intro hq
    apply hnotD
    refine ⟨b, ?_⟩
    rw [hfactorD, hfactorP, hq, mul_one]
  have hq : 3 ≤ q := by
    obtain ⟨a, ha⟩ := hqodd
    omega
  have hrelation : q * j = k * b := by
    rw [hfactorP, hfactorD] at hdegree
    nlinarith
  have hqk : q ∣ k := hcoprime.dvd_of_dvd_mul_right ⟨j, hrelation.symm⟩
  obtain ⟨δ, hδ⟩ := hqk
  have hjfactor : j = δ * b := by
    rw [hδ] at hrelation
    nlinarith
  have hmodcoprime : Nat.Coprime q (b % q) := by
    change Nat.gcd q (b % q) = 1
    rw [Nat.gcd_comm, ← Nat.gcd_rec]
    exact hcoprime
  have hmodnot : ¬ q ∣ b % q := by
    intro hdiv
    have hqeq : q = 1 := by
      rw [Nat.Coprime, Nat.gcd_eq_left_iff_dvd.mpr hdiv] at hmodcoprime
      exact hmodcoprime
    exact hqone hqeq
  have hmodpos : 0 < b % q := by
    by_contra hz
    exact hmodnot (by simp [show b % q = 0 by omega])
  have hjpos : 0 < j := by
    by_contra hzero
    exact hj (by simp [show j = 0 by omega])
  refine ⟨h, q, b % q, hh, hq, hqodd, hmodpos, hmodcoprime, hfactorP, ?_,
    hmodnot, by omega, ?_, ?_, ?_⟩
  · rw [hfactorD, hfactorP, Nat.mul_mod_mul_left]
  · intro hdiv
    have := Nat.dvd_sub hdiv (dvd_refl k)
    exact hj (by simpa only [Nat.add_sub_cancel_left] using this)
  · rw [hδ, hjfactor]
    exact ⟨q + b, by ring⟩
  · have hgcd : Nat.gcd k (k + j) = δ := by
      rw [hδ, hjfactor, show q * δ + δ * b = δ * (q + b) by ring,
        Nat.mul_comm q δ, Nat.gcd_mul_left, Nat.gcd_self_add_right,
        hcoprime.gcd_eq_one, mul_one]
    rw [hgcd]
    exact hδ.symm

/-- Bezout's identity gives a simultaneous root of compatible coprime powers. -/
theorem exists_compatible_coprime_powers
    {G : Type*} [CommGroup G] (q r : ℕ) (hcoprime : Nat.Coprime q r)
    (a b : G) (hrelation : a ^ r = b ^ q) :
    ∃ w : G, w ^ q = a ∧ w ^ r = b := by
  let u := Nat.gcdA q r
  let v := Nat.gcdB q r
  have hbezout : (q : ℤ) * u + (r : ℤ) * v = 1 := by
    simpa only [hcoprime.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab q r).symm
  let w : G := a ^ u * b ^ v
  have hpower (n : ℕ) : w ^ n = (a ^ n) ^ u * (b ^ n) ^ v := by
    dsimp [w]
    rw [mul_pow]
    congr 1
    · rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast]
    · rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast]
  refine ⟨w, ?_, ?_⟩
  · rw [hpower, ← hrelation, ← zpow_natCast a q, ← zpow_mul,
      ← zpow_natCast a r, ← zpow_mul, ← zpow_add, hbezout, zpow_one]
  · rw [hpower, hrelation, ← zpow_natCast b q, ← zpow_mul,
      ← zpow_natCast b r, ← zpow_mul, ← zpow_add, hbezout, zpow_one]

/-- Compatible complex powers lift through the common ramification factor. -/
theorem exists_complex_compatible_powers
    (h q r : ℕ) (hh : 0 < h) (hcoprime : Nat.Coprime q r)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hrelation : a ^ r = b ^ q) :
    ∃ x : ℂ, x ≠ 0 ∧ x ^ (h * q) = a ∧ x ^ (h * r) = b := by
  obtain ⟨w, hwq, hwr⟩ := exists_compatible_coprime_powers q r hcoprime
    (Units.mk0 a ha) (Units.mk0 b hb) (by ext; exact hrelation)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) hh
  have hxzero : x ≠ 0 := by
    intro hz
    exact w.ne_zero (by simpa [hz, zero_pow hh.ne'] using hx.symm)
  refine ⟨x, hxzero, ?_, ?_⟩
  · rw [pow_mul, hx]
    exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) hwq
  · rw [pow_mul, hx]
    exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) hwr

end OnLeConjecture.DTwo
