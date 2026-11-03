/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# The domain underlying a cyclic component

The polynomial `x² + a` is not a square when `a` is a nonzero constant in
a domain of characteristic zero. Integral closedness gives the same
conclusion in the fraction field. Applied over `ℂ[y]`, this proves that
`X² - x² - c y^L` is irreducible for `c ≠ 0`, and that its quotient is a
domain. The argument works for every natural exponent `L`, including zero.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- A nonzero constant term prevents the polynomial `x² + a` from being
a square in characteristic zero. -/
theorem X_sq_add_C_ne_polynomial_square
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {a : R} (ha : a ≠ 0) (q : Polynomial R) :
    q ^ 2 ≠ X ^ 2 + C a := by
  intro hq
  have hdegree := congrArg _root_.Polynomial.natDegree hq
  rw [natDegree_pow, natDegree_X_pow_add_C] at hdegree
  have hdegreeOne : q.natDegree ≤ 1 := by omega
  obtain ⟨u, v, hlinear⟩ := exists_eq_X_add_C_of_natDegree_le_one hdegreeOne
  rw [hlinear] at hq
  have hexpand :
      (C u * X + C v : Polynomial R) ^ 2 =
        C (u ^ 2) * X ^ 2 + C (2 * u * v) * X + C (v ^ 2) := by
    simp only [map_pow, map_mul, map_ofNat]
    ring
  rw [hexpand] at hq
  have hconstant : v ^ 2 = a := by
    have h := congrArg (fun p : Polynomial R ↦ p.coeff 0) hq
    norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_X,
      coeff_C, coeff_X_pow] at h
    simpa only [if_false, if_true, mul_zero, mul_one, zero_add, add_zero] using h
  have hlinearCoeff : 2 * u * v = 0 := by
    have h := congrArg (fun p : Polynomial R ↦ p.coeff 1) hq
    norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_X,
      coeff_C, coeff_X_pow] at h
    simpa only [if_false, if_true, mul_zero, mul_one, zero_add, add_zero] using h
  have hleading : u ^ 2 = 1 := by
    have h := congrArg (fun p : Polynomial R ↦ p.coeff 2) hq
    norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_X,
      coeff_C, coeff_X_pow] at h
    simpa only [if_false, if_true, mul_zero, mul_one, zero_add, add_zero] using h
  have hu : u ≠ 0 := by
    intro h
    simp [h] at hleading
  have htwo : (2 : R) ≠ 0 := by norm_num
  have hv : v = 0 :=
    (mul_eq_zero.mp hlinearCoeff).resolve_left (mul_ne_zero htwo hu)
  exact ha (by simpa [hv] using hconstant.symm)

/-- A square root in the fraction field would be integral and hence would
already be a polynomial. -/
theorem X_sq_add_C_ne_fraction_square
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [IsIntegrallyClosed R]
    {a : R} (ha : a ≠ 0) (q : FractionRing (Polynomial R)) :
    q ^ 2 ≠ algebraMap (Polynomial R) (FractionRing (Polynomial R))
      (X ^ 2 + C a) := by
  intro hq
  have hintegral : IsIntegral (Polynomial R) (q ^ 2) := by
    rw [hq]
    exact isIntegral_algebraMap
  obtain ⟨p, hp⟩ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
      (R := Polynomial R) (K := FractionRing (Polynomial R))
      (by norm_num : 0 < (2 : ℕ)) hintegral
  have hpoly : p ^ 2 = X ^ 2 + C a := by
    apply IsFractionRing.injective (Polynomial R) (FractionRing (Polynomial R))
    simpa only [map_pow, hp] using hq
  exact X_sq_add_C_ne_polynomial_square ha p hpoly

/-- The iterated polynomial ring `ℂ[y][x]`, representing `ℂ[x,y]`. -/
abbrev CyclicBaseRing := Polynomial (Polynomial ℂ)

/-- The radicand `x² + c y^L` in the cyclic component equation. -/
@[expose]
noncomputable def cyclicSquare (L : ℕ) (c : ℂ) : CyclicBaseRing :=
  X ^ 2 + C (C c * X ^ L)

/-- The radicand is not a square in the rational function field in `x,y`. -/
theorem cyclicSquare_ne_fraction_square
    (L : ℕ) {c : ℂ} (hc : c ≠ 0) (q : FractionRing CyclicBaseRing) :
    q ^ 2 ≠ algebraMap CyclicBaseRing (FractionRing CyclicBaseRing)
      (cyclicSquare L c) := by
  apply X_sq_add_C_ne_fraction_square
  exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ X_ne_zero)

/-- The component polynomial, with `X` the outermost variable. -/
@[expose]
noncomputable def cyclicComponentPolynomial (L : ℕ) (c : ℂ) :
    Polynomial CyclicBaseRing :=
  X ^ 2 - C (cyclicSquare L c)

/-- Gauss's lemma and the nonsquare radicand prove irreducibility of the
component equation over `ℂ[y][x]`. -/
theorem cyclicComponentPolynomial_irreducible
    (L : ℕ) {c : ℂ} (hc : c ≠ 0) :
    Irreducible (cyclicComponentPolynomial L c) := by
  have hmonic : (cyclicComponentPolynomial L c).Monic :=
    monic_X_pow_sub_C (cyclicSquare L c) (by norm_num)
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing CyclicBaseRing)).mpr
  simp only [cyclicComponentPolynomial, _root_.Polynomial.map_sub,
    _root_.Polynomial.map_pow, _root_.Polynomial.map_X, _root_.Polynomial.map_C]
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro q
  exact cyclicSquare_ne_fraction_square L hc q

/-- The component polynomial is a prime element of the polynomial ring. -/
theorem cyclicComponentPolynomial_prime
    (L : ℕ) {c : ℂ} (hc : c ≠ 0) :
    Prime (cyclicComponentPolynomial L c) :=
  (cyclicComponentPolynomial_irreducible L hc).prime

/-- The ideal generated by the component equation is prime. -/
theorem cyclicComponentIdeal_isPrime
    (L : ℕ) {c : ℂ} (hc : c ≠ 0) :
    (Ideal.span ({cyclicComponentPolynomial L c} :
      Set (Polynomial CyclicBaseRing))).IsPrime := by
  have hprime := cyclicComponentPolynomial_prime L hc
  exact (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime

/-- The polynomial quotient `ℂ[y][x][X] / (X² - x² - c y^L)`.
For positive `L`, this is the weighted homogeneous coordinate ring of
the projective cyclic component. -/
abbrev CyclicComponentRing (L : ℕ) (c : ℂ) :=
  AdjoinRoot (cyclicComponentPolynomial L c)

/-- The polynomial quotient defining the cyclic component is a domain. -/
theorem cyclicComponentRing_isDomain
    (L : ℕ) {c : ℂ} (hc : c ≠ 0) :
    IsDomain (CyclicComponentRing L c) :=
  AdjoinRoot.isDomain_of_prime (cyclicComponentPolynomial_prime L hc)

end OnLeConjecture.DTwo
