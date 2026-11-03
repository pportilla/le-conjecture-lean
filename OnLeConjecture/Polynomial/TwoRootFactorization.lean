/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.Ring

/-!
# Factorization with two prescribed roots

This file factors a complex polynomial whose only roots are `i` and `-i`
when these roots have equal multiplicity.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

/-- Root multiplicity is multiplied by taking a power of a nonzero
polynomial. -/
theorem rootMultiplicity_pow_eq_mul
    (p : _root_.Polynomial ℂ) (hp : p ≠ 0) (z : ℂ) (n : ℕ) :
    (p ^ n).rootMultiplicity z = n * p.rootMultiplicity z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp),
        ih]
      exact (Nat.succ_mul n (p.rootMultiplicity z)).symm

/-- Multiplying a linear factor by a nonzero scalar does not alter the
root multiplicity of its powers. -/
theorem rootMultiplicity_nonzero_scalar_mul_X_sub_C_pow
    (c : ℂ) (hc : c ≠ 0) (x y : ℂ) (n : ℕ) :
    ((C c * (X - C y)) ^ n).rootMultiplicity x =
      if x = y then n else 0 := by
  rw [rootMultiplicity_pow_eq_mul _
    (mul_ne_zero (C_ne_zero.mpr hc) (monic_X_sub_C y).ne_zero) x n,
    rootMultiplicity_mul
      (mul_ne_zero (C_ne_zero.mpr hc) (monic_X_sub_C y).ne_zero),
    rootMultiplicity_C, rootMultiplicity_X_sub_C]
  split_ifs
  all_goals simp_all

/-- A nonzero complex polynomial whose only roots are `i` and `-i` is the
product of the corresponding linear factors with their root
multiplicities. -/
theorem eq_leadingCoeff_mul_node_factors_of_two_roots
    (p : _root_.Polynomial ℂ)
    (hp : p ≠ 0)
    (hroots : ∀ (z : ℂ), p.eval z = 0 →
      z = Complex.I ∨ z = -Complex.I) :
    p = C p.leadingCoeff *
      (X - C Complex.I) ^ p.rootMultiplicity Complex.I *
      (X - C (-Complex.I)) ^ p.rootMultiplicity (-Complex.I) := by
  let a := p.rootMultiplicity Complex.I
  let b := p.rootMultiplicity (-Complex.I)
  have hrootMultiset : p.roots =
      Multiset.replicate a Complex.I +
        Multiset.replicate b (-Complex.I) := by
    ext z
    by_cases hzI : z = Complex.I
    · subst z
      have hne : Complex.I ≠ -Complex.I := by
        intro h
        have := congrArg Complex.im h
        norm_num at this
      simp only [Multiset.count_add, Multiset.count_replicate,
        count_roots, a, b]
      simp [Ne.symm hne]
    · by_cases hzNegI : z = -Complex.I
      · subst z
        have hne : -Complex.I ≠ Complex.I := by
          intro h
          have := congrArg Complex.im h
          norm_num at this
        simp only [Multiset.count_add, Multiset.count_replicate,
          count_roots, a, b]
        simp [Ne.symm hne]
      · have hzNotRoot : z ∉ p.roots := by
          intro hz
          have hzero : p.eval z = 0 := (mem_roots hp).mp hz
          rcases hroots z hzero with h | h
          · exact hzI h
          · exact hzNegI h
        rw [Multiset.count_eq_zero.mpr hzNotRoot]
        simp only [Multiset.count_add, Multiset.count_replicate,
          if_neg (Ne.symm hzI), if_neg (Ne.symm hzNegI), add_zero]
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
      (IsAlgClosed.splits p).eq_prod_roots
    _ = C p.leadingCoeff *
        (X - C Complex.I) ^ p.rootMultiplicity Complex.I *
        (X - C (-Complex.I)) ^ p.rootMultiplicity (-Complex.I) := by
      rw [hrootMultiset, Multiset.map_add, Multiset.prod_add,
        Multiset.map_replicate, Multiset.map_replicate,
        Multiset.prod_replicate, Multiset.prod_replicate]
      simp [a, b, mul_assoc]

/-- Under the hypotheses of the preceding factorization, the sum of the
two root multiplicities is the degree. -/
theorem node_rootMultiplicity_add_eq_natDegree
    (p : _root_.Polynomial ℂ)
    (hp : p ≠ 0)
    (hroots : ∀ (z : ℂ), p.eval z = 0 →
      z = Complex.I ∨ z = -Complex.I) :
    p.rootMultiplicity Complex.I + p.rootMultiplicity (-Complex.I) =
      p.natDegree := by
  have hfactor := eq_leadingCoeff_mul_node_factors_of_two_roots p hp hroots
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hfirst : (X - C Complex.I : Polynomial ℂ) ^
      p.rootMultiplicity Complex.I ≠ 0 :=
    ((monic_X_sub_C Complex.I).pow _).ne_zero
  have hsecond : (X - C (-Complex.I) : Polynomial ℂ) ^
      p.rootMultiplicity (-Complex.I) ≠ 0 :=
    ((monic_X_sub_C (-Complex.I)).pow _).ne_zero
  calc
    p.rootMultiplicity Complex.I + p.rootMultiplicity (-Complex.I) =
        ((X - C Complex.I) ^ p.rootMultiplicity Complex.I *
          (X - C (-Complex.I)) ^
            p.rootMultiplicity (-Complex.I)).natDegree := by
      rw [natDegree_mul hfirst hsecond, natDegree_pow, natDegree_pow,
        natDegree_X_sub_C, natDegree_X_sub_C]
      simp
    _ = (C p.leadingCoeff *
        ((X - C Complex.I) ^ p.rootMultiplicity Complex.I *
          (X - C (-Complex.I)) ^
            p.rootMultiplicity (-Complex.I))).natDegree := by
      rw [natDegree_C_mul hlc]
    _ = p.natDegree := by
      have hfactor' : p = C p.leadingCoeff *
          ((X - C Complex.I) ^ p.rootMultiplicity Complex.I *
            (X - C (-Complex.I)) ^
              p.rootMultiplicity (-Complex.I)) := by
        simpa only [mul_assoc] using hfactor
      rw [← hfactor']

/-- A nonzero polynomial of degree `4r` whose only roots are `i` and `-i`,
with equal multiplicities at those roots, is a scalar multiple of
`(X²+1)^(2r)`. -/
theorem eq_leadingCoeff_mul_X_sq_add_one_pow_of_two_roots
    (p : _root_.Polynomial ℂ) (r : ℕ)
    (hp : p ≠ 0) (hdegree : p.natDegree = 4 * r)
    (hroots : ∀ z : ℂ, p.eval z = 0 → z = Complex.I ∨ z = -Complex.I)
    (hmultiplicity : p.rootMultiplicity Complex.I =
      p.rootMultiplicity (-Complex.I)) :
    p = C p.leadingCoeff * (X ^ 2 + C 1) ^ (2 * r) := by
  let a := p.rootMultiplicity Complex.I
  have hrootMultiset : p.roots =
      Multiset.replicate a Complex.I +
        Multiset.replicate a (-Complex.I) := by
    ext z
    by_cases hzI : z = Complex.I
    · subst z
      have hne : Complex.I ≠ -Complex.I := by
        intro h
        have := congrArg Complex.im h
        norm_num at this
      simp only [Multiset.count_add, Multiset.count_replicate,
        count_roots, a]
      simp [Ne.symm hne]
    · by_cases hzNegI : z = -Complex.I
      · subst z
        have hne : -Complex.I ≠ Complex.I := by
          intro h
          have := congrArg Complex.im h
          norm_num at this
        simp only [Multiset.count_add, Multiset.count_replicate,
          count_roots]
        simpa [Ne.symm hne, a] using hmultiplicity.symm
      · have hzNotRoot : z ∉ p.roots := by
          intro hz
          have hzero : p.eval z = 0 := (mem_roots hp).mp hz
          rcases hroots z hzero with h | h
          · exact hzI h
          · exact hzNegI h
        rw [Multiset.count_eq_zero.mpr hzNotRoot]
        simp only [Multiset.count_add, Multiset.count_replicate,
          if_neg (Ne.symm hzI), if_neg (Ne.symm hzNegI), add_zero]
  have ha : a = 2 * r := by
    have hcard : p.roots.card = p.natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    rw [hrootMultiset, Multiset.card_add,
      Multiset.card_replicate, Multiset.card_replicate, hdegree] at hcard
    omega
  have hsplits : p.Splits := IsAlgClosed.splits p
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
      hsplits.eq_prod_roots
    _ = C p.leadingCoeff *
        ((X - C Complex.I) ^ a *
          (X - C (-Complex.I)) ^ a) := by
      rw [hrootMultiset, Multiset.map_add, Multiset.prod_add,
        Multiset.map_replicate, Multiset.map_replicate,
        Multiset.prod_replicate, Multiset.prod_replicate]
    _ = C p.leadingCoeff *
        (((X - C Complex.I) * (X - C (-Complex.I))) ^ a) := by
      rw [mul_pow]
    _ = C p.leadingCoeff * (X ^ 2 + C 1) ^ a := by
      congr 2
      calc
        (X - C Complex.I) * (X - C (-Complex.I)) =
            X ^ 2 - C (Complex.I * Complex.I) := by
          rw [map_neg]
          rw [map_mul]
          ring
        _ = X ^ 2 + C 1 := by
          rw [Complex.I_mul_I]
          simp
    _ = C p.leadingCoeff * (X ^ 2 + C 1) ^ (2 * r) := by
      rw [ha]

end OnLeConjecture.Polynomial
