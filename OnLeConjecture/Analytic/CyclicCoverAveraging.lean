/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Finite cyclic averaging

A finite sum of vectors with characters indexed by two residues has an
invariant part equal to its diagonal sum. This linear algebra statement
does not require independence of the summands.
-/

public section

open scoped BigOperators

namespace OnLeConjecture.Analytic.CyclicCover

/-- Orthogonality of the residue characters of a primitive root. -/
theorem character_sum (r : ℕ) (hr : 0 < r) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ r) (i j : Fin r) :
    (∑ k ∈ Finset.range r, (ζ ^ i.1 / ζ ^ j.1) ^ k) =
      if i = j then (r : ℂ) else 0 := by
  classical
  have hζzero : ζ ≠ 0 := hζ.ne_zero hr.ne'
  by_cases hij : i = j
  · subst j
    simp [div_self (pow_ne_zero _ hζzero)]
  · rw [if_neg hij]
    have hcharacter : ζ ^ i.1 / ζ ^ j.1 ≠ 1 := by
      intro h
      have hp : ζ ^ i.1 = ζ ^ j.1 :=
        (div_eq_one_iff_eq (pow_ne_zero _ hζzero)).mp h
      exact hij (Fin.ext (hζ.pow_inj i.isLt j.isLt hp))
    have hpower : (ζ ^ i.1 / ζ ^ j.1) ^ r = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul,
        Nat.mul_comm i.1 r, Nat.mul_comm j.1 r,
        pow_mul, pow_mul, hζ.pow_eq_one]
      simp
    have hsum := geom_sum_mul (ζ ^ i.1 / ζ ^ j.1) r
    rw [hpower, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right (sub_ne_zero.mpr hcharacter)

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

/-- Powers of an endomorphism act on a possibly zero eigenvector by the
corresponding powers of its eigenvalue. -/
theorem end_pow_apply_of_eigenrelation
    (T : Module.End ℂ A) (q : A) (eigenvalue : ℂ)
    (hq : T q = eigenvalue • q) (k : ℕ) :
    (T ^ k) q = eigenvalue ^ k • q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hq,
        smul_smul, pow_succ]

/-- Summing powers of an endomorphism on an eigenvector sums its character.
-/
theorem sum_end_pow_apply_of_eigenrelation
    (T : Module.End ℂ A) (q : A) (eigenvalue : ℂ)
    (hq : T q = eigenvalue • q) (r : ℕ) :
    (∑ k ∈ Finset.range r, T ^ k) q =
      (∑ k ∈ Finset.range r, eigenvalue ^ k) • q := by
  simp only [LinearMap.sum_apply]
  simp_rw [end_pow_apply_of_eigenrelation T q eigenvalue hq]
  exact Finset.sum_smul.symm

/-- Averaging an invariant finite character expansion leaves exactly its
diagonal residue terms. -/
theorem invariant_sum_eq_diagonal
    (r : ℕ) (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (T : Module.End ℂ A) (q : Fin r → Fin r → A) (f : A)
    (hdecomposition : f = ∑ i, ∑ j, q i j)
    (hcharacter : ∀ i j, T (q i j) = (ζ ^ i.1 / ζ ^ j.1) • q i j)
    (hinvariant : T f = f) :
    f = ∑ i, q i i := by
  classical
  let S : Module.End ℂ A := ∑ k ∈ Finset.range r, T ^ k
  have hSf : S f = (r : ℂ) • f := by
    simpa [S] using sum_end_pow_apply_of_eigenrelation T f 1
      (by simpa using hinvariant) r
  have hSq (i j : Fin r) :
      S (q i j) = if i = j then (r : ℂ) • q i j else 0 := by
    rw [show S (q i j) =
      (∑ k ∈ Finset.range r, (ζ ^ i.1 / ζ ^ j.1) ^ k) • q i j from
        sum_end_pow_apply_of_eigenrelation T (q i j)
          (ζ ^ i.1 / ζ ^ j.1) (hcharacter i j) r,
      character_sum r hr ζ hζ i j]
    split_ifs <;> simp
  have heq : (r : ℂ) • f = (r : ℂ) • ∑ i, q i i := by
    calc
      (r : ℂ) • f = S f := hSf.symm
      _ = ∑ i, ∑ j, S (q i j) := by rw [hdecomposition, map_sum]; simp_rw [map_sum]
      _ = ∑ i, (r : ℂ) • q i i := by simp_rw [hSq]; simp
      _ = (r : ℂ) • ∑ i, q i i := Finset.smul_sum.symm
  have hrzero : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hscaled := congrArg (fun x : A => (r : ℂ)⁻¹ • x) heq
  simpa only [smul_smul, inv_mul_cancel₀ hrzero, one_smul] using hscaled

end OnLeConjecture.Analytic.CyclicCover
