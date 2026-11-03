/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicReducedPowers

/-!
# Factoring the first-exponent residue of a weighted polynomial

A polynomial homogeneous for weights `(1,p)` has all first exponents
congruent to its degree modulo `p`. Factoring this residue expresses the
remaining polynomial in `xᵖ` and the second variable.
-/

public section

namespace OnLeConjecture.DTwo

open MvPolynomial

/-- The first-exponent residue factor follows from polynomial homogeneity. -/
theorem exists_weighted_residue_factor
    (p d : ℕ) (L : MvPolynomial (Fin 2) ℂ)
    (hL : L.IsWeightedHomogeneous ![1, p] d) :
    ∃ M : MvPolynomial (Fin 2) ℂ,
      L = X 0 ^ (d % p) * aeval ![X 0 ^ p, X 1] M := by
  induction hL using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add P Q hP hQ ihP ihQ =>
      obtain ⟨M, hM⟩ := ihP
      obtain ⟨N, hN⟩ := ihQ
      exact ⟨M + N, by rw [map_add, mul_add, ← hM, ← hN]⟩
  | monomial e c he =>
      have hweight : e 0 + p * e 1 = d := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using he
      have hmod : e 0 % p = d % p := by
        simpa only [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using
          congrArg (fun n : ℕ ↦ n % p) hweight
      have hexponent : d % p + p * (e 0 / p) = e 0 := by
        rw [← hmod]
        exact Nat.mod_add_div (e 0) p
      let f : Fin 2 →₀ ℕ := Finsupp.single 0 (e 0 / p) + Finsupp.single 1 (e 1)
      refine ⟨monomial f c, ?_⟩
      simp only [MvPolynomial.monomial_fin_two, map_mul, map_pow, aeval_C, aeval_X]
      simp only [f, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_one, ← pow_mul]
      calc
        (C c : MvPolynomial (Fin 2) ℂ) * X 0 ^ e 0 * X 1 ^ e 1 =
            C c * X 0 ^ (d % p + p * (e 0 / p)) * X 1 ^ e 1 := by
          rw [hexponent]
        _ = X 0 ^ (d % p) * (C c * X 0 ^ (p * (e 0 / p)) * X 1 ^ e 1) := by
          rw [pow_add]
          ring

theorem weighted_residue_factor_eval
    (p r : ℕ) (L M : MvPolynomial (Fin 2) ℂ)
    (hfactor : L = X 0 ^ r * aeval ![X 0 ^ p, X 1] M) (x t : ℂ) :
    eval ![x, t] L = x ^ r * eval ![x ^ p, t] M := by
  rw [hfactor, map_mul, map_pow, eval_X]
  congr 1
  change aeval ![x, t] (aeval _ M) = aeval _ M
  rw [comp_aeval_apply]
  apply congrArg (fun f : Fin 2 → ℂ ↦ aeval f M)
  ext index
  fin_cases index <;> simp

/-- The polynomial in `Yᵏ` remaining in the invariant third difference. -/
@[expose] noncomputable def cyclicResidueDifferencePolynomial
    (r : ℕ) (c : ℂ) (M : MvPolynomial (Fin 2) ℂ) : _root_.Polynomial ℂ :=
  let G : _root_.Polynomial ℂ := _root_.Polynomial.C (c / 2) * (_root_.Polynomial.X - 1)
  aeval ![G, 1] M - _root_.Polynomial.C ((-1 : ℂ) ^ r) * _root_.Polynomial.X *
    aeval ![-G, _root_.Polynomial.X] M

theorem cyclicResidueDifferencePolynomial_eval
    (k p r : ℕ) (hp : Odd p) (c x y : ℂ)
    (L M : MvPolynomial (Fin 2) ℂ)
    (hfactor : L = X 0 ^ r * aeval ![X 0 ^ p, X 1] M)
    (hcurve : x ^ p = c / 2 * (y ^ k - 1)) :
    eval ![x, 1] L - y ^ k * eval ![-x, y ^ k] L =
      x ^ r * (cyclicResidueDifferencePolynomial r c M).eval (y ^ k) := by
  have heval (A B : _root_.Polynomial ℂ) (z : ℂ) :
      (aeval ![A, B] M).eval z = eval ![A.eval z, B.eval z] M := by
    change (_root_.Polynomial.aeval z) (aeval _ M) = aeval _ M
    rw [comp_aeval_apply]
    apply congrArg (fun f : Fin 2 → ℂ ↦ aeval f M)
    ext index
    fin_cases index <;> simp
  rw [weighted_residue_factor_eval p r L M hfactor,
    weighted_residue_factor_eval p r L M hfactor, hp.neg_pow]
  simp only [cyclicResidueDifferencePolynomial, _root_.Polynomial.eval_sub,
    _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, _root_.Polynomial.eval_X,
    heval, _root_.Polynomial.eval_one, _root_.Polynomial.eval_sub,
    _root_.Polynomial.eval_neg, ← hcurve]
  rw [neg_pow]
  ring

end OnLeConjecture.DTwo
