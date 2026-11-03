/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Finite resultant equations for common polynomial roots

A monic polynomial and finitely many further polynomials have a common root
exactly when finitely many fixed linear combinations have zero resultant
with the monic polynomial. The coefficients of the combinations are powers
of distinct natural numbers. Their number depends only on the monic degree
and the number of additional polynomials.
-/

@[expose] public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial
open scoped BigOperators

/-- The linear combination with coefficients `1,t,…,t^(r-1)`. -/
noncomputable def momentCombination {r : ℕ} (R : Fin r → ℂ[X]) (t : ℂ) : ℂ[X] :=
  ∑ j : Fin r, C (t ^ (j : ℕ)) * R j

/-- The values at one proposed root, regarded as coefficients of a
polynomial in the combination parameter. -/
noncomputable def valueCoefficientPolynomial {r : ℕ} (R : Fin r → ℂ[X]) (z : ℂ) : ℂ[X] :=
  ∑ j : Fin r, monomial (j : ℕ) ((R j).eval z)

theorem eval_valueCoefficientPolynomial {r : ℕ} (R : Fin r → ℂ[X]) (z t : ℂ) :
    (valueCoefficientPolynomial R z).eval t = (momentCombination R t).eval z := by
  simp only [valueCoefficientPolynomial, momentCombination, eval_finsetSum,
    eval_monomial, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem coeff_valueCoefficientPolynomial {r : ℕ} (R : Fin r → ℂ[X]) (z : ℂ)
    (j : Fin r) :
    (valueCoefficientPolynomial R z).coeff j = (R j).eval z := by
  classical
  simp [valueCoefficientPolynomial, coeff_monomial, Fin.val_inj]

theorem natDegree_valueCoefficientPolynomial_le {r : ℕ} (R : Fin r → ℂ[X]) (z : ℂ) :
    (valueCoefficientPolynomial R z).natDegree ≤ r := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt j.isLt)

theorem natDegree_momentCombination_le {r e : ℕ} (R : Fin r → ℂ[X])
    (hR : ∀ j, (R j).natDegree ≤ e) (t : ℂ) :
    (momentCombination R t).natDegree ≤ e := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans (hR j)

/-- With a monic first polynomial, fixed resultant dimensions detect
common roots even when the second polynomial drops degree or is zero. -/
theorem fixed_resultant_eq_zero_iff_common_root
    (P Q : ℂ[X]) (hP : P.Monic) (e : ℕ) (hQ : Q.natDegree ≤ e) :
    resultant P Q P.natDegree e = 0 ↔ ∃ z : ℂ, P.eval z = 0 ∧ Q.eval z = 0 := by
  rw [resultant_eq_prod_eval P Q e hQ (IsAlgClosed.splits P), hP.leadingCoeff,
    one_pow, one_mul, Multiset.prod_eq_zero_iff]
  simp only [Multiset.mem_map, mem_roots hP.ne_zero, IsRoot.def]

/-- Common roots are characterized by a finite list of resultant equations.
The prescribed list works for every family satisfying the degree bound. -/
theorem exists_common_root_iff_finite_resultants_vanish
    {r e : ℕ} (P : ℂ[X]) (hP : P.Monic) (R : Fin r → ℂ[X])
    (hR : ∀ j, (R j).natDegree ≤ e) :
    (∃ z : ℂ, P.eval z = 0 ∧ ∀ j, (R j).eval z = 0) ↔
      ∀ k : Fin (P.natDegree * r + 1),
        resultant P (momentCombination R (k : ℕ)) P.natDegree e = 0 := by
  classical
  constructor
  · rintro ⟨z, hzP, hzR⟩ k
    apply (fixed_resultant_eq_zero_iff_common_root _ _ hP e
      (natDegree_momentCombination_le R hR _)).mpr
    refine ⟨z, hzP, ?_⟩
    simp only [momentCombination, eval_finsetSum, eval_mul, eval_C, hzR, mul_zero,
      Finset.sum_const_zero]
  · intro hresultants
    by_contra hnone
    have havoid (z : ℂ) (hz : z ∈ P.roots.toFinset) :
        valueCoefficientPolynomial R z ≠ 0 := by
      intro hzero
      apply hnone
      refine ⟨z, (mem_roots hP.ne_zero).mp (Multiset.mem_toFinset.mp hz), ?_⟩
      intro j
      have hc := congrArg (fun Q : ℂ[X] => Q.coeff j) hzero
      simpa only [coeff_valueCoefficientPolynomial, coeff_zero] using hc
    let Q : ℂ[X] := ∏ z ∈ P.roots.toFinset, valueCoefficientPolynomial R z
    have hQne : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr havoid
    have hQdegree : Q.natDegree ≤ P.natDegree * r := by
      calc
        Q.natDegree ≤ ∑ z ∈ P.roots.toFinset,
            (valueCoefficientPolynomial R z).natDegree := natDegree_prod_le _ _
        _ ≤ ∑ _z ∈ P.roots.toFinset, r :=
          Finset.sum_le_sum fun z _ => natDegree_valueCoefficientPolynomial_le R z
        _ = P.roots.toFinset.card * r := by simp
        _ ≤ P.natDegree * r := Nat.mul_le_mul_right r
          ((Multiset.toFinset_card_le _).trans (card_roots' P))
    have heval (k : Fin (P.natDegree * r + 1)) : Q.eval ((k : ℕ) : ℂ) = 0 := by
      obtain ⟨z, hzP, hzR⟩ :=
        (fixed_resultant_eq_zero_iff_common_root _ _ hP e
          (natDegree_momentCombination_le R hR _)).mp (hresultants k)
      rw [show Q.eval ((k : ℕ) : ℂ) = ∏ z ∈ P.roots.toFinset,
          (valueCoefficientPolynomial R z).eval ((k : ℕ) : ℂ) by
        simp only [Q, eval_prod]]
      apply Finset.prod_eq_zero (Multiset.mem_toFinset.mpr ((mem_roots hP.ne_zero).mpr hzP))
      rwa [eval_valueCoefficientPolynomial]
    apply hQne
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun k : Fin (P.natDegree * r + 1) => ((k : ℕ) : ℂ))
    · intro a b hab
      exact Fin.ext (Nat.cast_injective hab)
    · exact heval
    · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hQdegree

end OnLeConjecture.Polynomial
