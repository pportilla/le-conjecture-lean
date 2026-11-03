/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicInvariantDecomposition
public import OnLeConjecture.DThree.WeightedOrderExpansion

/-!
# A homogeneous cyclic coefficient with no nonzero restricted root

Weighted scaling sends any zero with first coordinate nonzero to the curve
`(s²,sᵖ+c)`. Oddness of `p` allows a choice of square root for which the
required scaling exists. Consequently the polynomial is a power of its
first variable times a nonzero constant.
-/

public section

namespace OnLeConjecture.DTwo

open MvPolynomial

@[expose] noncomputable def cyclicOddRestriction (p : ℕ) (c : ℂ)
    (A : MvPolynomial (Fin 2) ℂ) : _root_.Polynomial ℂ :=
  aeval ![_root_.Polynomial.X ^ 2, _root_.Polynomial.X ^ p + _root_.Polynomial.C c] A

theorem cyclicOddRestriction_eval (p : ℕ) (c s : ℂ) (A : MvPolynomial (Fin 2) ℂ) :
    (cyclicOddRestriction p c A).eval s = eval ![s ^ 2, s ^ p + c] A := by
  change (_root_.Polynomial.aeval s) (aeval _ A) = aeval _ A
  rw [comp_aeval_apply]
  apply congrArg (fun f : Fin 2 → ℂ ↦ aeval f A)
  funext i
  fin_cases i <;> simp

/-- Every point with first coordinate nonzero has a nonzero weighted
scaling on the curve `(s²,sᵖ+c)`. -/
theorem exists_cyclicInvariant_scaling (p : ℕ) (hp : Odd p) (c : ℂ) (hc : c ≠ 0)
    (P Q : ℂ) (hP : P ≠ 0) :
    ∃ lambda s : ℂ, lambda ≠ 0 ∧ s ≠ 0 ∧
      (fun i : Fin 2 ↦ lambda ^ (![2, p] i) * (![P, Q] i)) = ![s ^ 2, s ^ p + c] := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq P (show 0 < 2 by omega)
  have hxzero : x ≠ 0 := by
    intro h
    exact hP (by simpa [h] using hx.symm)
  have hchoice : ∃ z : ℂ, z ^ 2 = P ∧ z ≠ 0 ∧ Q - z ^ p ≠ 0 := by
    by_cases h : Q - x ^ p = 0
    · refine ⟨-x, by simpa using hx, neg_ne_zero.mpr hxzero, ?_⟩
      rw [hp.neg_pow]
      intro hnegative
      have hxp : x ^ p = 0 := by
        have htwo : (2 : ℂ) * x ^ p = 0 := by linear_combination hnegative - h
        exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      exact pow_ne_zero _ hxzero hxp
    · exact ⟨x, hx, hxzero, h⟩
  obtain ⟨z, hz, hzne, hdiff⟩ := hchoice
  have hpzero : 0 < p := hp.pos
  obtain ⟨lambda, hlambdaPow⟩ := IsAlgClosed.exists_pow_nat_eq (c / (Q - z ^ p)) hpzero
  have hlambda : lambda ≠ 0 := by
    intro h
    have : c / (Q - z ^ p) = 0 := by simpa [h, hpzero.ne'] using hlambdaPow.symm
    exact div_ne_zero hc hdiff this
  have hscale : lambda ^ p * (Q - z ^ p) = c := by
    rw [hlambdaPow, div_mul_cancel₀ _ hdiff]
  refine ⟨lambda, lambda * z, hlambda, mul_ne_zero hlambda hzne, ?_⟩
  ext i
  fin_cases i
  · change lambda ^ 2 * P = (lambda * z) ^ 2
    rw [mul_pow, hz]
  · change lambda ^ p * Q = (lambda * z) ^ p + c
    rw [mul_pow]
    linear_combination hscale

/-- A zero off the first coordinate axis scales to a nonzero root of the
restricted polynomial. -/
theorem cyclicInvariant_eval_ne_zero_of_no_nonzero_restricted_root
    (p E : ℕ) (hp : Odd p) (c : ℂ) (hc : c ≠ 0)
    (A : MvPolynomial (Fin 2) ℂ) (hA : A.IsWeightedHomogeneous ![2, p] E)
    (hroots : ∀ s : ℂ, (cyclicOddRestriction p c A).eval s = 0 → s = 0)
    (P Q : ℂ) (hP : P ≠ 0) : eval ![P, Q] A ≠ 0 := by
  intro hzero
  obtain ⟨lambda, s, _, hs, hcoords⟩ := exists_cyclicInvariant_scaling p hp c hc P Q hP
  have hscaled := OnLeConjecture.DThree.eval_weighted_smul_of_isWeightedHomogeneous
    hA lambda (![P, Q] : Fin 2 → ℂ)
  rw [hcoords, hzero, mul_zero] at hscaled
  have hroot : (cyclicOddRestriction p c A).eval s = 0 := by
    rwa [cyclicOddRestriction_eval]
  exact hs (hroots s hroot)

/-- Restriction to `(s²,sᵖ+c)` cannot annihilate a nonzero weighted
homogeneous polynomial. -/
theorem cyclicOddRestriction_ne_zero (p E : ℕ) (hp : Odd p) (c : ℂ) (hc : c ≠ 0)
    (A : MvPolynomial (Fin 2) ℂ) (hA : A.IsWeightedHomogeneous ![2, p] E)
    (hAzero : A ≠ 0) : cyclicOddRestriction p c A ≠ 0 := by
  intro hzero
  apply hAzero
  apply MvPolynomial.funext_set (![({0}ᶜ : Set ℂ), Set.univ] : Fin 2 → Set ℂ)
  · intro i
    fin_cases i
    · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
    · exact Set.infinite_univ
  · intro z hz
    have hz0 : z 0 ≠ 0 := by simpa using hz 0 (Set.mem_univ _)
    obtain ⟨lambda, s, hlambda, _, hcoords⟩ :=
      exists_cyclicInvariant_scaling p hp c hc (z 0) (z 1) hz0
    have hscaled := OnLeConjecture.DThree.eval_weighted_smul_of_isWeightedHomogeneous
      hA lambda (![z 0, z 1] : Fin 2 → ℂ)
    rw [hcoords, ← cyclicOddRestriction_eval, hzero, _root_.Polynomial.eval_zero] at hscaled
    have hzvec : (![z 0, z 1] : Fin 2 → ℂ) = z := by ext i; fin_cases i <;> rfl
    rw [hzvec] at hscaled
    simpa using (mul_eq_zero.mp hscaled.symm).resolve_left (pow_ne_zero _ hlambda)

private theorem first_one_restriction_coeff (p E : ℕ)
    (A : MvPolynomial (Fin 2) ℂ) (hA : A.IsWeightedHomogeneous ![2, p] E)
    (d : Fin 2 →₀ ℕ) (hd : coeff d A ≠ 0) :
    (aeval ![1, _root_.Polynomial.X] A).coeff (d 1) = coeff d A := by
  classical
  have hmono (e : Fin 2 →₀ ℕ) (b : ℂ) :
      aeval ![1, _root_.Polynomial.X] (monomial e b) =
        _root_.Polynomial.C b * _root_.Polynomial.X ^ e 1 := by
    simp [monomial_fin_two]
  conv_lhs => rw [A.as_sum, map_sum, _root_.Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single d]
  · rw [hmono, _root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_X_pow]
    simp
  · intro e he hne
    have hsecond : e 1 ≠ d 1 := by
      intro hsame
      have hed : 2 * e 0 + p * e 1 = E := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using
          hA (MvPolynomial.mem_support_iff.mp he)
      have hdd : 2 * d 0 + p * d 1 = E := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hA hd
      have hfirst : e 0 = d 0 := by
        rw [hsame] at hed
        omega
      apply hne
      ext i
      fin_cases i
      · exact hfirst
      · exact hsame
    rw [hmono, _root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_X_pow]
    simp [Ne.symm hsecond]
  · intro hnot
    exact (hnot (MvPolynomial.mem_support_iff.mpr hd)).elim

/-- No nonzero restricted root forces a homogeneous polynomial to be a
single power of its first variable. -/
theorem cyclicInvariant_eq_first_power_of_no_nonzero_restricted_root
    (p E : ℕ) (hp : Odd p) (c : ℂ) (hc : c ≠ 0)
    (A : MvPolynomial (Fin 2) ℂ) (hA : A.IsWeightedHomogeneous ![2, p] E)
    (hroots : ∀ s : ℂ, (cyclicOddRestriction p c A).eval s = 0 → s = 0) :
    ∃ κ : ℂ, ∃ r : ℕ, κ ≠ 0 ∧ 2 * r = E ∧ A = C κ * X 0 ^ r := by
  classical
  let f : _root_.Polynomial ℂ := aeval ![1, _root_.Polynomial.X] A
  have hfeval (s : ℂ) : f.eval s = eval ![1, s] A := by
    change (_root_.Polynomial.aeval s) (aeval _ A) = aeval _ A
    rw [comp_aeval_apply]
    apply congrArg (fun g : Fin 2 → ℂ ↦ aeval g A)
    funext i
    fin_cases i <;> simp
  have hfnz (s : ℂ) : f.eval s ≠ 0 := by
    rw [hfeval]
    exact cyclicInvariant_eval_ne_zero_of_no_nonzero_restricted_root
      p E hp c hc A hA hroots 1 s one_ne_zero
  have hdegree : f.degree = 0 := by
    by_contra h
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_root f h
    exact hfnz s hs
  have hfC := _root_.Polynomial.eq_C_of_degree_eq_zero hdegree
  have hAzero : A ≠ 0 := by
    intro h
    exact hfnz 0 (by simp [f, h])
  have hsecond (d : Fin 2 →₀ ℕ) (hd : coeff d A ≠ 0) : d 1 = 0 := by
    have hcoeff := first_one_restriction_coeff p E A hA d hd
    change f.coeff (d 1) = coeff d A at hcoeff
    rw [hfC] at hcoeff
    by_contra hne
    simp only [_root_.Polynomial.coeff_C, if_neg hne] at hcoeff
    exact hd hcoeff.symm
  obtain ⟨d, hd⟩ : ∃ d, coeff d A ≠ 0 := by
    by_contra! hall
    apply hAzero
    ext e
    simpa using hall e
  have hdegreeD : 2 * d 0 = E := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm, hsecond d hd] using hA hd
  have heq : A = monomial d (coeff d A) := by
    ext e
    by_cases he : coeff e A = 0
    · have hed : e ≠ d := by intro h; exact hd (h ▸ he)
      simp [he, Ne.symm hed]
    · have hdegreeE : 2 * e 0 = E := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm, hsecond e he] using hA he
      have heq : e = d := by
        ext i
        fin_cases i
        · change e 0 = d 0
          omega
        · exact (hsecond e he).trans (hsecond d hd).symm
      simp [heq]
  refine ⟨coeff d A, d 0, hd, hdegreeD, ?_⟩
  simpa only [monomial_fin_two, hsecond d hd, pow_zero, mul_one] using heq

/-- In a rank two expression for `tΛ`, the root condition on the odd
coefficient forces positive even residual degree and the claimed pure odd
power after subtraction of the even coefficient. -/
theorem cyclicInvariant_pure_odd_remainder
    (p N₀ : ℕ) (hp : Odd p) (hN₀ : 0 < N₀) (c : ℂ) (hc : c ≠ 0)
    (Λ A B : MvPolynomial (Fin 2) ℂ)
    (hB : B.IsWeightedHomogeneous ![2, p] (N₀ + p - 1))
    (hdecomp : X 1 * Λ =
      cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B)
    (hroots : ∀ s : ℂ, (cyclicOddRestriction p c B).eval s = 0 → s = 0) :
    ∃ κ : ℂ, ∃ r q₀ : ℕ, κ ≠ 0 ∧ 0 < q₀ ∧ N₀ = 2 * q₀ ∧
      2 * r = N₀ + p - 1 ∧ B = C κ * X 0 ^ r ∧
      X 1 * Λ - cyclicInvariantBaseHom p c A = C κ * X 0 ^ (p + N₀) := by
  obtain ⟨κ, r, hκ, hr, hBeq⟩ :=
    cyclicInvariant_eq_first_power_of_no_nonzero_restricted_root
      p (N₀ + p - 1) hp c hc B hB hroots
  have hpzero : 0 < p := hp.pos
  obtain ⟨m, hm⟩ := hp
  have hN : N₀ = 2 * (N₀ / 2) := by omega
  refine ⟨κ, r, N₀ / 2, hκ, by omega, hN, hr, hBeq, ?_⟩
  rw [hdecomp, add_sub_cancel_left, hBeq]
  have hsubstitution : cyclicInvariantBaseHom p c (C κ * X 0 ^ r) =
      C κ * (X 0 ^ 2) ^ r := by simp [cyclicInvariantBaseHom]
  rw [hsubstitution, ← pow_mul]
  have hexponent : p + N₀ = 2 * r + 1 := by omega
  rw [hexponent, pow_succ]
  ring

end OnLeConjecture.DTwo
