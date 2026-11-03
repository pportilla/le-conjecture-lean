/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.WeightedCubicInitialForm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Residue decomposition of weighted forms

A polynomial homogeneous for source weights `(a,1)` has a unique common
residue for the exponent of the second variable modulo `a`. Removing that
power leaves the substitution `t = y^a` of an ordinary homogeneous form.
-/

public section

namespace OnLeConjecture.DThree

/-- Substitute `x` for the first variable and `y^a` for the second variable
of an ordinary binary form. -/
@[expose]
noncomputable def weightedPowerSubstitutionForm (a : ℕ) :
    Form ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval fun i ↦
    if i = 0 then formX else formT ^ a

@[simp]
theorem weightedPowerSubstitutionForm_x (a : ℕ) :
    weightedPowerSubstitutionForm a formX = formX := by
  simp [weightedPowerSubstitutionForm, formX]

@[simp]
theorem weightedPowerSubstitutionForm_t (a : ℕ) :
    weightedPowerSubstitutionForm a formT = formT ^ a := by
  simp [weightedPowerSubstitutionForm, formT]

/-- Substitution multiplies ordinary homogeneous degree by the first source
weight. -/
theorem weightedPowerSubstitutionForm_isWeightedHomogeneous
    (a N : ℕ) (H : Form ℂ) (hH : H.IsHomogeneous N) :
    (weightedPowerSubstitutionForm a H).IsWeightedHomogeneous
      ![a, 1] (a * N) := by
  have hx : (formX : Form ℂ).IsWeightedHomogeneous ![a, 1] a :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
  have ht : (formT : Form ℂ).IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  induction hH using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      rw [map_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ ![a, 1] (a * N)
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact ihp.add ihq
  | monomial d c hd =>
      rw [weightedPowerSubstitutionForm, MvPolynomial.aeval_def,
        MvPolynomial.eval₂_monomial]
      have hproduct : MvPolynomial.IsWeightedHomogeneous ![a, 1]
          (∏ i ∈ d.support,
            (if i = 0 then (formX : Form ℂ) else formT ^ a) ^ d i)
          (∑ i ∈ d.support, a * d i) := by
        apply MvPolynomial.IsWeightedHomogeneous.prod
        intro i hi
        fin_cases i
        · simpa [Nat.mul_comm] using hx.pow (d 0)
        · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            (ht.pow a).pow (d 1)
      have hdegree : ∑ i ∈ d.support, a * d i = a * N := by
        rw [← Finset.mul_sum]
        congr 1
        simpa [Finsupp.weight_apply, Finsupp.sum] using hd
      rw [hdegree] at hproduct
      exact hproduct.C_mul c

/-- Evaluation after weighted power substitution replaces the second value
by its `a`th power. -/
theorem eval_weightedPowerSubstitutionForm
    (a : ℕ) (H : Form ℂ) (z : ℂ × ℂ) :
    MvPolynomial.eval
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
        (weightedPowerSubstitutionForm a H) =
      MvPolynomial.eval
        ![z.1, z.2 ^ a] H := by
  let left : Form ℂ →ₐ[ℂ] ℂ :=
    (MvPolynomial.aeval
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)).comp
        (weightedPowerSubstitutionForm a)
  let right : Form ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval ![z.1, z.2 ^ a]
  have hequality : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    all_goals simp [left, right, weightedPowerSubstitutionForm, formX, formT]
  simpa [left, right] using AlgHom.congr_fun hequality H

private theorem exists_residue_decomposition_monomial
    (a D : ℕ) (ha : 0 < a) (d : Fin 2 →₀ ℕ) (c : ℂ)
    (hd : Finsupp.weight ![a, 1] d = D) :
    ∃ H : Form ℂ, H.IsHomogeneous (D / a) ∧
      MvPolynomial.monomial d c =
        formT ^ (D % a) * weightedPowerSubstitutionForm a H := by
  have hdegree : a * d 0 + d 1 = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
  have hdiv : D / a = d 0 + d 1 / a := by
    rw [← hdegree, Nat.mul_add_div ha]
  have hmod : D % a = d 1 % a := by
    rw [← hdegree, Nat.mul_add_mod]
  let H : Form ℂ :=
    MvPolynomial.C c * formX ^ d 0 * formT ^ (d 1 / a)
  refine ⟨H, ?_, ?_⟩
  · have hx :=
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow (d 0)
    have ht :=
      (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow (d 1 / a)
    have hH := (hx.mul ht).C_mul c
    rw [hdiv]
    simpa only [H, formX, formT, nsmul_eq_mul, one_mul, mul_assoc] using hH
  · have hdF : d = Finsupp.single (0 : Fin 2) (d 0) +
        Finsupp.single (1 : Fin 2) (d 1) := by
      ext i
      fin_cases i
      all_goals simp
    have hyExponent : D % a + a * (d 1 / a) = d 1 := by
      rw [hmod, Nat.mod_add_div]
    rw [hdF]
    simp only [H, weightedPowerSubstitutionForm, MvPolynomial.aeval_def,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
      formX, formT, if_pos,
      if_neg (by norm_num : (1 : Fin 2) ≠ 0),
      MvPolynomial.algebraMap_eq]
    rw [← pow_mul]
    have hright :
        MvPolynomial.X (1 : Fin 2) ^ (D % a) *
            (MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
              MvPolynomial.X (1 : Fin 2) ^ (a * (d 1 / a))) =
          MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
            MvPolynomial.X (1 : Fin 2) ^ d 1 := by
      calc
        MvPolynomial.X (1 : Fin 2) ^ (D % a) *
              (MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
                MvPolynomial.X (1 : Fin 2) ^ (a * (d 1 / a))) =
            MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
              (MvPolynomial.X (1 : Fin 2) ^ (D % a) *
                MvPolynomial.X (1 : Fin 2) ^ (a * (d 1 / a))) := by ring
        _ = MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
              MvPolynomial.X (1 : Fin 2) ^
                (D % a + a * (d 1 / a)) := by
            rw [pow_add]
        _ = MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
              MvPolynomial.X (1 : Fin 2) ^ d 1 := by rw [hyExponent]
    rw [hright]
    rw [MvPolynomial.C_mul_X_pow_eq_monomial,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
    simp

/-- Every weighted homogeneous binary form is a power of the second variable
times the substitution of an ordinary homogeneous binary form. -/
theorem exists_weightedResidueDecomposition
    (a D : ℕ) (ha : 0 < a) (P : Form ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) :
    ∃ H : Form ℂ, H.IsHomogeneous (D / a) ∧
      P = formT ^ (D % a) * weightedPowerSubstitutionForm a H := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      exact ⟨0,
        MvPolynomial.isHomogeneous_zero (Fin 2) ℂ (D / a), by simp⟩
  | add p q hp hq ihp ihq =>
      obtain ⟨Pzero, hPzero, hpzero⟩ := ihp
      obtain ⟨Qzero, hQzero, hqzero⟩ := ihq
      refine ⟨Pzero + Qzero, hPzero.add hQzero, ?_⟩
      rw [map_add, hpzero, hqzero]
      ring
  | monomial d c hd =>
      exact exists_residue_decomposition_monomial a D ha d c hd

/-- The residue exponent in the weighted decomposition is less than the
first source weight. -/
theorem weightedResidue_lt
    (a D : ℕ) (ha : 0 < a) :
    D % a < a :=
  Nat.mod_lt D ha

/-- The weighted degree is reconstructed from its quotient and residue. -/
theorem weightedDegree_eq_residue_add_mul_quotient
    (a D : ℕ) :
    D = D % a + a * (D / a) := by
  exact (Nat.mod_add_div D a).symm

/-- A nonzero weighted form has a nonzero ordinary form in every residue
decomposition. -/
theorem weightedResidueDecomposition_ne_zero
    {a D : ℕ} {P H : Form ℂ}
    (hP : P ≠ 0)
    (hdecomposition :
      P = formT ^ (D % a) * weightedPowerSubstitutionForm a H) :
    H ≠ 0 := by
  intro hH
  subst H
  apply hP
  simpa using hdecomposition

end OnLeConjecture.DThree
