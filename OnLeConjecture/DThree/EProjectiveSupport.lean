/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EJacobianDescent
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Projective support of the residual polynomial for the `E` pair

This file proves the binary form argument in the invariant branch of the
degree three case.  A nonzero homogeneous binary form over `C` whose
projective zeros lie on the diagonal is a scalar multiple of a power of the
diagonal equation.  Symmetry makes the exponent even.  Divisibility by the
square of the diagonal makes the half exponent positive.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial.Bivariate

/-- A polynomial in the residual coordinates is homogeneous of degree `n`
when its image in the two variable presentation is homogeneous of degree
`n`. -/
def EPairIsHomogeneous (theta : EPairRing ℂ) (n : ℕ) : Prop :=
  (eIteratedToForm theta).IsHomogeneous n

theorem ePairIsHomogeneous_iff
    (theta : EPairRing ℂ) (n : ℕ) :
    EPairIsHomogeneous theta n ↔
      (eIteratedToForm theta).IsHomogeneous n :=
  Iff.rfl

/-- Every projective zero of `theta` lies on the diagonal. -/
def EPairProjectiveZerosOnDiagonal (theta : EPairRing ℂ) : Prop :=
  ∀ x X : ℂ, x ≠ 0 ∨ X ≠ 0 →
    MvPolynomial.eval ![x, X] (eIteratedToForm theta) = 0 → x = X

/-- Scalar evaluation in the iterated presentation agrees with evaluation
after transport to a two variable polynomial. -/
theorem ePairPointEval_eq_eval_iteratedToForm
    (theta : EPairRing ℂ) (x y : ℂ) :
    ePairPointEval ℂ x y theta =
      MvPolynomial.eval ![x, y] (eIteratedToForm theta) := by
  let transported : EPairRing ℂ →ₐ[ℂ] ℂ :=
    (MvPolynomial.aeval ![x, y]).comp eIteratedToForm
  have heq : ePairPointEval ℂ x y = transported := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      change ePairPointEval ℂ x y (C X) = transported (C X)
      dsimp only [transported, AlgHom.comp_apply]
      rw [eIteratedToForm_innerX,
        show (C X : EPairRing ℂ) = ePairFirst ℂ by rfl,
        ePairPointEval_first]
      simp [formX]
    · change ePairPointEval ℂ x y X = transported X
      dsimp only [transported, AlgHom.comp_apply]
      rw [eIteratedToForm_outerX,
        show (X : EPairRing ℂ) = ePairSecond ℂ by rfl,
        ePairPointEval_second]
      simp [formT]
  exact (AlgHom.congr_fun heq theta).trans rfl

/-- The zero polynomial does not have all projective zeros on the
diagonal. -/
theorem not_ePairProjectiveZerosOnDiagonal_zero :
    ¬ EPairProjectiveZerosOnDiagonal (0 : EPairRing ℂ) := by
  intro hsupport
  have hone := hsupport 1 0 (Or.inl one_ne_zero) (by simp)
  norm_num at hone

/-- Dehomogenization in the chart where the second coordinate is one. -/
noncomputable def ePairDehomogenize (theta : EPairRing ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval ![X, 1] (eIteratedToForm theta)

theorem ePairDehomogenize_eval (theta : EPairRing ℂ) (z : ℂ) :
    (ePairDehomogenize theta).eval z =
      MvPolynomial.eval ![z, 1] (eIteratedToForm theta) := by
  rw [ePairDehomogenize, MvPolynomial.aeval_def,
    MvPolynomial.polynomial_eval_eval₂]
  have hcomp :
      (Polynomial.evalRingHom z).comp (algebraMap ℂ (Polynomial ℂ)) =
        RingHom.id ℂ := by
    ext a
    simp
  rw [hcomp, MvPolynomial.eval₂_id]
  congr
  funext i
  fin_cases i <;> simp

/-- The chart polynomial is obtained from `finSuccEquiv` by setting its
remaining coefficient variable equal to one. -/
theorem ePairDehomogenize_eq_map_finSuccEquiv
    (theta : EPairRing ℂ) :
    ePairDehomogenize theta =
      Polynomial.map (MvPolynomial.eval fun _ : Fin 1 ↦ (1 : ℂ))
        (MvPolynomial.finSuccEquiv ℂ 1 (eIteratedToForm theta)) := by
  let left : Form ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval ![X, 1]
  let evaluation : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval fun _ ↦ (1 : ℂ)
  let right : Form ℂ →ₐ[ℂ] Polynomial ℂ :=
    (Polynomial.mapAlgHom evaluation).comp
      (MvPolynomial.finSuccEquiv ℂ 1).toAlgHom
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [left, right, Polynomial.coe_mapAlgHom,
        MvPolynomial.finSuccEquiv_X_zero]
    · simp only [left, right, MvPolynomial.aeval_X,
        AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
        Polynomial.coe_mapAlgHom]
      change ![X, 1] j.succ =
        Polynomial.map evaluation.toRingHom
          (MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X j.succ))
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
      fin_cases j
      simp [evaluation]
  change left (eIteratedToForm theta) =
    right (eIteratedToForm theta)
  exact AlgHom.congr_fun heq (eIteratedToForm theta)

/-- The degree of a chart polynomial does not exceed the degree of its
homogeneous binary form. -/
theorem ePairDehomogenize_natDegree_le
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n) :
    (ePairDehomogenize theta).natDegree ≤ n := by
  rw [ePairDehomogenize_eq_map_finSuccEquiv]
  calc
    (Polynomial.map (MvPolynomial.eval fun _ : Fin 1 ↦ (1 : ℂ))
        (MvPolynomial.finSuccEquiv ℂ 1
          (eIteratedToForm theta))).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1
          (eIteratedToForm theta)).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 0 (eIteratedToForm theta) :=
      MvPolynomial.natDegree_finSuccEquiv _
    _ ≤ MvPolynomial.totalDegree (eIteratedToForm theta) :=
      MvPolynomial.degreeOf_le_totalDegree _ _
    _ ≤ n := hhomogeneous.totalDegree_le

/-- Homogenizing the chart polynomial recovers the original binary form. -/
theorem ePair_homogenize_dehomogenize
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n) :
    (ePairDehomogenize theta).homogenize n = eIteratedToForm theta := by
  exact Polynomial.homogenize_eq_of_isHomogeneous hhomogeneous rfl

private theorem eval_homogenize_one_zero
    (p : Polynomial ℂ) (n : ℕ) :
    MvPolynomial.eval ![(1 : ℂ), 0] (p.homogenize n) = p.coeff n := by
  simp only [Polynomial.homogenize, map_sum,
    MvPolynomial.eval_monomial]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = n := Finset.mem_antidiagonal.mp hab
    have hb : b ≠ 0 := by
      intro hb
      apply hne
      subst b
      simp only [add_zero] at hsum
      exact Prod.ext hsum rfl
    simp [hb]
  · simp

/-- The chart has full degree because a degree drop would produce the
projective zero `[1:0]`. -/
theorem ePairDehomogenize_natDegree_eq
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n)
    (hsupport : EPairProjectiveZerosOnDiagonal theta) :
    (ePairDehomogenize theta).natDegree = n := by
  apply le_antisymm (ePairDehomogenize_natDegree_le hhomogeneous)
  by_contra hle
  have hlt : (ePairDehomogenize theta).natDegree < n :=
    Nat.lt_of_not_ge hle
  have hcoeff : (ePairDehomogenize theta).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  have heval :
      MvPolynomial.eval ![(1 : ℂ), 0] (eIteratedToForm theta) = 0 := by
    rw [← ePair_homogenize_dehomogenize hhomogeneous,
      eval_homogenize_one_zero, hcoeff]
  have hone := hsupport 1 0 (Or.inl one_ne_zero) heval
  norm_num at hone

/-- Every root of the chart polynomial is the diagonal point one. -/
theorem ePairDehomogenize_root_eq_one
    {theta : EPairRing ℂ}
    (hsupport : EPairProjectiveZerosOnDiagonal theta)
    {z : ℂ} (hz : (ePairDehomogenize theta).eval z = 0) :
    z = 1 := by
  apply hsupport z 1 (Or.inr one_ne_zero)
  rwa [← ePairDehomogenize_eval]

private theorem polynomial_eq_leadingCoeff_mul_X_sub_one_pow
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (hroot : ∀ z : ℂ, p.eval z = 0 → z = 1) :
    p = C p.leadingCoeff * (X - C 1) ^ p.natDegree := by
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroots : p.roots = Multiset.replicate p.natDegree 1 := by
    apply Multiset.eq_replicate.mpr
    constructor
    · exact IsAlgClosed.card_roots_eq_natDegree
    · intro z hz
      apply hroot z
      exact (Polynomial.mem_roots hp).mp hz
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
      hsplits.eq_prod_roots
    _ = C p.leadingCoeff * (X - C 1) ^ p.natDegree := by
      rw [hroots, Multiset.map_replicate, Multiset.prod_replicate]

/-- A nonzero homogeneous binary form whose projective zeros lie on the
diagonal is a scalar multiple of a power of the diagonal equation. -/
theorem ePair_eq_scalar_mul_first_sub_second_pow_of_projective_support
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n)
    (hsupport : EPairProjectiveZerosOnDiagonal theta) :
    ∃ coefficient : ℂ, coefficient ≠ 0 ∧
      theta = algebraMap ℂ (EPairRing ℂ) coefficient *
        (ePairFirst ℂ - ePairSecond ℂ) ^ n := by
  let p := ePairDehomogenize theta
  have hp : p ≠ 0 := by
    intro hpzero
    have hzero : p.eval 0 = 0 := by rw [hpzero, Polynomial.eval_zero]
    have := ePairDehomogenize_root_eq_one hsupport hzero
    norm_num at this
  have hdegree : p.natDegree = n :=
    ePairDehomogenize_natDegree_eq hhomogeneous hsupport
  have hpFactor :
      p = C p.leadingCoeff * (X - C 1) ^ n := by
    rw [← hdegree]
    exact polynomial_eq_leadingCoeff_mul_X_sub_one_pow p hp
      (fun _ hz ↦ ePairDehomogenize_root_eq_one hsupport hz)
  let diagonalForm : Form ℂ :=
    MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2)
  have hdiagonalHomogeneous : diagonalForm.IsHomogeneous 1 := by
    exact (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).sub
      (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))
  have hpowerHomogeneous :
      (MvPolynomial.C p.leadingCoeff * diagonalForm ^ n).IsHomogeneous n := by
    simpa only [one_mul] using
      (hdiagonalHomogeneous.pow n).C_mul p.leadingCoeff
  have hdehomogenizePower :
      MvPolynomial.aeval ![X, 1]
          (MvPolynomial.C p.leadingCoeff * diagonalForm ^ n) = p := by
    calc
      MvPolynomial.aeval ![X, 1]
          (MvPolynomial.C p.leadingCoeff * diagonalForm ^ n) =
          C p.leadingCoeff * (X - C 1) ^ n := by
        simp [diagonalForm]
      _ = p := hpFactor.symm
  have hformPower :
      p.homogenize n =
        MvPolynomial.C p.leadingCoeff * diagonalForm ^ n :=
    Polynomial.homogenize_eq_of_isHomogeneous
      hpowerHomogeneous hdehomogenizePower
  have hthetaForm :
      eIteratedToForm theta =
        MvPolynomial.C p.leadingCoeff * diagonalForm ^ n := by
    rw [← ePair_homogenize_dehomogenize hhomogeneous, hformPower]
  refine ⟨p.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hp, ?_⟩
  have htransport := congrArg eFormToIterated hthetaForm
  have hback : eFormToIterated (eIteratedToForm theta) = theta := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eFormToIterated_comp_iteratedToForm theta
  rw [hback] at htransport
  have hconstant :
      eFormToIterated (MvPolynomial.C p.leadingCoeff) =
        algebraMap ℂ (EPairRing ℂ) p.leadingCoeff :=
    eFormToIterated.commutes p.leadingCoeff
  simp only [map_mul, map_pow, map_sub, diagonalForm] at htransport
  rw [hconstant,
    show MvPolynomial.X (0 : Fin 2) = (formX : Form ℂ) by rfl,
    show MvPolynomial.X (1 : Fin 2) = (formT : Form ℂ) by rfl,
    eFormToIterated_x, eFormToIterated_t] at htransport
  simpa only [ePairFirst, ePairSecond] using htransport

/-- Symmetry forces the exponent in the preceding diagonal power to be
even. -/
theorem ePair_exponent_even_of_projective_support
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n)
    (hsymmetric : Polynomial.Bivariate.swap theta = theta)
    (hsupport : EPairProjectiveZerosOnDiagonal theta) :
    Even n := by
  obtain ⟨coefficient, hcoefficient, hpower⟩ :=
    ePair_eq_scalar_mul_first_sub_second_pow_of_projective_support
      hhomogeneous hsupport
  have hswap := congrArg (Polynomial.aevalAeval (0 : ℂ) 1) hsymmetric
  rw [Polynomial.Bivariate.aevalAeval_swap, hpower] at hswap
  simp only [map_mul, map_pow, map_sub,
    (Polynomial.aevalAeval (0 : ℂ) 1).commutes,
    (Polynomial.aevalAeval (1 : ℂ) 0).commutes,
    ePairFirst, ePairSecond, Polynomial.aevalAeval_X,
    Polynomial.aevalAeval_Y, sub_zero, one_pow, zero_sub] at hswap
  have hnegOne : (-1 : ℂ) ^ n = 1 := by
    apply mul_left_cancel₀ hcoefficient
    simpa only [Algebra.algebraMap_self_apply, mul_one] using hswap.symm
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp
    hnegOne

/-- If the square of the diagonal divides the form, the even exponent has
positive half. -/
theorem ePair_eq_nonzero_scalar_mul_positive_even_diagonal_power
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n)
    (hsymmetric : Polynomial.Bivariate.swap theta = theta)
    (hdiagonal : ePairDiagonal ℂ ^ 2 ∣ theta)
    (hsupport : EPairProjectiveZerosOnDiagonal theta) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ coefficient : ℂ, coefficient ≠ 0 ∧
      theta = algebraMap ℂ (EPairRing ℂ) coefficient *
        ePairDiagonal ℂ ^ (2 * k) := by
  obtain ⟨coefficient, hcoefficient, hpower⟩ :=
    ePair_eq_scalar_mul_first_sub_second_pow_of_projective_support
      hhomogeneous hsupport
  obtain ⟨k, hk⟩ :=
    ePair_exponent_even_of_projective_support
      hhomogeneous hsymmetric hsupport
  have hn : n = 2 * k := by omega
  have hdiagonalPower :
      (ePairFirst ℂ - ePairSecond ℂ) ^ n =
        ePairDiagonal ℂ ^ (2 * k) := by
    rw [hn]
    have hneg :
        ePairFirst ℂ - ePairSecond ℂ = -ePairDiagonal ℂ := by
      simp only [ePairDiagonal]
      ring
    rw [hneg]
    have heven : Even (2 * k) := ⟨k, by omega⟩
    exact heven.neg_pow (ePairDiagonal ℂ)
  have hpowerDiagonal :
      theta = algebraMap ℂ (EPairRing ℂ) coefficient *
        ePairDiagonal ℂ ^ (2 * k) := by
    rw [hpower, hdiagonalPower]
  have hkPositive : 1 ≤ k := by
    by_contra hkzero
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkzero
    subst k
    obtain ⟨quotient, hquotient⟩ := hdiagonal
    have hevalZero : ePairPointEval ℂ 0 0 theta = 0 := by
      rw [hquotient, map_mul, map_pow]
      rw [ePairDiagonal, map_sub, ePairPointEval_second,
        ePairPointEval_first]
      norm_num
    have hevalCoefficient :
        ePairPointEval ℂ 0 0 theta = coefficient := by
      rw [hpowerDiagonal]
      rw [map_mul, (ePairPointEval ℂ 0 0).commutes,
        Algebra.algebraMap_self_apply]
      simp
    exact hcoefficient (hevalCoefficient.symm.trans hevalZero)
  exact ⟨k, hkPositive, coefficient, hcoefficient, hpowerDiagonal⟩

/-- For the residual polynomial `Theta_R`, diagonal support contradicts the
cocycle obstruction.  Hence `Theta_R` has a projective zero away from the
diagonal.  The conclusion also covers the zero polynomial. -/
theorem eThetaPolynomial_exists_off_diagonal_projective_zero
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hdiagonal :
      ePairDiagonal ℂ ^ 2 ∣ eThetaPolynomial ℂ c) :
    ∃ x X : ℂ, (x ≠ 0 ∨ X ≠ 0) ∧
      ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0 ∧ x ≠ X := by
  by_contra hnone
  have hsupport :
      EPairProjectiveZerosOnDiagonal (eThetaPolynomial ℂ c) := by
    intro x X hnonzero hzero
    by_contra hne
    apply hnone
    refine ⟨x, X, hnonzero, ?_, hne⟩
    rw [ePairPointEval_eq_eval_iteratedToForm]
    exact hzero
  obtain ⟨k, hk, coefficient, hcoefficient, hpower⟩ :=
    ePair_eq_nonzero_scalar_mul_positive_even_diagonal_power
      hhomogeneous (eThetaPolynomial_swap ℂ c) hdiagonal hsupport
  exact eThetaPolynomial_diagonal_power_impossible
    omega homega c k hk coefficient hcoefficient hpower

end OnLeConjecture.DThree
