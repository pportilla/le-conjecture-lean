/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.TwoForms
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Rescaling the two forms in the case `d = 3`

This file carries out the source and target rescalings after the coefficient
classification in `OnLeConjecture.DThree.TwoForms`.
-/

public section

namespace OnLeConjecture.DThree

open Polynomial

/-- Substitute `sX` in a polynomial and multiply its value by `u`. -/
@[expose]
noncomputable def rescale {K : Type*} [CommRing K]
    (s u : K) (p : K[X]) : K[X] :=
  C u * p.comp (C s * X)

/-- A polynomial in the two variables used for the homogeneous initial
forms.  Variable `0` is `x` and variable `1` is `t`. -/
abbrev Form (K : Type*) [CommSemiring K] := MvPolynomial (Fin 2) K

/-- The source variable `x` in a homogeneous initial form. -/
@[expose]
noncomputable def formX {K : Type*} [CommSemiring K] : Form K :=
  MvPolynomial.X 0

/-- The source variable `t` in a homogeneous initial form. -/
@[expose]
noncomputable def formT {K : Type*} [CommSemiring K] : Form K :=
  MvPolynomial.X 1

/-- The degree three homogenization of `cubic A B`. -/
@[expose]
noncomputable def cubicForm {K : Type*} [CommRing K] (A B : K) : Form K :=
  formX ^ 3 + MvPolynomial.C A * formX * formT ^ 2 +
    MvPolynomial.C B * formT ^ 3

/-- The degree four homogenization of `quartic c4 c3 c2 c1 c0`. -/
@[expose]
noncomputable def quarticForm {K : Type*} [CommRing K]
    (c4 c3 c2 c1 c0 : K) : Form K :=
  MvPolynomial.C c4 * formX ^ 4 +
    MvPolynomial.C c3 * formX ^ 3 * formT +
    MvPolynomial.C c2 * formX ^ 2 * formT ^ 2 +
    MvPolynomial.C c1 * formX * formT ^ 3 +
    MvPolynomial.C c0 * formT ^ 4

/-- Replace `x` by `sx`, keep `t` fixed, and multiply a homogeneous form
by `u`. -/
@[expose]
noncomputable def rescaleForm {K : Type*} [CommRing K]
    (s u : K) (F : Form K) : Form K :=
  MvPolynomial.C u *
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i ↦ if i = 0 then MvPolynomial.C s * formX else formT) F

variable {K : Type*} [Field K]

private theorem rescale_cubic_formula (s u A B : K) :
    rescale s u (cubic A B) =
      C (u * s ^ 3) * X ^ 3 + C (u * A * s) * X + C (u * B) := by
  simp [rescale, cubic]
  ring

private theorem rescale_quartic_formula
    (s u c4 c3 c2 c1 c0 : K) :
    rescale s u (quartic c4 c3 c2 c1 c0) =
      quartic (u * c4 * s ^ 4) (u * c3 * s ^ 3)
        (u * c2 * s ^ 2) (u * c1 * s) (u * c0) := by
  simp [rescale, quartic]
  ring

private theorem rescale_cubicForm_formula (s u A B : K) :
    rescaleForm s u (cubicForm A B) =
      MvPolynomial.C (u * s ^ 3) * formX ^ 3 +
        MvPolynomial.C (u * A * s) * formX * formT ^ 2 +
        MvPolynomial.C (u * B) * formT ^ 3 := by
  simp [rescaleForm, cubicForm, formX, formT]
  ring

private theorem rescale_quarticForm_formula
    (s u c4 c3 c2 c1 c0 : K) :
    rescaleForm s u (quarticForm c4 c3 c2 c1 c0) =
      quarticForm (u * c4 * s ^ 4) (u * c3 * s ^ 3)
        (u * c2 * s ^ 2) (u * c1 * s) (u * c0) := by
  simp [rescaleForm, quarticForm, formX, formT]
  ring

/-- Equality of the univariate coefficient presentations induces equality of
their degree four homogenizations. -/
theorem quarticForm_eq_of_quartic_eq
    {c4 c3 c2 c1 c0 d4 d3 d2 d1 d0 : K}
    (h : quartic c4 c3 c2 c1 c0 = quartic d4 d3 d2 d1 d0) :
    quarticForm c4 c3 c2 c1 c0 = quarticForm d4 d3 d2 d1 d0 := by
  have h4 : c4 = d4 := by
    have hc := congrArg (fun p : K[X] ↦ p.coeff 4) h
    simpa [quartic] using hc
  have h3 : c3 = d3 := by
    have hc := congrArg (fun p : K[X] ↦ p.coeff 3) h
    simpa [quartic] using hc
  have h2 : c2 = d2 := by
    have hc := congrArg (fun p : K[X] ↦ p.coeff 2) h
    simpa [quartic] using hc
  have h1 : c1 = d1 := by
    have hc := congrArg (fun p : K[X] ↦ p.coeff 1) h
    simpa [quartic] using hc
  have h0 : c0 = d0 := by
    have hc := congrArg (fun p : K[X] ↦ p.coeff 0) h
    simpa [quartic] using hc
  rw [h4, h3, h2, h1, h0]

variable [CharZero K] [IsAlgClosed K]

/-- The coefficient alternative with vanishing linear cubic coefficient
normalizes to the `E` pair. -/
theorem exists_E_rescaling (B c4 : K) (hB : B ≠ 0) (hc4 : c4 ≠ 0) :
    ∃ s u v : K,
      s ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      rescale s u (cubic 0 B) = X ^ 3 + C 3 ∧
      rescale s v (C c4 * (X ^ 4 + C (4 * B / 3) * X)) =
        X ^ 4 + C 4 * X ∧
      rescaleForm s u (cubicForm 0 B) = cubicForm 0 3 ∧
      rescaleForm s v
          (quarticForm c4 0 0 (c4 * (4 * B / 3)) 0) =
        quarticForm 1 0 0 4 0 := by
  obtain ⟨s, hs3⟩ := IsAlgClosed.exists_pow_nat_eq (B / 3) (by norm_num : 0 < 3)
  have hthree : (3 : K) ≠ 0 := by norm_num
  have hs : s ≠ 0 := by
    intro hs0
    have hquot : B / 3 = 0 := by
      rw [← hs3, hs0]
      norm_num
    exact (div_ne_zero hB hthree) hquot
  have hBformula : B = 3 * s ^ 3 := by
    calc
      B = (B / 3) * 3 := by field_simp
      _ = s ^ 3 * 3 := by rw [hs3]
      _ = 3 * s ^ 3 := by ring
  let u : K := (s ^ 3)⁻¹
  let v : K := (c4 * s ^ 4)⁻¹
  have hu_lead : u * s ^ 3 = 1 := by
    simp [u, hs]
  have hu_const : u * B = 3 := by
    rw [hBformula]
    calc
      u * (3 * s ^ 3) = 3 * (u * s ^ 3) := by ring
      _ = 3 := by rw [hu_lead, mul_one]
  have hv_lead : v * c4 * s ^ 4 = 1 := by
    calc
      v * c4 * s ^ 4 = (c4 * s ^ 4)⁻¹ * (c4 * s ^ 4) := by
        simp only [v]
        ring
      _ = 1 := inv_mul_cancel₀ (mul_ne_zero hc4 (pow_ne_zero 4 hs))
  have hv_linear : v * (c4 * (4 * B / 3)) * s = 4 := by
    rw [hBformula]
    calc
      v * (c4 * (4 * (3 * s ^ 3) / 3)) * s = 4 * (v * c4 * s ^ 4) := by
        field_simp
      _ = 4 := by rw [hv_lead, mul_one]
  have hquartic :
      C c4 * (X ^ 4 + C (4 * B / 3) * X) =
        quartic c4 0 0 (c4 * (4 * B / 3)) 0 := by
    simp [quartic]
    ring
  refine ⟨s, u, v, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_ne_zero (pow_ne_zero 3 hs)
  · exact inv_ne_zero (mul_ne_zero hc4 (pow_ne_zero 4 hs))
  · rw [rescale_cubic_formula]
    simp [hu_lead, hu_const]
  · rw [hquartic, rescale_quartic_formula]
    simp [hv_lead, hv_linear, quartic]
  · rw [rescale_cubicForm_formula]
    simp [hu_lead, hu_const, cubicForm]
  · rw [rescale_quarticForm_formula]
    simp [hv_lead, hv_linear]

/-- The coefficient alternative with vanishing constant cubic coefficient
normalizes to the `H` pair. -/
theorem exists_H_rescaling (A c4 : K) (hA : A ≠ 0) (hc4 : c4 ≠ 0) :
    ∃ s u v : K,
      s ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      rescale s u (cubic A 0) = X ^ 3 + C 3 * X ∧
      rescale s v
          (C c4 *
            (X ^ 4 + C (4 * A / 3) * X ^ 2 + C (2 * A ^ 2 / 9))) =
        X ^ 4 + C 4 * X ^ 2 + C 2 ∧
      rescaleForm s u (cubicForm A 0) = cubicForm 3 0 ∧
      rescaleForm s v
          (quarticForm c4 0 (c4 * (4 * A / 3)) 0
            (c4 * (2 * A ^ 2 / 9))) =
        quarticForm 1 0 4 0 2 := by
  obtain ⟨s, hs2⟩ := IsAlgClosed.exists_pow_nat_eq (A / 3) (by norm_num : 0 < 2)
  have hthree : (3 : K) ≠ 0 := by norm_num
  have hs : s ≠ 0 := by
    intro hs0
    have hquot : A / 3 = 0 := by
      rw [← hs2, hs0]
      norm_num
    exact (div_ne_zero hA hthree) hquot
  have hAformula : A = 3 * s ^ 2 := by
    calc
      A = (A / 3) * 3 := by field_simp
      _ = s ^ 2 * 3 := by rw [hs2]
      _ = 3 * s ^ 2 := by ring
  let u : K := (s ^ 3)⁻¹
  let v : K := (c4 * s ^ 4)⁻¹
  have hu_lead : u * s ^ 3 = 1 := by
    simp [u, hs]
  have hu_linear : u * A * s = 3 := by
    rw [hAformula]
    calc
      u * (3 * s ^ 2) * s = 3 * (u * s ^ 3) := by ring
      _ = 3 := by rw [hu_lead, mul_one]
  have hv_lead : v * c4 * s ^ 4 = 1 := by
    calc
      v * c4 * s ^ 4 = (c4 * s ^ 4)⁻¹ * (c4 * s ^ 4) := by
        simp only [v]
        ring
      _ = 1 := inv_mul_cancel₀ (mul_ne_zero hc4 (pow_ne_zero 4 hs))
  have hv_quadratic : v * (c4 * (4 * A / 3)) * s ^ 2 = 4 := by
    rw [hAformula]
    calc
      v * (c4 * (4 * (3 * s ^ 2) / 3)) * s ^ 2 =
          4 * (v * c4 * s ^ 4) := by
        field_simp
      _ = 4 := by rw [hv_lead, mul_one]
  have hv_const : v * (c4 * (2 * A ^ 2 / 9)) = 2 := by
    rw [hAformula]
    calc
      v * (c4 * (2 * (3 * s ^ 2) ^ 2 / 9)) =
          2 * (v * c4 * s ^ 4) := by
        field_simp
        ring
      _ = 2 := by rw [hv_lead, mul_one]
  have hquartic :
      C c4 *
          (X ^ 4 + C (4 * A / 3) * X ^ 2 + C (2 * A ^ 2 / 9)) =
        quartic c4 0 (c4 * (4 * A / 3)) 0
          (c4 * (2 * A ^ 2 / 9)) := by
    simp [quartic]
    ring
  refine ⟨s, u, v, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_ne_zero (pow_ne_zero 3 hs)
  · exact inv_ne_zero (mul_ne_zero hc4 (pow_ne_zero 4 hs))
  · rw [rescale_cubic_formula]
    simp [hu_lead, hu_linear]
  · rw [hquartic, rescale_quartic_formula]
    simp [hv_lead, hv_quadratic, hv_const, quartic]
  · rw [rescale_cubicForm_formula]
    simp [hu_lead, hu_linear, cubicForm]
  · rw [rescale_quarticForm_formula]
    simp [hv_lead, hv_quadratic, hv_const]

/-- A nonzero constant value of `4 p' χ - 3 p χ'` allows a nonzero
rescaling of the source variable and independent nonzero rescalings of the
two target coordinates which give exactly the `E` or `H` pair from the
paper. -/
theorem rescale_to_E_or_H
    (A B c4 c3 c2 c1 c0 c : K)
    (hc : c ≠ 0)
    (hODE :
      4 * (cubic A B).derivative * quartic c4 c3 c2 c1 c0 -
          3 * cubic A B * (quartic c4 c3 c2 c1 c0).derivative = C c) :
    ∃ s u v : K,
      s ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      ((rescale s u (cubic A B) = X ^ 3 + C 3 ∧
          rescale s v (quartic c4 c3 c2 c1 c0) =
            X ^ 4 + C 4 * X) ∨
       (rescale s u (cubic A B) = X ^ 3 + C 3 * X ∧
          rescale s v (quartic c4 c3 c2 c1 c0) =
            X ^ 4 + C 4 * X ^ 2 + C 2)) := by
  rcases classify_two_forms_of_ode A B c4 c3 c2 c1 c0 c hc hODE with
    ⟨hc4, hE | hH⟩
  · rcases hE with ⟨hA, hB, hquartic⟩
    rcases exists_E_rescaling B c4 hB hc4 with
      ⟨s, u, v, hs, hu, hv, hp, hq, _hPf, _hQf⟩
    refine ⟨s, u, v, hs, hu, hv, Or.inl ⟨?_, ?_⟩⟩
    · rw [hA]
      exact hp
    · rw [hquartic]
      exact hq
  · rcases hH with ⟨hB, hA, hquartic⟩
    rcases exists_H_rescaling A c4 hA hc4 with
      ⟨s, u, v, hs, hu, hv, hp, hq, _hPf, _hQf⟩
    refine ⟨s, u, v, hs, hu, hv, Or.inr ⟨?_, ?_⟩⟩
    · rw [hB]
      exact hp
    · rw [hquartic]
      exact hq

/-- The homogeneous degree three and degree four initial forms themselves
normalize to the two pairs displayed in Lemma `dthree-twoforms`. -/
theorem rescaleForms_to_E_or_H
    (A B c4 c3 c2 c1 c0 c : K)
    (hc : c ≠ 0)
    (hODE :
      4 * (cubic A B).derivative * quartic c4 c3 c2 c1 c0 -
          3 * cubic A B * (quartic c4 c3 c2 c1 c0).derivative = C c) :
    ∃ s u v : K,
      s ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      ((rescaleForm s u (cubicForm A B) = cubicForm 0 3 ∧
          rescaleForm s v (quarticForm c4 c3 c2 c1 c0) =
            quarticForm 1 0 0 4 0) ∨
       (rescaleForm s u (cubicForm A B) = cubicForm 3 0 ∧
          rescaleForm s v (quarticForm c4 c3 c2 c1 c0) =
            quarticForm 1 0 4 0 2)) := by
  rcases classify_two_forms_of_ode A B c4 c3 c2 c1 c0 c hc hODE with
    ⟨hc4, hE | hH⟩
  · rcases hE with ⟨hA, hB, hquartic⟩
    rcases exists_E_rescaling B c4 hB hc4 with
      ⟨s, u, v, hs, hu, hv, _hp, _hq, hPf, hQf⟩
    have hquartic' :
        quartic c4 c3 c2 c1 c0 =
          quartic c4 0 0 (c4 * (4 * B / 3)) 0 := by
      calc
        quartic c4 c3 c2 c1 c0 =
            C c4 * (X ^ 4 + C (4 * B / 3) * X) := hquartic
        _ = quartic c4 0 0 (c4 * (4 * B / 3)) 0 := by
          simp [quartic]
          ring
    have hquarticForm := quarticForm_eq_of_quartic_eq hquartic'
    refine ⟨s, u, v, hs, hu, hv, Or.inl ⟨?_, ?_⟩⟩
    · rw [hA]
      exact hPf
    · rw [hquarticForm]
      exact hQf
  · rcases hH with ⟨hB, hA, hquartic⟩
    rcases exists_H_rescaling A c4 hA hc4 with
      ⟨s, u, v, hs, hu, hv, _hp, _hq, hPf, hQf⟩
    have hquartic' :
        quartic c4 c3 c2 c1 c0 =
          quartic c4 0 (c4 * (4 * A / 3)) 0
            (c4 * (2 * A ^ 2 / 9)) := by
      calc
        quartic c4 c3 c2 c1 c0 =
            C c4 *
              (X ^ 4 + C (4 * A / 3) * X ^ 2 +
                C (2 * A ^ 2 / 9)) := hquartic
        _ = quartic c4 0 (c4 * (4 * A / 3)) 0
              (c4 * (2 * A ^ 2 / 9)) := by
          simp [quartic]
          ring
    have hquarticForm := quarticForm_eq_of_quartic_eq hquartic'
    refine ⟨s, u, v, hs, hu, hv, Or.inr ⟨?_, ?_⟩⟩
    · rw [hB]
      exact hPf
    · rw [hquarticForm]
      exact hQf

end OnLeConjecture.DThree
