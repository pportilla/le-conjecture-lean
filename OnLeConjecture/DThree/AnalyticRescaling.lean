/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.DiagonalCoordinates
public import OnLeConjecture.Analytic.CoordinatePermutation
public import OnLeConjecture.DThree.Rescaling
public import OnLeConjecture.Polynomial.WeightedJacobian
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.FinCases

/-!
# Analytic realization of the degree three rescaling

The polynomial rescaling from `DThree.Rescaling` is induced by diagonal
source and target equivalences of pointed analytic germs. This file also
transports the prescribed initial forms and the orders of their analytic
remainders.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The source scaling multiplies `x` by `s` and fixes `t`. -/
@[expose]
noncomputable def sourceRescaleVector (s : ℂ) : Fin 2 → ℂ :=
  ![s, 1]

/-- The three target coordinates are multiplied independently. -/
@[expose]
noncomputable def targetRescaleVector (u v w : ℂ) : Fin 3 → ℂ :=
  ![u, v, w]

theorem sourceRescaleVector_ne_zero {s : ℂ} (hs : s ≠ 0) :
    ∀ i, sourceRescaleVector s i ≠ 0 := by
  intro i
  fin_cases i
  · simpa [sourceRescaleVector] using hs
  · simp [sourceRescaleVector]

theorem targetRescaleVector_ne_zero {u v w : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∀ i, targetRescaleVector u v w i ≠ 0 := by
  intro i
  fin_cases i
  · simpa [targetRescaleVector] using hu
  · simpa [targetRescaleVector] using hv
  · simpa [targetRescaleVector] using hw

/-- Apply the source scaling followed by the three target scalings to a
pointed plane map germ. -/
@[expose]
noncomputable def rescaledPointedMap
    (g : PointedMapGerm 2 3) (s u v w : ℂ)
    (hs : s ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    PointedMapGerm 2 3 :=
  (diagonalPointedEquiv (targetRescaleVector u v w)
      (targetRescaleVector_ne_zero hu hv hw)).forward.comp
    (g.comp
      (diagonalPointedEquiv (sourceRescaleVector s)
        (sourceRescaleVector_ne_zero hs)).forward)

/-- The rescaled germ is right left equivalent to the original germ. -/
theorem rightLeftEquivalent_rescaledPointedMap
    (g : PointedMapGerm 2 3) (s u v w : ℂ)
    (hs : s ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    g.RightLeftEquivalent (rescaledPointedMap g s u v w hs hu hv hw) := by
  exact
    ⟨diagonalPointedEquiv (sourceRescaleVector s)
        (sourceRescaleVector_ne_zero hs),
      diagonalPointedEquiv (targetRescaleVector u v w)
        (targetRescaleVector_ne_zero hu hv hw), rfl⟩

/-- A component of the rescaled germ is the source pullback of the old
component multiplied by its target scalar. -/
theorem rescaledPointedMap_component
    (g : PointedMapGerm 2 3) (s u v w : ℂ)
    (hs : s ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (i : Fin 3) :
    (rescaledPointedMap g s u v w hs hu hv hw).1.component i =
      Germ.constRingHom 2 (targetRescaleVector u v w i) *
        (diagonalPointedEquiv (sourceRescaleVector s)
          (sourceRescaleVector_ne_zero hs)).forward.pullbackRingHom
            (g.1.component i) := by
  rw [rescaledPointedMap,
    PointedMapGerm.component_comp_general,
    diagonalPointedEquiv_component, map_mul,
    PointedMapGerm.pullback_constRingHom,
    PointedMapGerm.pullback_coordinate,
    PointedMapGerm.component_comp_general]

/-- Source diagonal substitution is the substitution used by
`rescaleForm`. -/
theorem diagonalPolynomialSubstitution_sourceRescale
    (s : ℂ) (F : Form ℂ) :
    diagonalPolynomialSubstitution (sourceRescaleVector s) F =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i ↦ if i = 0 then MvPolynomial.C s * formX else formT) F := by
  apply DFunLike.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [diagonalPolynomialSubstitution]
  · intro i
    fin_cases i
    · simp [diagonalPolynomialSubstitution, sourceRescaleVector,
        formX]
    · simp [diagonalPolynomialSubstitution, sourceRescaleVector,
        formT]

/-- Evaluation of a rescaled form is the target scalar times the source
pullback of the original evaluated form. -/
theorem coordinatePolynomial_rescaleForm
    (s u : ℂ) (hs : s ≠ 0) (F : Form ℂ) :
    Germ.coordinatePolynomialAlgHom 2 (rescaleForm s u F) =
      Germ.constRingHom 2 u *
        (diagonalPointedEquiv (sourceRescaleVector s)
          (sourceRescaleVector_ne_zero hs)).forward.pullbackRingHom
            (Germ.coordinatePolynomialAlgHom 2 F) := by
  rw [rescaleForm, map_mul, Germ.coordinatePolynomialAlgHom_C,
    diagonalPointedEquiv_pullback_coordinatePolynomial,
    diagonalPolynomialSubstitution_sourceRescale]

/-- The rescaling preserves the ordinary homogeneous degree of a form. -/
theorem rescaleForm_isHomogeneous {F : Form ℂ} {N : ℕ}
    (hF : F.IsHomogeneous N) (s u : ℂ) :
    (rescaleForm s u F).IsHomogeneous N := by
  have hsubstitution :
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun i : Fin 2 ↦
          if i = 0 then MvPolynomial.C s * formX else formT) F
            ).IsHomogeneous N := by
    have h := hF.eval₂ MvPolynomial.C
      (fun i : Fin 2 ↦
        if i = 0 then MvPolynomial.C s * formX else formT)
      (fun c ↦ MvPolynomial.isHomogeneous_C (σ := Fin 2) c)
      (fun i ↦ by
        fin_cases i
        · simpa [formX] using
            (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul s
        · simpa [formT] using
            MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))
    simpa using h
  exact hsubstitution.C_mul u

/-- Partial differentiation of diagonal substitution introduces the scalar
of the differentiated coordinate. -/
theorem pderiv_diagonalPolynomialSubstitution_sourceRescale
    (s : ℂ) (F : Form ℂ) (k : Fin 2) :
    MvPolynomial.pderiv k
        (diagonalPolynomialSubstitution (sourceRescaleVector s) F) =
      MvPolynomial.C (sourceRescaleVector s k) *
        diagonalPolynomialSubstitution (sourceRescaleVector s)
          (MvPolynomial.pderiv k F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      simp [diagonalPolynomialSubstitution]
  | add p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq]
      rw [(diagonalPolynomialSubstitution
        (sourceRescaleVector s)).map_add]
      ring
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.pderiv_mul,
        diagonalPolynomialSubstitution_X,
        MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X, hp]
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, map_mul,
        diagonalPolynomialSubstitution_X]
      fin_cases k
      all_goals fin_cases i
      all_goals simp [diagonalPolynomialSubstitution, sourceRescaleVector]
      all_goals ring

/-- The Jacobian of two rescaled forms is the source substitution of the old
Jacobian multiplied by the three coordinate scalars. -/
theorem jacobian_rescaleForm (s u v : ℂ) (F G : Form ℂ) :
    OnLeConjecture.Polynomial.jacobian
        (rescaleForm s u F) (rescaleForm s v G) =
      MvPolynomial.C (u * v * s) *
        diagonalPolynomialSubstitution (sourceRescaleVector s)
          (OnLeConjecture.Polynomial.jacobian F G) := by
  have hderiv (a : ℂ) (H : Form ℂ) (k : Fin 2) :
      MvPolynomial.pderiv k (rescaleForm s a H) =
        MvPolynomial.C (a * sourceRescaleVector s k) *
          diagonalPolynomialSubstitution (sourceRescaleVector s)
            (MvPolynomial.pderiv k H) := by
    rw [rescaleForm, MvPolynomial.pderiv_C_mul,
      ← diagonalPolynomialSubstitution_sourceRescale,
      pderiv_diagonalPolynomialSubstitution_sourceRescale]
    simp only [map_mul]
    ring
  rw [OnLeConjecture.Polynomial.jacobian,
    hderiv u F 0, hderiv v G 1,
    hderiv u F 1, hderiv v G 0,
    OnLeConjecture.Polynomial.jacobian]
  rw [(diagonalPolynomialSubstitution
      (sourceRescaleVector s)).map_sub,
    (diagonalPolynomialSubstitution
      (sourceRescaleVector s)).map_mul,
    (diagonalPolynomialSubstitution
      (sourceRescaleVector s)).map_mul]
  simp only [sourceRescaleVector, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, map_mul]
  ring

/-- Divisibility of the Jacobian by a power of `t` is preserved by the
source and target rescalings. -/
theorem formT_pow_dvd_jacobian_rescaleForm
    (s u v : ℂ) (F G : Form ℂ) (k : ℕ)
    (hdiv : formT ^ k ∣
      OnLeConjecture.Polynomial.jacobian F G) :
    formT ^ k ∣
      OnLeConjecture.Polynomial.jacobian
        (rescaleForm s u F) (rescaleForm s v G) := by
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨MvPolynomial.C (u * v * s) *
    diagonalPolynomialSubstitution (sourceRescaleVector s) Q, ?_⟩
  rw [jacobian_rescaleForm, hQ,
    (diagonalPolynomialSubstitution
      (sourceRescaleVector s)).map_mul,
    (diagonalPolynomialSubstitution
      (sourceRescaleVector s)).map_pow]
  have hformT :
      diagonalPolynomialSubstitution (sourceRescaleVector s) formT =
        formT := by
    simp [diagonalPolynomialSubstitution, sourceRescaleVector, formT]
  rw [hformT]
  simp only [map_mul]
  ring

/-- A strict ordinary tail remains a strict tail of the rescaled component.
-/
theorem rescaledPointedMap_component_tail
    (g : PointedMapGerm 2 3) (s u v w : ℂ)
    (hs : s ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (i : Fin 3) (F : Form ℂ) (k : ℕ)
    (htail : g.1.component i - Germ.coordinatePolynomialAlgHom 2 F ∈
      Germ.maximalIdeal 2 ^ k) :
    (rescaledPointedMap g s u v w hs hu hv hw).1.component i -
        Germ.coordinatePolynomialAlgHom 2
          (rescaleForm s (targetRescaleVector u v w i) F) ∈
      Germ.maximalIdeal 2 ^ k := by
  rw [rescaledPointedMap_component,
    coordinatePolynomial_rescaleForm s
      (targetRescaleVector u v w i) hs F]
  rw [← mul_sub]
  apply Ideal.mul_mem_left
  have hpull :=
    (diagonalPointedEquiv (sourceRescaleVector s)
      (sourceRescaleVector_ne_zero hs)).pullback_mem_maximalIdeal_pow htail
  rw [map_sub] at hpull
  exact hpull

/-- The polynomial normalization of the degree three and degree four forms
is realized by a right left equivalence of pointed analytic germs. -/
theorem exists_rightLeft_rescaling_to_E_or_H
    (g : PointedMapGerm 2 3) (R : Form ℂ) (N : ℕ)
    (A B c4 c3 c2 c1 c0 c : ℂ)
    (hc : c ≠ 0)
    (hODE :
      4 * (cubic A B).derivative * quartic c4 c3 c2 c1 c0 -
          3 * cubic A B * (quartic c4 c3 c2 c1 c0).derivative =
        Polynomial.C c)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (cubicForm A B) ∈ Germ.maximalIdeal 2 ^ 4)
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (quarticForm c4 c3 c2 c1 c0) ∈ Germ.maximalIdeal 2 ^ 5)
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.maximalIdeal 2 ^ (N + 1)) :
    ∃ s : ℂ, ∃ h : PointedMapGerm 2 3,
      s ≠ 0 ∧ g.RightLeftEquivalent h ∧
      (h.HasInjectiveRepresentative ↔ g.HasInjectiveRepresentative) ∧
      ((h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (cubicForm 0 3) ∈ Germ.maximalIdeal 2 ^ 4 ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (quarticForm 1 0 0 4 0) ∈ Germ.maximalIdeal 2 ^ 5 ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.maximalIdeal 2 ^ (N + 1)) ∨
       (h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (cubicForm 3 0) ∈ Germ.maximalIdeal 2 ^ 4 ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (quarticForm 1 0 4 0 2) ∈ Germ.maximalIdeal 2 ^ 5 ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.maximalIdeal 2 ^ (N + 1))) := by
  obtain ⟨s, u, v, hs, hu, hv, hE | hH⟩ :=
    rescaleForms_to_E_or_H A B c4 c3 c2 c1 c0 c hc hODE
  all_goals
    let h := rescaledPointedMap g s u v 1 hs hu hv one_ne_zero
    have hequivalent : g.RightLeftEquivalent h :=
      rightLeftEquivalent_rescaledPointedMap
        g s u v 1 hs hu hv one_ne_zero
    have hinjective := hequivalent.hasInjectiveRepresentative_iff
    refine ⟨s, h, hs, hequivalent, hinjective, ?_⟩
  · apply Or.inl
    rcases hE with ⟨hzeroForm, honeForm⟩
    refine ⟨?_, ?_, ?_⟩
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 0 (cubicForm A B) 4 htailZero
      simpa [h, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 1
            (quarticForm c4 c3 c2 c1 c0) 5 htailOne
      simpa [h, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 2 R (N + 1) htailTwo
      simpa [h, targetRescaleVector] using htail
  · apply Or.inr
    rcases hH with ⟨hzeroForm, honeForm⟩
    refine ⟨?_, ?_, ?_⟩
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 0 (cubicForm A B) 4 htailZero
      simpa [h, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 1
            (quarticForm c4 c3 c2 c1 c0) 5 htailOne
      simpa [h, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 2 R (N + 1) htailTwo
      simpa [h, targetRescaleVector] using htail

/-- The analytic rescaling transports the homogeneous third form and both
Jacobian divisibilities together with the three strict tail conditions. -/
theorem exists_rightLeft_rescaling_to_E_or_H_with_jacobians
    (g : PointedMapGerm 2 3) (R : Form ℂ) (N : ℕ)
    (A B c4 c3 c2 c1 c0 c : ℂ)
    (hc : c ≠ 0)
    (hODE :
      4 * (cubic A B).derivative * quartic c4 c3 c2 c1 c0 -
          3 * cubic A B * (quartic c4 c3 c2 c1 c0).derivative =
        Polynomial.C c)
    (hR : R.IsHomogeneous N)
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm A B) R)
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm c4 c3 c2 c1 c0) R)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (cubicForm A B) ∈ Germ.maximalIdeal 2 ^ 4)
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (quarticForm c4 c3 c2 c1 c0) ∈ Germ.maximalIdeal 2 ^ 5)
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.maximalIdeal 2 ^ (N + 1)) :
    ∃ s : ℂ, ∃ h : PointedMapGerm 2 3,
      s ≠ 0 ∧ g.RightLeftEquivalent h ∧
      (h.HasInjectiveRepresentative ↔ g.HasInjectiveRepresentative) ∧
      (rescaleForm s 1 R).IsHomogeneous N ∧
      ((h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (cubicForm 0 3) ∈ Germ.maximalIdeal 2 ^ 4 ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (quarticForm 1 0 0 4 0) ∈ Germ.maximalIdeal 2 ^ 5 ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.maximalIdeal 2 ^ (N + 1) ∧
          formT ^ 5 ∣ OnLeConjecture.Polynomial.jacobian
            (cubicForm 0 3) (rescaleForm s 1 R) ∧
          formT ^ 5 ∣ OnLeConjecture.Polynomial.jacobian
            (quarticForm 1 0 0 4 0) (rescaleForm s 1 R)) ∨
       (h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (cubicForm 3 0) ∈ Germ.maximalIdeal 2 ^ 4 ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (quarticForm 1 0 4 0 2) ∈ Germ.maximalIdeal 2 ^ 5 ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.maximalIdeal 2 ^ (N + 1) ∧
          formT ^ 5 ∣ OnLeConjecture.Polynomial.jacobian
            (cubicForm 3 0) (rescaleForm s 1 R) ∧
          formT ^ 5 ∣ OnLeConjecture.Polynomial.jacobian
            (quarticForm 1 0 4 0 2) (rescaleForm s 1 R))) := by
  obtain ⟨s, u, v, hs, hu, hv, hE | hH⟩ :=
    rescaleForms_to_E_or_H A B c4 c3 c2 c1 c0 c hc hODE
  all_goals
    let h := rescaledPointedMap g s u v 1 hs hu hv one_ne_zero
    have hequivalent : g.RightLeftEquivalent h :=
      rightLeftEquivalent_rescaledPointedMap
        g s u v 1 hs hu hv one_ne_zero
    have hinjective := hequivalent.hasInjectiveRepresentative_iff
    have hRscaled : (rescaleForm s 1 R).IsHomogeneous N :=
      rescaleForm_isHomogeneous hR s 1
    refine ⟨s, h, hs, hequivalent, hinjective, hRscaled, ?_⟩
  · apply Or.inl
    rcases hE with ⟨hzeroForm, honeForm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 0 (cubicForm A B) 4 htailZero
      simpa [h, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 1
            (quarticForm c4 c3 c2 c1 c0) 5 htailOne
      simpa [h, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 2 R (N + 1) htailTwo
      simpa [h, targetRescaleVector] using htail
    · have hdiv := formT_pow_dvd_jacobian_rescaleForm
          s u 1 (cubicForm A B) R 5 hPdiv
      rw [hzeroForm] at hdiv
      exact hdiv
    · have hdiv := formT_pow_dvd_jacobian_rescaleForm
          s v 1 (quarticForm c4 c3 c2 c1 c0) R 5 hQdiv
      rw [honeForm] at hdiv
      exact hdiv
  · apply Or.inr
    rcases hH with ⟨hzeroForm, honeForm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 0 (cubicForm A B) 4 htailZero
      simpa [h, targetRescaleVector, hzeroForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 1
            (quarticForm c4 c3 c2 c1 c0) 5 htailOne
      simpa [h, targetRescaleVector, honeForm] using htail
    · have htail := rescaledPointedMap_component_tail
          g s u v 1 hs hu hv one_ne_zero 2 R (N + 1) htailTwo
      simpa [h, targetRescaleVector] using htail
    · have hdiv := formT_pow_dvd_jacobian_rescaleForm
          s u 1 (cubicForm A B) R 5 hPdiv
      rw [hzeroForm] at hdiv
      exact hdiv
    · have hdiv := formT_pow_dvd_jacobian_rescaleForm
          s v 1 (quarticForm c4 c3 c2 c1 c0) R 5 hQdiv
      rw [honeForm] at hdiv
      exact hdiv

end OnLeConjecture.DThree
