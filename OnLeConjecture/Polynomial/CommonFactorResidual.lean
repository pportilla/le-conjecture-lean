/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Removing the common factor of a polynomial family

A nonzero family of complex polynomials generates a nonzero principal
ideal. Division by its generator produces a family with no common zero.
The common zeros of the original family are exactly the zeros of the
generator. The index type need not be finite.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial Submodule.IsPrincipal

/-- Removing the generator of the common polynomial ideal leaves no
common zero. The original common zeros are exactly those of that generator. -/
theorem exists_common_factor_residual
    {ι : Type*} (F : ι → ℂ[X]) (hne : ∃ i, F i ≠ 0) :
    ∃ (G : ℂ[X]) (H : ι → ℂ[X]), G ≠ 0 ∧
      (∀ i, F i = G * H i) ∧
      (∀ z : ℂ, ∃ i, (H i).eval z ≠ 0) ∧
      (∀ z : ℂ, G.eval z = 0 ↔ ∀ i, (F i).eval z = 0) := by
  classical
  let I : Ideal ℂ[X] := Ideal.span (Set.range F)
  let G : ℂ[X] := generator I
  have hdiv (i : ι) : G ∣ F i :=
    (mem_iff_generator_dvd I).mp (Ideal.subset_span (Set.mem_range_self i))
  have hG : G ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hne
    have h := hdiv i
    rw [hz, zero_dvd_iff] at h
    exact hi h
  choose H hH using hdiv
  have hresidual (z : ℂ) : ∃ i, (H i).eval z ≠ 0 := by
    by_contra hnot
    push Not at hnot
    have hall (i : ι) : X - C z ∣ H i := dvd_iff_isRoot.mpr (hnot i)
    have hGdiv : G * (X - C z) ∣ G := by
      apply (dvd_generator_span_iff).mpr
      rintro _ ⟨i, rfl⟩
      rw [hH i]
      exact mul_dvd_mul_left G (hall i)
    obtain ⟨r, hr⟩ := hGdiv
    have hone : (1 : ℂ[X]) = (X - C z) * r := by
      apply mul_left_cancel₀ hG
      simpa only [mul_one, ← mul_assoc] using hr
    exact not_isUnit_X_sub_C z (isUnit_iff_dvd_one.mpr ⟨r, hone⟩)
  refine ⟨G, H, hG, hH, hresidual, ?_⟩
  intro z
  constructor
  · intro hz i
    rw [hH i, eval_mul, hz, zero_mul]
  · intro hall
    obtain ⟨i, hi⟩ := hresidual z
    have hz := hall i
    rw [hH i, eval_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_right hi

end OnLeConjecture.Polynomial
