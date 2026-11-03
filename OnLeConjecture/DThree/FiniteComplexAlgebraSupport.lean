/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Norm.Basic

/-!
# Zeros of norms in finite complex algebras

If an element of a finite dimensional commutative complex algebra has zero
norm, it vanishes under a complex algebra homomorphism. The proof passes to a
maximal ideal containing the element and embeds the integral residue domain
into the algebraically closed base field.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

/-- An element with zero norm in a finite dimensional commutative complex
algebra vanishes at a complex algebra point. -/
theorem exists_complexAlgHom_eq_zero_of_norm_eq_zero
    {A : Type*} [CommRing A] [Algebra ℂ A] [Nontrivial A]
    [FiniteDimensional ℂ A] {a : A}
    (ha : Algebra.norm ℂ a = 0) :
    ∃ φ : A →ₐ[ℂ] ℂ, φ a = 0 := by
  classical
  have haNonunit : ¬ IsUnit a := by
    intro haUnit
    have hnormUnit : IsUnit (Algebra.norm ℂ a) :=
      haUnit.map (Algebra.norm ℂ)
    rw [ha] at hnormUnit
    exact not_isUnit_zero hnormUnit
  have hspan : Ideal.span ({a} : Set A) ≠ ⊤ :=
    Ideal.span_singleton_ne_top haNonunit
  obtain ⟨M, hM, hspanM⟩ :=
    Ideal.exists_le_maximal (Ideal.span ({a} : Set A)) hspan
  let _ : M.IsMaximal := hM
  let ψ : (A ⧸ M) →ₐ[ℂ] ℂ := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ ℂ M), ?_⟩
  have haM : a ∈ M :=
    hspanM (Ideal.mem_span_singleton_self a)
  simp only [AlgHom.comp_apply]
  change ψ (Ideal.Quotient.mk M a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr haM, map_zero]

end OnLeConjecture.DThree
