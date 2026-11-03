/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm
public import OnLeConjecture.Analytic.OrdinaryWeightedOrder
import Mathlib.Tactic

/-!
# Constant linear combinations of analytic initial forms and Jacobians

A common Jacobian divisor is preserved by constant linear combinations.
Every polynomial in the linear span of prescribed initial forms lifts to
the corresponding linear span of analytic germs, with the same strict tail.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The common divisors of the pairwise Jacobians also divide the Jacobian
of any two constant linear combinations. No invertibility is needed. -/
theorem dvd_jacobian_of_mem_linear_span
    {ι : Type*} (f : ι → Germ 2) (c : Germ 2)
    (hdiv : ∀ i j, c ∣ jacobian (f i) (f j))
    {g h : Germ 2}
    (hg : g ∈ Submodule.span ℂ (Set.range f))
    (hh : h ∈ Submodule.span ℂ (Set.range f)) : c ∣ jacobian g h := by
  refine Submodule.span_induction₂ (p := fun g h _ _ => c ∣ jacobian g h)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hg hh
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact hdiv i j
  · intro y _
    have hz : jacobian 0 y = 0 := by simpa using jacobian_const_left 0 y
    rw [hz]
    exact dvd_zero c
  · intro x _
    have hz : jacobian x 0 = 0 := by simpa using jacobian_const_right x 0
    rw [hz]
    exact dvd_zero c
  · intro x y z _ _ _ hx hy
    rw [jacobian_add_left]
    exact dvd_add hx hy
  · intro x y z _ _ _ hy hz
    rw [jacobian_add_right]
    exact dvd_add hy hz
  · intro r x y _ _ hxy
    have heq : jacobian (r • x) y = r • jacobian x y := by
      simp only [jacobian_eq, partialDerivative_smul, smul_mul_assoc, smul_sub]
    rw [heq, Algebra.smul_def]
    exact dvd_mul_of_dvd_right hxy _
  · intro r x y _ _ hxy
    have heq : jacobian x (r • y) = r • jacobian x y := by
      simp only [jacobian_eq, partialDerivative_smul, mul_smul_comm, smul_sub]
    rw [heq, Algebra.smul_def]
    exact dvd_mul_of_dvd_right hxy _

/-- Linear combinations of polynomial jets lift to the identical constant
linear combinations of the analytic germs. -/
theorem exists_linear_span_lift_of_initial_form
    {ι : Type*} (f : ι → Germ 2) (P : ι → MvPolynomial (Fin 2) ℂ) (D : ℕ)
    (htail : ∀ i, f i - coordinatePolynomialAlgHom 2 (P i) ∈ maximalIdeal 2 ^ D)
    {Q : MvPolynomial (Fin 2) ℂ} (hQ : Q ∈ Submodule.span ℂ (Set.range P)) :
    ∃ g ∈ Submodule.span ℂ (Set.range f),
      g - coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ D := by
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨i, rfl⟩ := hQ
    exact ⟨f i, Submodule.subset_span (Set.mem_range_self i), htail i⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add Q R _ _ hQ hR =>
    obtain ⟨g, hg, hgt⟩ := hQ
    obtain ⟨h, hh, hht⟩ := hR
    refine ⟨g + h, Submodule.add_mem _ hg hh, ?_⟩
    rw [map_add, show g + h - (coordinatePolynomialAlgHom 2 Q +
      coordinatePolynomialAlgHom 2 R) =
      (g - coordinatePolynomialAlgHom 2 Q) + (h - coordinatePolynomialAlgHom 2 R) by abel]
    exact (maximalIdeal 2 ^ D).add_mem hgt hht
  | smul r Q _ hQ =>
    obtain ⟨g, hg, hgt⟩ := hQ
    refine ⟨r • g, Submodule.smul_mem _ r hg, ?_⟩
    rw [map_smul, ← smul_sub]
    exact ((maximalIdeal 2 ^ D).restrictScalars ℂ).smul_mem r hgt

end OnLeConjecture.Analytic.Germ
