/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.SingleComparison
public import OnLeConjecture.KnotFloer.SpectralDualCertificate

/-!
# Two torus representatives suffice for the numerical reduction

Only the staircase vertices numbered one and two enter the final numerical
argument. Two representatives of the same normalized class at their
specified levels, one shifted chain map, and one dual certificate on the
image class suffice. No full staircase equivalence, exact spectral value,
or threshold attainment is needed for this implication.

The construction of these representatives in the geometric torus complex,
the normalized class, and the geometric cobordism map remains necessary.
The dual certificate must belong to the actual transverse complex.
-/

@[expose] public section

universe u v w

namespace OnLeConjecture.KnotFloer.Bifiltration

open CategoryTheory HomologicalComplex Staircase

variable {R : Type u} [CommRing R] [Nontrivial R]
  {ι : Type w} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat.{v} R) c}

/-- A representative and a dual certificate compare the two levels
without assuming that either spectral threshold is finite or attained. -/
theorem level_comparison_of_cycle_and_dual
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D}
    {gCob : ℝ} (hφ : F.Shifts G φ 0 gCob) (i : ι) (ξ : C.homology i)
    (t a b : ℝ) (hcycle : (F.weighted t).RepresentedBelow i ξ a)
    (ℓ : D.X i →ₗ[R] R)
    (hclass : ∀ z : D.cycles i, D.homologyπ i z = homologyMap φ i ξ →
      ℓ (D.iCycles i z) = 1)
    (hlevel : ∀ s : ℝ, s < b → ∀ x ∈ (G.weighted t).level s i, ℓ x = 0) :
    -2 * a ≤ -2 * b + t * gCob := by
  have hlo := (G.weighted t).le_spectralThreshold_of_dual ℓ hclass hlevel
  have hhi := RealFiltration.spectralThreshold_le_of_representedBelow
    (hcycle.map_shift (hφ.weighted t))
  have h := EReal.coe_le_coe_iff.mp (hlo.trans hhi)
  nlinarith

/-- A normalized representative at one explicit vertex gives its affine
lower bound after comparison with the transverse dual certificate. -/
theorem consecutive_affine_upper_of_cycle_and_dual
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D}
    {gCob gTr : ℝ} (hφ : F.Shifts G φ 0 gCob)
    (i : ι) (ξ : C.homology i) (n M : ℕ) (t : ℝ) (j : Fin (n + 1))
    (hcycle : (F.weighted t).RepresentedBelow i ξ (consecutiveWeight n t j))
    (ℓ : D.X i →ₗ[R] R)
    (hclass : ∀ z : D.cycles i, D.homologyπ i z = homologyMap φ i ξ →
      ℓ (D.iCycles i z) = 1)
    (hlevel : ∀ s : ℝ, s < gTr * t / 2 →
      ∀ x ∈ (G.weighted t).level s i, ℓ x = 0)
    (hgenus : (n : ℝ) * ((n : ℝ) + 1) / 2 - gTr + gCob =
      ((n : ℝ) + 1) - (M : ℝ)) :
    ((n : ℝ) + 1) * (j : ℝ) * t - (j : ℝ) * ((j : ℝ) + 1) ≤
      (((n : ℝ) + 1) - (M : ℝ)) * t := by
  have h := level_comparison_of_cycle_and_dual hφ i ξ t
    (consecutiveWeight n t j) (gTr * t / 2) hcycle ℓ hclass hlevel
  rw [← consecutive_shifted_vertex]
  nlinarith [congrArg (fun x : ℝ => x * t) hgenus]

/-- The two required torus representatives imply both final inequalities.
No identification of the entire torus spectrum is an input. -/
theorem estimates_of_two_cycles_and_dual
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D}
    {gCob gTr : ℝ} (hφ : F.Shifts G φ 0 gCob)
    (i : ι) (ξ : C.homology i) (n M m : ℕ) (hn : 2 ≤ n) (hm : 0 < m)
    (hcycle₁ : (F.weighted (2 / (m : ℝ))).RepresentedBelow i ξ
      (consecutiveWeight n (2 / (m : ℝ)) ⟨1, by omega⟩))
    (hcycle₂ : (F.weighted (2 / (m : ℝ))).RepresentedBelow i ξ
      (consecutiveWeight n (2 / (m : ℝ)) ⟨2, by omega⟩))
    (ℓ : D.X i →ₗ[R] R)
    (hclass : ∀ z : D.cycles i, D.homologyπ i z = homologyMap φ i ξ →
      ℓ (D.iCycles i z) = 1)
    (hlevel : ∀ s : ℝ, s < gTr * (2 / (m : ℝ)) / 2 →
      ∀ x ∈ (G.weighted (2 / (m : ℝ))).level s i, ℓ x = 0)
    (hgenus : (n : ℝ) * ((n : ℝ) + 1) / 2 - gTr + gCob =
      ((n : ℝ) + 1) - (M : ℝ)) :
    M ≤ m ∧ (n + 1) + M ≤ 3 * m := by
  have h₁ := consecutive_affine_upper_of_cycle_and_dual hφ i ξ n M
    (2 / (m : ℝ)) ⟨1, by omega⟩ hcycle₁ ℓ hclass hlevel hgenus
  have h₂ := consecutive_affine_upper_of_cycle_and_dual hφ i ξ n M
    (2 / (m : ℝ)) ⟨2, by omega⟩ hcycle₂ ℓ hclass hlevel hgenus
  apply Numerical.estimates_of_breakpoint_bounds (n + 1) M m
    (2 * (((n : ℝ) + 1) - (M : ℝ)) / (m : ℝ)) hm
  · simpa only [Fin.val_mk, Nat.cast_one, one_mul, mul_one, one_add_one_eq_two,
      Nat.cast_add, Nat.cast_one, mul_div_assoc, mul_comm] using h₁
  · convert h₂ using 1 <;> push_cast <;> ring
  · simp only [Nat.cast_add, Nat.cast_one, le_refl]

end OnLeConjecture.KnotFloer.Bifiltration
