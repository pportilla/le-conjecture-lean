/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.BifilteredShift
public import OnLeConjecture.KnotFloer.ConsecutiveStaircase
import Mathlib.Tactic.LinearCombination

/-!
# The single filtered comparison needed at the critical breakpoint

Only a map from the torus complex to the transverse-knot complex is needed
for the upper bound. The minus sign in the definition of Upsilon reverses
the spectral-threshold inequality. Inverse maps and a two-sided cobordism
bound are not required for this deduction.

The statements retain the exact unproved inputs: an actual chain map with
its filtration shift, the selected homology classes and their finite
thresholds, the two invariant identifications, and the genus identity.
This file neither constructs geometric cobordism maps nor identifies an
abstract class invariant with a geometric knot invariant.
-/

@[expose] public section

universe u v w

namespace OnLeConjecture.KnotFloer.Bifiltration

open CategoryTheory HomologicalComplex Staircase

variable {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat.{v} R) c}

/-- One shifted map gives the required direction of the Upsilon bound. -/
theorem classUpsilon_upper_of_second_shift
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D} {g : ℝ}
    (hφ : F.Shifts G φ 0 g) (i : ι) (ξ : C.homology i)
    (t a b : ℝ) (ha : (F.weighted t).spectralThreshold i ξ = (a : EReal))
    (hb : (G.weighted t).spectralThreshold i (homologyMap φ i ξ) = (b : EReal)) :
    -2 * a ≤ -2 * b + t * g := by
  have h := RealFiltration.spectralThreshold_map_le_add (hφ.weighted t) i ξ
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  nlinarith

/-- The genus calculation and the two normalized-value identifications
turn a single actual filtered map into the precise staircase upper bound. -/
theorem consecutive_staircase_comparison_of_shifted_map
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D}
    {gCob gT gTr : ℝ} (hφ : F.Shifts G φ 0 gCob)
    (i : ι) (ξ : C.homology i) (n M m : ℕ) (a b : ℝ)
    (ha : (F.weighted (2 / (m : ℝ))).spectralThreshold i ξ = (a : EReal))
    (hb : (G.weighted (2 / (m : ℝ))).spectralThreshold i (homologyMap φ i ξ) =
      (b : EReal))
    (hT : consecutiveShiftedValue n (2 / (m : ℝ)) = -2 * a + gT * (2 / (m : ℝ)))
    (hTr : -2 * b + gTr * (2 / (m : ℝ)) = 0)
    (hgenus : gT - gTr + gCob = ((n : ℝ) + 1) - (M : ℝ)) :
    consecutiveShiftedValue n (2 / (m : ℝ)) ≤
      2 * (((n : ℝ) + 1) - (M : ℝ)) / (m : ℝ) := by
  have h := classUpsilon_upper_of_second_shift hφ i ξ (2 / (m : ℝ)) a b ha hb
  rw [hT, ← hgenus]
  calc
    -2 * a + gT * (2 / (m : ℝ)) ≤
        (-2 * b + (2 / (m : ℝ)) * gCob) + gT * (2 / (m : ℝ)) :=
      by linarith
    _ = 2 * (gT - gTr + gCob) / (m : ℝ) := by
      linear_combination hTr

/-- The exact map and invariant identifications already imply both final
numerical estimates. This is an algebraic implication, not a construction
of a geometric knot invariant or of its cobordism map. -/
theorem estimates_of_shifted_map_and_staircase_identifications
    {F : Bifiltration C} {G : Bifiltration D} {φ : C ⟶ D}
    {gCob gT gTr : ℝ} (hφ : F.Shifts G φ 0 gCob)
    (i : ι) (ξ : C.homology i) (n M m : ℕ) (hn : 2 ≤ n) (hm : 0 < m)
    (a b : ℝ)
    (ha : (F.weighted (2 / (m : ℝ))).spectralThreshold i ξ = (a : EReal))
    (hb : (G.weighted (2 / (m : ℝ))).spectralThreshold i (homologyMap φ i ξ) =
      (b : EReal))
    (hT : consecutiveShiftedValue n (2 / (m : ℝ)) = -2 * a + gT * (2 / (m : ℝ)))
    (hTr : -2 * b + gTr * (2 / (m : ℝ)) = 0)
    (hgenus : gT - gTr + gCob = ((n : ℝ) + 1) - (M : ℝ)) :
    M ≤ m ∧ (n + 1) + M ≤ 3 * m :=
  estimates_of_consecutive_staircase_comparison n M m hn hm
    (consecutive_staircase_comparison_of_shifted_map hφ i ξ n M m a b ha hb hT hTr hgenus)

end OnLeConjecture.KnotFloer.Bifiltration
