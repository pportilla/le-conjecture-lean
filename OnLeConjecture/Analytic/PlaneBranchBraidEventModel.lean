/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidEventWord
public import OnLeConjecture.KnotTheory.PositiveWordHeightPath
public import OnLeConjecture.KnotTheory.PositiveWordHeights
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Smooth height models of the actual positive braid events

An event word supplies the height inequalities needed by its smooth word path.
Relabeling by the initial sorting permutation keeps the original sheet labels
and the imaginary coordinates of those sheets at the event. The real endpoint
positions are the ranks in the initial and final sorting permutations.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace OnLeConjecture.Analytic

open KnotTheory

/-- The smooth event model in the original sheet labels, retaining the imaginary
coordinates of the given strands at the event time. -/
def planeBranchBraidEventModel {a : ℕ} (K : Fin a → ℝ → ℂ) (θ : ℝ)
    (before : Equiv.Perm (Fin a)) (w : PositiveAdjacentWord a) (k : Fin a) (t : ℝ) : ℂ :=
  positiveWordHeight w (fun j => (K (before j) θ).im) (before.symm k) t

/-- The height inequalities for the smooth word follow from the actual event's
recorded crossing pairs and transition permutation. -/
theorem IsPositiveBraidEventWord.letter_height_order
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (j : ℕ) (hj : j < w.length) :
    (K (before (positiveWordPrefix w j (adjacentLower w[j]))) θ).im <
      (K (before (positiveWordPrefix w j (adjacentUpper w[j]))) θ).im := by
  have hsplit : w = w.take j ++ w[j] :: w.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  simpa only [positiveWordPrefix, PositiveAdjacentWord.permutation] using
    positiveWord_letter_height_order before after w (fun k => (K k θ).im)
      h.1 h.2.2.2.1 (w.take j) (w.drop (j + 1)) w[j] hsplit

/-- Every letter exchanges two original sheets whose real coordinates coincide
at the assigned event. -/
theorem IsPositiveBraidEventWord.letter_real_eq
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (j : ℕ) (hj : j < w.length) :
    (K (before (positiveWordPrefix w j (adjacentLower w[j]))) θ).re =
      (K (before (positiveWordPrefix w j (adjacentUpper w[j]))) θ).re := by
  let u : PositiveAdjacentWord a := w.take j
  let v : PositiveAdjacentWord a := w.drop (j + 1)
  have hsplit : w = u ++ w[j] :: v := by
    dsimp [u, v]
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hp : (v.permutation.symm (adjacentLower w[j]),
      v.permutation.symm (adjacentUpper w[j])) ∈ w.crossingPairs := by
    rw [congrArg PositiveAdjacentWord.crossingPairs hsplit]
    exact PositiveAdjacentWord.crossingPairs_mem_append_right u (w[j] :: v)
      List.mem_cons_self
  have he := ((h.2.2.1 _ _).mp hp).2
  have hperm : w.permutation = u.permutation * (adjacentSwap w[j] * v.permutation) := by
    conv_lhs => rw [hsplit]
    change (u ++ w[j] :: v).toSigned.permutation = _
    rw [PositiveAdjacentWord.permutation_append]
    exact congrArg (fun q => u.permutation * q) (PositiveAdjacentWord.permutation_cons w[j] v)
  have hafter : after = before * (u.permutation * (adjacentSwap w[j] * v.permutation)) := by
    rw [← h.1]
    change before * w.permutation = _
    rw [hperm]
  rw [hafter] at he
  simp only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] at he
  rw [adjacentSwap.eq_def, Equiv.swap_apply_left, Equiv.swap_apply_right] at he
  exact he.symm

theorem planeBranchBraidEventModel_contDiff {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (k : Fin a) :
    ContDiff ℝ ∞ (planeBranchBraidEventModel K θ before w k) :=
  positiveWordHeight_contDiff w (fun j => (K (before j) θ).im) (before.symm k)

/-- The model keeps each original strand's event height for all times. -/
@[simp] theorem planeBranchBraidEventModel_im {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (k : Fin a) (t : ℝ) :
    (planeBranchBraidEventModel K θ before w k t).im = (K k θ).im := by
  simp [planeBranchBraidEventModel]

theorem IsPositiveBraidEventWord.model_injective
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w) (t : ℝ) :
    Function.Injective (fun k => planeBranchBraidEventModel K θ before w k t) :=
  (positiveWordHeight_injective w _ (fun j hj => (h.letter_height_order j hj).ne) t).comp
    before.symm.injective

@[simp] theorem planeBranchBraidEventModel_zero {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (k : Fin a) :
    planeBranchBraidEventModel K θ before w k 0 =
      ((before.symm k).val : ℂ) + ((K k θ).im : ℂ) * Complex.I := by
  simp [planeBranchBraidEventModel]

theorem planeBranchBraidEventModel_of_nonpos {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (k : Fin a) {t : ℝ} (ht : t ≤ 0) :
    planeBranchBraidEventModel K θ before w k t =
      ((before.symm k).val : ℂ) + ((K k θ).im : ℂ) * Complex.I := by
  rw [planeBranchBraidEventModel, positiveWordHeight_of_nonpos w _ _ ht]
  simp

/-- The final rank is exactly that of the event's final sorting permutation. -/
theorem IsPositiveBraidEventWord.model_of_length_le
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (k : Fin a) {t : ℝ} (ht : (w.length : ℝ) ≤ t) :
    planeBranchBraidEventModel K θ before w k t =
      ((after.symm k).val : ℂ) + ((K k θ).im : ℂ) * Complex.I := by
  have he : w.permutation.symm (before.symm k) = after.symm k := by
    apply after.injective
    have hp : before * w.permutation = after := h.1
    rw [← hp]
    simp
  simp only [planeBranchBraidEventModel, positiveWordHeight_of_length_le w _ _ ht,
    he, Equiv.apply_symm_apply]

/-- The event model has exactly the prefix-labeled crossings of its assigned word. -/
theorem planeBranchBraidEventModel_re_eq_iff {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) {k l : Fin a} (hkl : k ≠ l) (t : ℝ) :
    (planeBranchBraidEventModel K θ before w k t).re =
      (planeBranchBraidEventModel K θ before w l t).re ↔
      ∃ j : ℕ, ∃ hj : j < w.length,
        ((k = before (positiveWordPrefix w j (adjacentLower w[j])) ∧
          l = before (positiveWordPrefix w j (adjacentUpper w[j]))) ∨
         (k = before (positiveWordPrefix w j (adjacentUpper w[j])) ∧
          l = before (positiveWordPrefix w j (adjacentLower w[j])))) ∧
            t = (j : ℝ) + 1 / 2 := by
  simp only [planeBranchBraidEventModel,
    positiveWordHeight_re_eq_iff w _ (fun he => hkl (before.symm.injective he)),
    Equiv.symm_apply_eq]

/-- Model crossings correspond to coincident original sheets at the event. -/
theorem IsPositiveBraidEventWord.model_coincidence_original
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    {k l : Fin a} (hkl : k ≠ l) {t : ℝ}
    (ht : (planeBranchBraidEventModel K θ before w k t).re =
      (planeBranchBraidEventModel K θ before w l t).re) : (K k θ).re = (K l θ).re := by
  obtain ⟨j, hj, hp | hp, _⟩ :=
    (planeBranchBraidEventModel_re_eq_iff K θ before w hkl t).mp ht
  · rcases hp with ⟨rfl, rfl⟩
    exact h.letter_real_eq j hj
  · rcases hp with ⟨rfl, rfl⟩
    exact (h.letter_real_eq j hj).symm

/-- Positivity and transversality are proved for the model using the given
event word, without additional imaginary-height assumptions. -/
theorem IsPositiveBraidEventWord.model_positive_at_coincidence
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    {k l : Fin a} (hkl : k ≠ l) {t : ℝ}
    (ht : (planeBranchBraidEventModel K θ before w k t).re =
      (planeBranchBraidEventModel K θ before w l t).re) :
    0 < -deriv (fun s => (planeBranchBraidEventModel K θ before w k s -
      planeBranchBraidEventModel K θ before w l s).re) t *
      (planeBranchBraidEventModel K θ before w k t -
        planeBranchBraidEventModel K θ before w l t).im ∧
      deriv (fun s => (planeBranchBraidEventModel K θ before w k s -
        planeBranchBraidEventModel K θ before w l s).re) t ≠ 0 :=
  positiveWordHeight_positive_at_coincidence w _ (h.letter_height_order)
    (fun he => hkl (before.symm.injective he)) ht

end OnLeConjecture.Analytic
