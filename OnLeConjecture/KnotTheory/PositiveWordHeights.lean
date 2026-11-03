/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordSequence
import all OnLeConjecture.KnotTheory.BraidPermutationCycles
public import Mathlib.Data.Real.Basic

/-!
# Height orders for the letters of an event word

Event words record crossed pairs in final-position coordinates. The
smooth adjacent-generator paths use the labels at the prefix of each
letter. The lemma below proves the exact conversion between these two
conventions, without assuming that every positive word admits fixed heights.
-/

public section

namespace OnLeConjecture.KnotTheory

open Equiv

/-- Crossed pairs in a suffix retain their final-position labels. -/
theorem PositiveAdjacentWord.crossingPairs_mem_append_right {a : ℕ}
    (u v : PositiveAdjacentWord a) {p : Fin a × Fin a}
    (hp : p ∈ v.crossingPairs) : p ∈ (u ++ v).crossingPairs := by
  induction u with
  | nil => exact hp
  | cons i u ih =>
    exact List.mem_cons_of_mem _ ih

/-- The reversed final-position height order supplied by a positive event
block is exactly the lower-before-upper order required for the smooth
path of each letter. -/
theorem positiveWord_letter_height_order {a : ℕ}
    (before after : Perm (Fin a)) (w : PositiveAdjacentWord a) (y : Fin a → ℝ)
    (htransition : before * w.toSigned.permutation = after)
    (hy : ∀ x z, (x, z) ∈ w.crossingPairs → y (after z) < y (after x))
    (u v : PositiveAdjacentWord a) (i : Fin (a - 1)) (hw : w = u ++ i :: v) :
    y (before (u.toSigned.permutation (adjacentLower i))) <
      y (before (u.toSigned.permutation (adjacentUpper i))) := by
  have hp : (v.permutation.symm (adjacentLower i), v.permutation.symm (adjacentUpper i)) ∈
      w.crossingPairs := by
    rw [hw]
    exact PositiveAdjacentWord.crossingPairs_mem_append_right u (i :: v) (List.mem_cons_self)
  have h := hy _ _ hp
  have hperm : w.permutation = u.permutation * (adjacentSwap i * v.permutation) := by
    rw [hw]
    change (u ++ i :: v).toSigned.permutation = _
    rw [PositiveAdjacentWord.permutation_append]
    exact congrArg (fun q => u.permutation * q) (PositiveAdjacentWord.permutation_cons i v)
  change before * w.permutation = after at htransition
  have hafter : after = before * (u.permutation * (adjacentSwap i * v.permutation)) := by
    rw [← htransition, hperm]
  have hlo : after (v.permutation.symm (adjacentUpper i)) =
      before (u.permutation (adjacentLower i)) := by
    rw [hafter]
    simp only [Perm.mul_apply, apply_symm_apply]
    rw [adjacentSwap.eq_def, Equiv.swap_apply_right]
  have hhi : after (v.permutation.symm (adjacentLower i)) =
      before (u.permutation (adjacentUpper i)) := by
    rw [hafter]
    simp only [Perm.mul_apply, apply_symm_apply]
    rw [adjacentSwap.eq_def, Equiv.swap_apply_left]
  rw [hlo, hhi] at h
  exact h

end OnLeConjecture.KnotTheory
