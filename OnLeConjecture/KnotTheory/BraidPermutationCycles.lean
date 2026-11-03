/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Cycles of the permutation of a signed adjacent-generator word

An unused adjacent generator separates two intervals preserved by the word permutation.
Representatives immediately to the right of unused cuts, together with the first strand,
therefore belong to distinct permutation orbits. This proves the generator-count bound
used in the braid argument of `prop:braid` in `DMJ_submission/reduction_thm.tex`.

The cycle count here is the cardinality of Mathlib's `SameCycle` quotient, including
fixed points. No identification with components of a geometrically embedded link is assumed.
-/

public section

namespace OnLeConjecture.KnotTheory

open Equiv

/-- A signed word in the adjacent generators on `m` strands. -/
abbrev SignedAdjacentWord (m : ℕ) := List (Fin (m - 1) × ℤˣ)

/-- The transposition exchanging strand positions `i` and `i + 1`. -/
def adjacentSwap {m : ℕ} (i : Fin (m - 1)) : Perm (Fin m) :=
  Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩

namespace SignedAdjacentWord

/-- The strand permutation, with each signed generator interpreted as a signed power
of its adjacent transposition. -/
def permutation {m : ℕ} (w : SignedAdjacentWord m) : Perm (Fin m) :=
  (w.map fun a => adjacentSwap a.1 ^ (a.2 : ℤ)).prod

/-- The distinct adjacent-generator indices occurring in the word. -/
def generatorIndices {m : ℕ} (w : SignedAdjacentWord m) : Finset (Fin (m - 1)) :=
  (w.map Prod.fst).toFinset

/-- The number of permutation orbits, including singleton orbits of fixed strands. -/
noncomputable def cycleCount {m : ℕ} (w : SignedAdjacentWord m) : ℕ := by
  classical
  exact Fintype.card (Quotient (Perm.SameCycle.setoid w.permutation))

@[simp] theorem signed_adjacentSwap {m : ℕ} (i : Fin (m - 1)) (ε : ℤˣ) :
    adjacentSwap i ^ (ε : ℤ) = adjacentSwap i := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [adjacentSwap]

@[simp] theorem permutation_nil (m : ℕ) : permutation ([] : SignedAdjacentWord m) = 1 := by
  simp [permutation]

@[simp] theorem permutation_cons {m : ℕ} (a : Fin (m - 1) × ℤˣ)
    (w : SignedAdjacentWord m) :
    permutation (a :: w) = adjacentSwap a.1 * w.permutation := by
  simp [permutation]

@[simp] theorem generatorIndices_cons {m : ℕ} (a : Fin (m - 1) × ℤˣ)
    (w : SignedAdjacentWord m) :
    generatorIndices (a :: w) = insert a.1 w.generatorIndices := by
  simp [generatorIndices]

private theorem adjacentSwap_preserves_cut {m : ℕ} (i j : Fin (m - 1))
    (hji : j ≠ i) (x : Fin m) :
    (adjacentSwap j x).val ≤ i.val ↔ x.val ≤ i.val := by
  simp only [adjacentSwap, Equiv.swap_apply_def]
  split_ifs <;> simp_all only [Fin.ext_iff] <;> dsimp at * <;> omega

/-- A cut whose generator is absent from the word is preserved by its permutation. -/
theorem permutation_preserves_unused_cut {m : ℕ} (w : SignedAdjacentWord m)
    (i : Fin (m - 1)) (hi : i ∉ w.generatorIndices) (x : Fin m) :
    (w.permutation x).val ≤ i.val ↔ x.val ≤ i.val := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [generatorIndices_cons, Finset.mem_insert, not_or] at hi
    rw [permutation_cons, Perm.mul_apply,
      adjacentSwap_preserves_cut i a.1 (Ne.symm hi.1), ih hi.2]

/-- Two strands in the same permutation orbit lie on the same side of every unused cut. -/
theorem sameCycle_preserves_unused_cut {m : ℕ} (w : SignedAdjacentWord m)
    (i : Fin (m - 1)) (hi : i ∉ w.generatorIndices) {x y : Fin m}
    (hxy : w.permutation.SameCycle x y) :
    x.val ≤ i.val ↔ y.val ≤ i.val := by
  obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  symm
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, permutation_preserves_unused_cut w i hi, ih]

/-- The first strand and the strands immediately following unused cuts. -/
def boundaryRepresentatives {n : ℕ} (w : SignedAdjacentWord (n + 1)) : Finset (Fin (n + 1)) :=
  insert 0 (w.generatorIndicesᶜ.image Fin.succ)

private theorem not_sameCycle_of_lt_boundary {n : ℕ} (w : SignedAdjacentWord (n + 1))
    {x y : Fin (n + 1)} (hxy : x.val < y.val) (hy : y ∈ w.boundaryRepresentatives) :
    ¬w.permutation.SameCycle x y := by
  simp only [boundaryRepresentatives, Finset.mem_insert, Finset.mem_image,
    Finset.mem_compl] at hy
  rcases hy with rfl | ⟨i, hi, rfl⟩
  · simp at hxy
  · intro h
    have hh := (w.sameCycle_preserves_unused_cut i hi h).mp (by simpa using hxy)
    simp at hh

/-- The chosen representatives lie in pairwise distinct permutation orbits. -/
theorem boundaryRepresentatives_sameCycle_eq {n : ℕ} (w : SignedAdjacentWord (n + 1))
    {x y : Fin (n + 1)} (hx : x ∈ w.boundaryRepresentatives)
    (hy : y ∈ w.boundaryRepresentatives) (hxy : w.permutation.SameCycle x y) : x = y := by
  apply Fin.ext
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact False.elim (w.not_sameCycle_of_lt_boundary h hy hxy)
  · exact h
  · exact False.elim (w.not_sameCycle_of_lt_boundary h hx hxy.symm)

theorem card_boundaryRepresentatives {n : ℕ} (w : SignedAdjacentWord (n + 1)) :
    w.boundaryRepresentatives.card = n - w.generatorIndices.card + 1 := by
  rw [boundaryRepresentatives, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Fin.succ_injective n), Finset.card_compl]
  simp

/-- For a word on `n + 1` strands, the cycle count is at least the number of intervals
separated by unused adjacent generators. -/
theorem strandCount_sub_generatorCount_le_cycleCount_succ {n : ℕ}
    (w : SignedAdjacentWord (n + 1)) :
    n + 1 - w.generatorIndices.card ≤ w.cycleCount := by
  classical
  have hcard : w.boundaryRepresentatives.card ≤ w.cycleCount := by
    let f : w.boundaryRepresentatives → Quotient (Perm.SameCycle.setoid w.permutation) :=
      fun x => Quotient.mk _ x.val
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact w.boundaryRepresentatives_sameCycle_eq x.property y.property (Quotient.exact h)
    simpa [cycleCount] using Fintype.card_le_of_injective f hf
  rw [card_boundaryRepresentatives] at hcard
  have hle : w.generatorIndices.card ≤ n := card_finset_fin_le _
  omega

/-- The number of strands minus the number of distinct adjacent generators is at most
the number of cycles of the signed word's permutation. -/
theorem strandCount_sub_generatorCount_le_cycleCount {m : ℕ} (w : SignedAdjacentWord m) :
    m - w.generatorIndices.card ≤ w.cycleCount := by
  cases m with
  | zero => simp
  | succ n => exact w.strandCount_sub_generatorCount_le_cycleCount_succ

/-- Equivalently, the cycle count and distinct-generator count together cover the strands. -/
theorem strandCount_le_cycleCount_add_generatorCount {m : ℕ} (w : SignedAdjacentWord m) :
    m ≤ w.cycleCount + w.generatorIndices.card := by
  have h := w.strandCount_sub_generatorCount_le_cycleCount
  omega

/-- A permutation has at most one orbit per strand. -/
theorem cycleCount_le_strandCount {m : ℕ} (w : SignedAdjacentWord m) :
    w.cycleCount ≤ m := by
  classical
  simpa [cycleCount] using Fintype.card_le_of_surjective
    (Quotient.mk (Perm.SameCycle.setoid w.permutation)) Quotient.mk_surjective

/-- The empty word has one singleton orbit for every strand. -/
@[simp] theorem cycleCount_nil (m : ℕ) : cycleCount ([] : SignedAdjacentWord m) = m := by
  apply le_antisymm (cycleCount_le_strandCount _)
  simpa [generatorIndices] using
    strandCount_sub_generatorCount_le_cycleCount ([] : SignedAdjacentWord m)

/-- A nonempty set of strands in one permutation orbit has cycle count one. -/
theorem cycleCount_eq_one_of_sameCycle {m : ℕ} (w : SignedAdjacentWord m) (hm : 0 < m)
    (h : ∀ k l : Fin m, w.permutation.SameCycle k l) : w.cycleCount = 1 := by
  classical
  unfold cycleCount
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨Quotient.mk _ ⟨0, hm⟩, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | h k => exact Quotient.sound (h k ⟨0, hm⟩)

end SignedAdjacentWord

end OnLeConjecture.KnotTheory
