/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.BraidPermutationCycles
import all OnLeConjecture.KnotTheory.BraidPermutationCycles
public import OnLeConjecture.External.TauCeti.Data.Finset.Inversions
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Card

/-! # Positive adjacent words for finite permutations

A permutation maps final positions to initial positions. Crossed pairs are
recorded in final-position coordinates. They are exactly the pairs `x < y`
with `p y < p x`, each appearing once. Thus orders given by enumerations
`σ₋, σ₊` use `p = σ₋.symm * σ₊` and the sheet labels of a recorded pair are
`σ₊ x, σ₊ y`. The results concern words and permutations, not geometric closure.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory

open Equiv

abbrev adjacentLower {m : ℕ} (i : Fin (m - 1)) : Fin m := ⟨i.val, by omega⟩
abbrev adjacentUpper {m : ℕ} (i : Fin (m - 1)) : Fin m := ⟨i.val + 1, by omega⟩

theorem adjacentSwap_lt_iff {m : ℕ} (i : Fin (m - 1)) (x y : Fin m) :
    adjacentSwap i x < adjacentSwap i y ↔
      (x < y ∧ ¬(x = adjacentLower i ∧ y = adjacentUpper i)) ∨
        (x = adjacentUpper i ∧ y = adjacentLower i) := by
  simp only [adjacentSwap.eq_def, Equiv.swap_apply_def]
  split_ifs <;>
    simp_all [Fin.ext_iff, Fin.lt_def, adjacentLower, adjacentUpper, -Fin.val_fin_lt] <;> omega

/-- A nonidentity finite permutation has a descent in its inverse. -/
theorem exists_inverse_adjacent_descent {m : ℕ} (p : Perm (Fin m)) (hp : p ≠ 1) :
    ∃ i : Fin (m - 1), p.symm (adjacentUpper i) < p.symm (adjacentLower i) := by
  cases m with
  | zero => exact (hp (Subsingleton.elim _ _)).elim
  | succ n =>
    by_contra h
    push Not at h
    have hm : Monotone p.symm := Fin.monotone_iff_le_succ.mpr fun i => h i
    have he := (Equiv.Perm.monotone_iff p.symm).mp hm
    apply hp
    apply Equiv.ext
    intro x
    have hh := congrArg (fun q : Perm (Fin (n + 1)) => q (p x)) he
    simpa using hh.symm

/-- Swapping adjacent values at an inverse descent removes precisely one inversion. -/
theorem inversions_adjacentSwap_mul {m : ℕ} (p : Perm (Fin m))
    (i : Fin (m - 1))
    (hi : p.symm (adjacentUpper i) < p.symm (adjacentLower i)) :
    Finset.univ.inversions (adjacentSwap i * p) =
      (Finset.univ.inversions p).erase
        (p.symm (adjacentUpper i), p.symm (adjacentLower i)) := by
  classical
  ext v
  rcases v with ⟨x, y⟩
  simp only [Finset.mem_inversions, Finset.mem_univ, true_and,
    Finset.mem_erase, Perm.mul_apply, adjacentSwap_lt_iff]
  have hlo (z : Fin m) : p z = adjacentLower i ↔ z = p.symm (adjacentLower i) :=
    p.eq_symm_apply.symm
  have hhi (z : Fin m) : p z = adjacentUpper i ↔ z = p.symm (adjacentUpper i) :=
    p.eq_symm_apply.symm
  simp only [hlo, hhi]
  constructor
  · rintro ⟨hxy, hgood | hbad⟩
    · refine ⟨?_, hxy, hgood.1⟩
      intro he
      exact hgood.2 ⟨congrArg Prod.snd he, congrArg Prod.fst he⟩
    · rcases hbad with ⟨rfl, rfl⟩
      exact (not_lt_of_gt hi hxy).elim
  · rintro ⟨hne, hxy, hpy⟩
    refine ⟨hxy, Or.inl ⟨hpy, ?_⟩⟩
    rintro ⟨hy, hx⟩
    exact hne (Prod.ext hx hy)

theorem inverse_adjacent_descent_mem_inversions {m : ℕ} (p : Perm (Fin m))
    (i : Fin (m - 1))
    (hi : p.symm (adjacentUpper i) < p.symm (adjacentLower i)) :
    (p.symm (adjacentUpper i), p.symm (adjacentLower i)) ∈ Finset.univ.inversions p := by
  simp only [Finset.mem_inversions, Finset.mem_univ, true_and, apply_symm_apply]
  exact ⟨hi, by change i.val < i.val + 1; omega⟩

/-- Every letter represents a positive adjacent generator. -/
abbrev PositiveAdjacentWord (m : ℕ) := List (Fin (m - 1))

namespace PositiveAdjacentWord

def toSigned {m : ℕ} (w : PositiveAdjacentWord m) : SignedAdjacentWord m :=
  w.map fun i => (i, 1)

theorem toSigned_sign {m : ℕ} (w : PositiveAdjacentWord m)
    {letter : Fin (m - 1) × ℤˣ} (hletter : letter ∈ w.toSigned) : letter.2 = 1 := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hletter
  rfl

def permutation {m : ℕ} (w : PositiveAdjacentWord m) : Perm (Fin m) :=
  w.toSigned.permutation

@[simp] theorem permutation_nil (m : ℕ) : permutation ([] : PositiveAdjacentWord m) = 1 := by
  simp [permutation, toSigned]

@[simp] theorem permutation_cons {m : ℕ} (i : Fin (m - 1)) (w : PositiveAdjacentWord m) :
    permutation (i :: w) = adjacentSwap i * w.permutation := by
  simp [permutation, toSigned]

/-- At a letter followed by suffix `w`, adjacent positions are pulled back through
the suffix permutation. Hence both labels are final-position labels. -/
def crossingPairs {m : ℕ} : PositiveAdjacentWord m → List (Fin m × Fin m)
  | [] => []
  | i :: w => ((permutation w).symm (adjacentLower i),
      (permutation w).symm (adjacentUpper i)) :: crossingPairs w

@[simp] theorem crossingPairs_length {m : ℕ} (w : PositiveAdjacentWord m) :
    w.crossingPairs.length = w.length := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [crossingPairs, ih]

end PositiveAdjacentWord

/-- Every finite permutation is represented by a positive word whose recorded
strand pairs are precisely its inversions, without repetition. -/
theorem exists_positive_word_inversion_pairs {m : ℕ} (p : Perm (Fin m)) :
    ∃ w : PositiveAdjacentWord m, w.permutation = p ∧ w.crossingPairs.Nodup ∧
      w.crossingPairs.toFinset = Finset.univ.inversions p := by
  classical
  suffices ∀ k : ℕ, ∀ p : Perm (Fin m), (Finset.univ.inversions p).card = k →
      ∃ w : PositiveAdjacentWord m, w.permutation = p ∧ w.crossingPairs.Nodup ∧
        w.crossingPairs.toFinset = Finset.univ.inversions p from
    this _ p rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro p hpcount
    by_cases hp : p = 1
    · subst p
      refine ⟨[], by simp, by simp [PositiveAdjacentWord.crossingPairs], ?_⟩
      simp only [PositiveAdjacentWord.crossingPairs, List.toFinset_nil]
      exact (Finset.inversions_eq_empty_of_monotone (fun _ _ h => h) _).symm
    · obtain ⟨i, hi⟩ := exists_inverse_adjacent_descent p hp
      let q := adjacentSwap i * p
      have hmem := inverse_adjacent_descent_mem_inversions p i hi
      have hqset := inversions_adjacentSwap_mul p i hi
      have hlt : (Finset.univ.inversions q).card < k := by
        rw [← hpcount]
        change (Finset.univ.inversions (adjacentSwap i * p)).card < _
        rw [hqset]
        exact Finset.card_erase_lt_of_mem hmem
      obtain ⟨w, hw, hnodup, hset⟩ := ih _ hlt q rfl
      have hlo : q.symm (adjacentLower i) = p.symm (adjacentUpper i) := by
        apply q.injective
        simp [q, adjacentSwap.eq_def, adjacentLower, adjacentUpper]
      have hhi : q.symm (adjacentUpper i) = p.symm (adjacentLower i) := by
        apply q.injective
        simp [q, adjacentSwap.eq_def, adjacentLower, adjacentUpper]
      refine ⟨i :: w, ?_, ?_, ?_⟩
      · rw [PositiveAdjacentWord.permutation_cons, hw]
        simp [q, adjacentSwap.eq_def, ← mul_assoc]
      · simp only [PositiveAdjacentWord.crossingPairs, hw, hlo, hhi, List.nodup_cons]
        refine ⟨?_, hnodup⟩
        rw [← List.mem_toFinset, hset]
        change _ ∉ Finset.univ.inversions (adjacentSwap i * p)
        rw [hqset]
        exact Finset.notMem_erase _ _
      · simp only [PositiveAdjacentWord.crossingPairs, hw, hlo, hhi, List.toFinset_cons]
        rw [hset]
        change insert _ (Finset.univ.inversions (adjacentSwap i * p)) = _
        rw [hqset, Finset.insert_erase hmem]

/-- The explicit positive word has length equal to the inversion count, and every
unordered strand pair whose order reverses occurs exactly once. Pairs are written
in increasing final-position order. -/
theorem exists_positive_reduced_permutation_word {m : ℕ} (p : Perm (Fin m)) :
    ∃ w : PositiveAdjacentWord m, w.toSigned.permutation = p ∧
      w.length = (Finset.univ.inversions p).card ∧
      w.crossingPairs.Nodup ∧
      (∀ x y : Fin m, (x, y) ∈ w.crossingPairs ↔ x < y ∧ p y < p x) := by
  classical
  obtain ⟨w, hw, hnodup, hset⟩ := exists_positive_word_inversion_pairs p
  refine ⟨w, hw, ?_, hnodup, ?_⟩
  · rw [← hset, List.toFinset_card_of_nodup hnodup,
      PositiveAdjacentWord.crossingPairs_length]
  · intro x y
    rw [← List.mem_toFinset, hset]
    simp [Finset.mem_inversions]

/-- A transition between two position-to-label enumerations has a positive word.
Recorded pairs use the final enumeration, so their sheet labels are `after x`
and `after y`. The inequality compares their positions in the initial enumeration. -/
theorem exists_positive_order_transition_word {m : ℕ}
    (before after : Perm (Fin m)) :
    ∃ w : PositiveAdjacentWord m, before * w.toSigned.permutation = after ∧
      w.length = (Finset.univ.inversions (before.symm * after)).card ∧
      w.crossingPairs.Nodup ∧
      (∀ x y : Fin m, (x, y) ∈ w.crossingPairs ↔
        x < y ∧ before.symm (after y) < before.symm (after x)) := by
  obtain ⟨w, hw, hlength, hnodup, hpairs⟩ :=
    exists_positive_reduced_permutation_word (before.symm * after)
  refine ⟨w, ?_, hlength, hnodup, hpairs⟩
  rw [hw]
  change before * (before⁻¹ * after) = after
  exact mul_inv_cancel_left before after

end OnLeConjecture.KnotTheory
