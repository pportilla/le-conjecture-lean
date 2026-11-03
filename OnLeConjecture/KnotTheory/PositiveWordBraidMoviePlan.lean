/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordNormalForms
import all OnLeConjecture.KnotTheory.BraidPermutationCycles
import all OnLeConjecture.KnotTheory.PositivePermutationWords

/-! # Word-level plan of the braid grid movie

This module contains the purely combinatorial part of the braid grid movie of
job J12. Let `w` be a positive word on `S` strands whose permutation has `b`
cycles.

* `exists_coxeter_split` chooses a sublist `γ₀` of `w` with `S - b` distinct
  letters and a list `η` of the remaining `b - 1` generators, so that `γ₀ ++ η`
  contains every generator exactly once. Its existence uses the bound
  `S - #generators(w) ≤ b` of `strandCount_sub_generatorCount_le_cycleCount`.
* `reach_append_of_sublist` and `reach_append_delete` produce chains of single
  letter insertions and deletions after a fixed prefix, for any relation closed
  under reflexivity, composition and single steps. The number of steps is
  additive, so the chains count X switches when the relation is a grid movie.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory

open Equiv

/-- The distinct generators of a positive word are its letters. -/
theorem PositiveAdjacentWord.generatorIndices_toSigned {m : ℕ} (w : PositiveAdjacentWord m) :
    w.toSigned.generatorIndices = w.toFinset := by
  simp only [SignedAdjacentWord.generatorIndices, PositiveAdjacentWord.toSigned, List.map_map]
  congr 1
  exact List.map_id' w

/-- A permutation of a nonempty set of strands has at least one cycle. -/
theorem SignedAdjacentWord.one_le_cycleCount {m : ℕ} (hm : 1 ≤ m) (w : SignedAdjacentWord m) :
    1 ≤ w.cycleCount := by
  classical
  unfold SignedAdjacentWord.cycleCount
  have : Nonempty (Quotient (Perm.SameCycle.setoid w.permutation)) :=
    ⟨Quotient.mk _ ⟨0, by omega⟩⟩
  exact Fintype.card_pos

/-- **Coxeter split.** A positive word `w` on `S ≥ 1` strands whose permutation has `b`
cycles contains, as a sublist, a list `γ₀` of `S - b` distinct letters. Together with a
list `η` of the remaining `b - 1` generators, `γ₀ ++ η` contains every generator exactly
once. -/
theorem exists_coxeter_split {S : ℕ} (hS : 1 ≤ S) (w : PositiveAdjacentWord S) :
    ∃ γ₀ η : PositiveAdjacentWord S, γ₀.Sublist w ∧
      (γ₀ ++ η).Perm (List.finRange (S - 1)) ∧
      γ₀.length = S - w.toSigned.cycleCount ∧ η.length = w.toSigned.cycleCount - 1 := by
  classical
  set b := w.toSigned.cycleCount with hb
  have hL409 := SignedAdjacentWord.strandCount_sub_generatorCount_le_cycleCount w.toSigned
  rw [PositiveAdjacentWord.generatorIndices_toSigned, List.card_toFinset] at hL409
  have hb1 : 1 ≤ b := SignedAdjacentWord.one_le_cycleCount hS w.toSigned
  have hbS : b ≤ S := SignedAdjacentWord.cycleCount_le_strandCount w.toSigned
  set γ₀ := w.dedup.take (S - b) with hγ₀
  set η := (List.finRange (S - 1)).filter (fun i => i ∉ γ₀) with hη
  have hnd₀ : γ₀.Nodup := (List.nodup_dedup w).sublist (List.take_sublist _ _)
  have hlen₀ : γ₀.length = S - b := by
    rw [hγ₀, List.length_take]
    omega
  have hperm : (γ₀ ++ η).Perm (List.finRange (S - 1)) := by
    apply (List.perm_ext_iff_of_nodup _ (List.nodup_finRange _)).mpr
    · intro i
      simp only [List.mem_append, hη, List.mem_filter, List.mem_finRange, true_and,
        decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      tauto
    · rw [List.nodup_append]
      refine ⟨hnd₀, (List.nodup_finRange _).filter _, ?_⟩
      intro a ha c hc hac
      subst hac
      simp only [hη, List.mem_filter, decide_eq_true_eq] at hc
      exact hc.2 ha
  refine ⟨γ₀, η, (List.take_sublist _ _).trans (List.dedup_sublist w), hperm, hlen₀, ?_⟩
  have hl := hperm.length_eq
  rw [List.length_append, List.length_finRange, hlen₀] at hl
  omega

section Reach

variable {α : Type*} (Reach : List α → List α → ℕ → Prop)

/-- Single letter insertions after a fixed prefix `p` turn `p ++ γ` into `p ++ w`
whenever `γ` is a sublist of `w`, with `w.length - γ.length` steps. -/
theorem reach_append_of_sublist (p : List α)
    (refl : ∀ x, Reach x x 0)
    (trans : ∀ {x y z s t}, Reach x y s → Reach y z t → Reach x z (s + t))
    (ins : ∀ u v i, Reach (p ++ u ++ v) (p ++ u ++ i :: v) 1)
    {γ w : List α} (h : γ.Sublist w) :
    Reach (p ++ γ) (p ++ w) (w.length - γ.length) := by
  suffices H : ∀ u, Reach (p ++ u ++ γ) (p ++ u ++ w) (w.length - γ.length) by
    simpa using H []
  induction h with
  | slnil =>
    intro u
    simpa using refl (p ++ u)
  | @cons l₁ l₂ a h ih =>
    intro u
    have hle := h.length_le
    have h1 := trans (ih u) (ins u l₂ a)
    have he : l₂.length - l₁.length + 1 = (a :: l₂).length - l₁.length := by
      simp only [List.length_cons]
      omega
    rwa [he] at h1
  | @cons_cons l₁ l₂ a h ih =>
    intro u
    have h1 := ih (u ++ [a])
    simp only [List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_sub_add_right] at h1 ⊢
    exact h1

/-- Single letter deletions after a fixed prefix `p` remove a suffix `η`, with
`η.length` steps. -/
theorem reach_append_delete (p : List α)
    (refl : ∀ x, Reach x x 0)
    (trans : ∀ {x y z s t}, Reach x y s → Reach y z t → Reach x z (s + t))
    (del : ∀ v i, Reach (p ++ i :: v) (p ++ v) 1) (η : List α) :
    Reach (p ++ η) p η.length := by
  induction η with
  | nil => simpa using refl p
  | cons i η ih =>
    have h1 := trans (del η i) ih
    rwa [List.length_cons, Nat.add_comm]

end Reach

end OnLeConjecture.KnotTheory
