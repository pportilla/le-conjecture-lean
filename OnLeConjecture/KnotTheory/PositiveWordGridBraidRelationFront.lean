/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationData

/-! # The braid relation on selected word grids, explicit form

`docs/route-n/J09-word-grid-moves.tex`, Proposition *braid*: for adjacent generators `i` and
`j = i + 1` and arbitrary positive words `u` and `v`, the selected grids of
`u ++ [i, j, i] ++ v` and `u ++ [j, i, j] ++ v` are related by grid moves
(`wordGrid_movesTo_braid'`).

The proof rotates the block to the front (`wordGrid_movesTo_append_comm`), splits into the
seven possible sets of ranks among `i, i + 1, i + 2` that do not occur in the rest of the word,
and applies `BraidWindow.wordGrid_movesTo_of_windows` to the window sequences of
`PositiveWordGridBraidRelationData` (`wordGrid_movesTo_braid_front`). The remaining set, where
`i + 1` occurs in the rest of the word but `i` and `i + 2` do not, is impossible. All results are
unconditional. This file does not import the `KnotFloer` layer.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-- Cyclic rotation of a word gives grid moves. -/
theorem wordGrid_movesTo_append_comm {m : ℕ} (x y : PositiveAdjacentWord m) :
    (wordGrid (x ++ y)).MovesTo (wordGrid (y ++ x)) := by
  induction y using List.reverseRecOn generalizing x with
  | nil =>
    rw [List.append_nil, List.nil_append]
  | append_singleton y a ih =>
    have h1 : (wordGrid (x ++ (y ++ [a]))).MovesTo (wordGrid (a :: (x ++ y))) := by
      rw [← List.append_assoc]; exact wordGrid_movesTo_rotate _ _
    have h2 := ih (a :: x)
    rw [List.append_assoc]
    exact h1.trans h2

namespace BraidWindow

section Blocks

variable {m : ℕ} (i j : Fin (m - 1)) (hij : (j : ℕ) = i + 1) (v : PositiveAdjacentWord m)
  {flags : List Bool}

include hij in
theorem blockA_hyp (hfl : ∀ e ≤ 2, flagOf flags e = true ↔ ∃ k, ∃ hk : k < v.length,
      i.val + e = (v[k]).val ∨ i.val + e = (v[k]).val + 1) :
    BlockHyp i [0, 1, 0] [i, j, i] v (flagOf flags) where
  len := rfl
  val k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [hij]
  offs_le k hk := by interval_cases k <;> simp
  room := by have := j.isLt; omega
  fl_iff := hfl

include hij in
theorem blockB_hyp (hfl : ∀ e ≤ 2, flagOf flags e = true ↔ ∃ k, ∃ hk : k < v.length,
      i.val + e = (v[k]).val ∨ i.val + e = (v[k]).val + 1) :
    BlockHyp i [1, 0, 1] [j, i, j] v (flagOf flags) where
  len := rfl
  val k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [hij]
  offs_le k hk := by interval_cases k <;> simp
  room := by have := j.isLt; omega
  fl_iff := hfl

include hij in
theorem blockA_ranks (r : Fin m) :
    (∃ k, ∃ h₁ : k < ([i, j, i] ++ v).length, k < 3 ∧
      (r = adjacentLower ([i, j, i] ++ v)[k] ∨ r = adjacentUpper ([i, j, i] ++ v)[k])) ↔
      (i.val ≤ r.val ∧ r.val ≤ i.val + 2) := by
  constructor
  · rintro ⟨k, hk, hk3, h⟩
    interval_cases k <;>
      simp [adjacentLower, adjacentUpper, Fin.ext_iff, hij] at h <;> omega
  · rintro ⟨h1, h2⟩
    rcases (show r.val = i.val ∨ r.val = i.val + 1 ∨ r.val = i.val + 2 by omega) with e | e | e
    · exact ⟨0, by simp, by norm_num, Or.inl (Fin.ext (by simp [e]))⟩
    · exact ⟨0, by simp, by norm_num, Or.inr (Fin.ext (by simp [e]))⟩
    · exact ⟨1, by simp, by norm_num, Or.inr (Fin.ext (by simp [e, hij]))⟩

include hij in
theorem blockB_ranks (r : Fin m) :
    (∃ k, ∃ h₁ : k < ([j, i, j] ++ v).length, k < 3 ∧
      (r = adjacentLower ([j, i, j] ++ v)[k] ∨ r = adjacentUpper ([j, i, j] ++ v)[k])) ↔
      (i.val ≤ r.val ∧ r.val ≤ i.val + 2) := by
  constructor
  · rintro ⟨k, hk, hk3, h⟩
    interval_cases k <;>
      simp [adjacentLower, adjacentUpper, Fin.ext_iff, hij] at h <;> omega
  · rintro ⟨h1, h2⟩
    rcases (show r.val = i.val ∨ r.val = i.val + 1 ∨ r.val = i.val + 2 by omega) with e | e | e
    · exact ⟨1, by simp, by norm_num, Or.inl (Fin.ext (by simp [e]))⟩
    · exact ⟨0, by simp, by norm_num, Or.inl (Fin.ext (by simp [e, hij]))⟩
    · exact ⟨0, by simp, by norm_num, Or.inr (Fin.ext (by simp [e, hij]))⟩

include hij in
/-- The braid relation at the front of a word, from the finite data of one case. -/
theorem braid_block_of_data
    (hfl : ∀ e ≤ 2, flagOf flags e = true ↔ ∃ k, ∃ hk : k < v.length,
      i.val + e = (v[k]).val ∨ i.val + e = (v[k]).val + 1)
    {S₁ S₂ : WState} (hS₁ : InitOK S₁ [0, 1, 0] flags) (hS₂ : InitOK S₂ [1, 0, 1] flags)
    (hP : PairOK S₁ [0, 1, 0] S₂ [1, 0, 1]) {ms₁ ms₂ : List WMove} {F₁ F₂ : WState}
    (hr₁ : run S₁ ms₁ = some F₁) (hr₂ : run S₂ ms₂ = some F₂) {σ : List (ℕ × ℕ)}
    (hF : FinalOK F₁ F₂ σ) :
    (wordGrid ([i, j, i] ++ v)).MovesTo (wordGrid ([j, i, j] ++ v)) :=
  wordGrid_movesTo_of_windows (blockA_hyp i j hij v hfl) (blockB_hyp i j hij v hfl)
    ⟨fun r => (blockA_ranks i j hij v r).trans (blockB_ranks i j hij v r).symm⟩
    S₁ S₂ hS₁ hS₂ hP hr₁ hr₂ hF

end Blocks

end BraidWindow

open BraidWindow in
/-- The braid relation at the front of a word. -/
theorem wordGrid_movesTo_braid_front {m : ℕ} (i j : Fin (m - 1)) (hij : (j : ℕ) = i + 1)
    (v : PositiveAdjacentWord m) :
    (wordGrid ([i, j, i] ++ v)).MovesTo (wordGrid ([j, i, j] ++ v)) := by
  let f : ℕ → Bool := fun e => v.any (fun a => a.val == i.val + e || a.val + 1 == i.val + e)
  have hf : ∀ e, f e = true ↔ ∃ k, ∃ hk : k < v.length,
      i.val + e = (v[k]).val ∨ i.val + e = (v[k]).val + 1 := by
    intro e
    simp only [f, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨a, ha, h⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨k, hk, by omega⟩
    · rintro ⟨k, hk, h⟩
      exact ⟨v[k], List.getElem_mem hk, by omega⟩
  have hfl : ∀ e ≤ 2, flagOf [f 0, f 1, f 2] e = true ↔ ∃ k, ∃ hk : k < v.length,
      i.val + e = (v[k]).val ∨ i.val + e = (v[k]).val + 1 := by
    intro e he
    interval_cases e <;> exact hf _
  have key : ∀ b₀ b₁ b₂ : Bool, f 0 = b₀ → f 1 = b₁ → f 2 = b₂ →
      ∀ e ≤ 2, flagOf [b₀, b₁, b₂] e = true ↔ ∃ k, ∃ hk : k < v.length,
        i.val + e = (v[k]).val ∨ i.val + e = (v[k]).val + 1 := by
    rintro b₀ b₁ b₂ rfl rfl rfl
    exact hfl
  rcases h0 : f 0 <;> rcases h1 : f 1 <;> rcases h2 : f 2
  · exact braid_block_of_data i j hij v (key _ _ _ h0 h1 h2) initA_d012 initB_d012 pair_d012
      runA_d012 runB_d012 final_d012
  · exact braid_block_of_data i j hij v (key _ _ _ h0 h1 h2) initA_d01 initB_d01 pair_d01
      runA_d01 runB_d01 final_d01
  · exfalso
    obtain ⟨k, hk, h⟩ := (hf 1).mp h1
    rcases (show (v[k]).val = i.val + 1 ∨ (v[k]).val = i.val by omega) with e | e
    · have : f 2 = true := (hf 2).mpr ⟨k, hk, by omega⟩
      rw [h2] at this; exact absurd this (by simp)
    · have : f 0 = true := (hf 0).mpr ⟨k, hk, by omega⟩
      rw [h0] at this; exact absurd this (by simp)
  · exact braid_block_of_data i j hij v (key _ _ _ h0 h1 h2) initA_d0 initB_d0 pair_d0
      runA_d0 runB_d0 final_d0
  · exact braid_block_of_data i j hij v (key _ _ _ h0 h1 h2) initA_d12 initB_d12 pair_d12
      runA_d12 runB_d12 final_d12
  · exact braid_block_of_data i j hij v (key _ _ _ h0 h1 h2) initA_d1 initB_d1 pair_d1
      runA_d1 runB_d1 final_d1
  · exact braid_block_of_data i j hij v (key _ _ _ h0 h1 h2) initA_d2 initB_d2 pair_d2
      runA_d2 runB_d2 final_d2
  · exact braid_block_of_data i j hij v (key _ _ _ h0 h1 h2) initA_n initB_n pair_n
      runA_n runB_n final_n

/-- **The braid relation on selected word grids**, `docs/route-n/J09-word-grid-moves.tex`,
Proposition *braid*, with the statement written out. -/
theorem wordGrid_movesTo_braid' {m : ℕ} (u v : PositiveAdjacentWord m) (i j : Fin (m - 1))
    (hij : (j : ℕ) = i + 1) :
    (wordGrid (u ++ [i, j, i] ++ v)).MovesTo (wordGrid (u ++ [j, i, j] ++ v)) := by
  have h1 : (wordGrid (u ++ [i, j, i] ++ v)).MovesTo (wordGrid ([i, j, i] ++ (v ++ u))) := by
    have := wordGrid_movesTo_append_comm u ([i, j, i] ++ v)
    rw [List.append_assoc] at this
    rw [List.append_assoc]
    exact this
  have h2 : (wordGrid ([j, i, j] ++ (v ++ u))).MovesTo (wordGrid (u ++ [j, i, j] ++ v)) := by
    have := wordGrid_movesTo_append_comm ([j, i, j] ++ v) u
    rw [List.append_assoc] at this
    rw [List.append_assoc]
    exact this
  exact (h1.trans (wordGrid_movesTo_braid_front i j hij (v ++ u))).trans h2

end OnLeConjecture.KnotTheory
