/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesBraidData

/-! # The positive braid relation in signed words

For adjacent generators `i` and `j = i + 1` and arbitrary signed words `u` and `v`, every signed
word grid of `u σᵢ σⱼ σᵢ v` is related by grid moves to a signed word grid of `u σⱼ σᵢ σⱼ v`, and
conversely (`SignedGrid.fwd_braid`). The block is rotated to the front
(`SignedGrid.fwd_rotate`), and the seven cases of degenerate ranks are the window sequences of
`docs/route-n/J09-word-grid-moves.tex`, Proposition *braid*, checked in
`SignedWordGridMovesBraidData`. This is the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 7, *The three-letter Artin relation*), with the
window sequences of the J09 note. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

section Blocks

variable (i j : Fin (m - 1)) (hij : j.val = i.val + 1) (t : SignedAdjacentWord m)
  {flags : List Bool}

include hij in
theorem blockA_S (hfl : ∀ e ≤ 2, flagOf flags e = true ↔ ∃ k, ∃ hk : k < t.length,
      i.val + e = (t[k]).1.val ∨ i.val + e = (t[k]).1.val + 1) :
    BlockS 3 2 i.val [0, 1, 0] [true, true, true] [(i, 1), (j, 1), (i, 1)] t (flagOf flags) where
  kpos := by norm_num
  len := rfl
  val k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [hij]
  sgn k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [posB]
  offs_le k hk := by interval_cases k <;> simp
  fl_iff := hfl

include hij in
theorem blockB_S (hfl : ∀ e ≤ 2, flagOf flags e = true ↔ ∃ k, ∃ hk : k < t.length,
      i.val + e = (t[k]).1.val ∨ i.val + e = (t[k]).1.val + 1) :
    BlockS 3 2 i.val [1, 0, 1] [true, true, true] [(j, 1), (i, 1), (j, 1)] t (flagOf flags) where
  kpos := by norm_num
  len := rfl
  val k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [hij]
  sgn k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [posB]
  offs_le k hk := by interval_cases k <;> simp
  fl_iff := hfl

include hij in
theorem blockA_occ (s : ℕ) :
    (∃ k : Fin ([(i, 1), (j, 1), (i, 1)] ++ t).length, k.val < 3 ∧
      Occ ([(i, 1), (j, 1), (i, 1)] ++ t) s k) ↔ (i.val ≤ s ∧ s ≤ i.val + 2) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hk3, ho⟩
    simp only at hk3
    unfold Occ at ho
    interval_cases k <;> simp [hij] at ho <;> omega
  · rintro ⟨h1, h2⟩
    rcases (show s = i.val ∨ s = i.val + 1 ∨ s = i.val + 2 by omega) with e | e | e
    · exact ⟨⟨0, by simp⟩, by norm_num, by unfold Occ; simp [e]⟩
    · exact ⟨⟨0, by simp⟩, by norm_num, by unfold Occ; simp [e]⟩
    · exact ⟨⟨1, by simp⟩, by norm_num, by unfold Occ; simp [e, hij]⟩

include hij in
theorem blockB_occ (s : ℕ) :
    (∃ k : Fin ([(j, 1), (i, 1), (j, 1)] ++ t).length, k.val < 3 ∧
      Occ ([(j, 1), (i, 1), (j, 1)] ++ t) s k) ↔ (i.val ≤ s ∧ s ≤ i.val + 2) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hk3, ho⟩
    simp only at hk3
    unfold Occ at ho
    interval_cases k <;> simp [hij] at ho <;> omega
  · rintro ⟨h1, h2⟩
    rcases (show s = i.val ∨ s = i.val + 1 ∨ s = i.val + 2 by omega) with e | e | e
    · exact ⟨⟨1, by simp⟩, by norm_num, by unfold Occ; simp [e]⟩
    · exact ⟨⟨0, by simp⟩, by norm_num, by unfold Occ; simp [e, hij]⟩
    · exact ⟨⟨0, by simp⟩, by norm_num, by unfold Occ; simp [e, hij]⟩

include hij in
/-- The braid relation at the front of a word, from the finite data of one case. -/
theorem braid_front_of_data
    (hfl : ∀ e ≤ 2, flagOf flags e = true ↔ ∃ k, ∃ hk : k < t.length,
      i.val + e = (t[k]).1.val ∨ i.val + e = (t[k]).1.val + 1)
    {S₁ S₂ : WState} (hS₁ : InitOKS 3 S₁ [0, 1, 0] [true, true, true] flags)
    (hS₂ : InitOKS 3 S₂ [1, 0, 1] [true, true, true] flags)
    (hP : PairOKS S₁ [0, 1, 0] [true, true, true] S₂ [1, 0, 1] [true, true, true])
    {ms₁ ms₂ : List WMove} {F₁ F₂ : WState} (hr₁ : run S₁ ms₁ = some F₁)
    (hr₂ : run S₂ ms₂ = some F₂) {σ : List (ℕ × ℕ)} (hF : FinalOK F₁ F₂ σ) :
    Fwd ([(i, 1), (j, 1), (i, 1)] ++ t) ([(j, 1), (i, 1), (j, 1)] ++ t) ∧
      Fwd ([(j, 1), (i, 1), (j, 1)] ++ t) ([(i, 1), (j, 1), (i, 1)] ++ t) := by
  obtain ⟨G₁, G₂, h₁, h₂, hm⟩ := sgrids_of_windows (by norm_num) (blockA_S i j hij t hfl)
    (blockB_S i j hij t hfl)
    ⟨fun s => (blockA_occ i j hij t s).trans (blockB_occ i j hij t s).symm⟩
    S₁ S₂ hS₁ hS₂ hP hr₁ hr₂ hF
  exact fwd_of_grids h₁ h₂ hm

include hij in
/-- The braid relation at the front of a signed word. -/
theorem fwd_braid_front :
    Fwd ([(i, 1), (j, 1), (i, 1)] ++ t) ([(j, 1), (i, 1), (j, 1)] ++ t) ∧
      Fwd ([(j, 1), (i, 1), (j, 1)] ++ t) ([(i, 1), (j, 1), (i, 1)] ++ t) := by
  let f : ℕ → Bool := fun e => t.any (fun a => a.1.val == i.val + e || a.1.val + 1 == i.val + e)
  have hf : ∀ e, f e = true ↔ ∃ k, ∃ hk : k < t.length,
      i.val + e = (t[k]).1.val ∨ i.val + e = (t[k]).1.val + 1 := by
    intro e
    simp only [f, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨a, ha, h⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨k, hk, by omega⟩
    · rintro ⟨k, hk, h⟩
      exact ⟨t[k], List.getElem_mem hk, by omega⟩
  have key : ∀ b₀ b₁ b₂ : Bool, f 0 = b₀ → f 1 = b₁ → f 2 = b₂ →
      ∀ e ≤ 2, flagOf [b₀, b₁, b₂] e = true ↔ ∃ k, ∃ hk : k < t.length,
        i.val + e = (t[k]).1.val ∨ i.val + e = (t[k]).1.val + 1 := by
    rintro b₀ b₁ b₂ rfl rfl rfl e he
    interval_cases e <;> exact hf _
  rcases h0 : f 0 <;> rcases h1 : f 1 <;> rcases h2 : f 2
  · exact braid_front_of_data i j hij t (key _ _ _ h0 h1 h2) sinitA_d012 sinitB_d012 spair_d012
      runA_d012 runB_d012 final_d012
  · exact braid_front_of_data i j hij t (key _ _ _ h0 h1 h2) sinitA_d01 sinitB_d01 spair_d01
      runA_d01 runB_d01 final_d01
  · exfalso
    obtain ⟨k, hk, h⟩ := (hf 1).mp h1
    rcases (show (t[k]).1.val = i.val + 1 ∨ (t[k]).1.val = i.val by omega) with e | e
    · have : f 2 = true := (hf 2).mpr ⟨k, hk, by omega⟩
      rw [h2] at this; exact absurd this (by simp)
    · have : f 0 = true := (hf 0).mpr ⟨k, hk, by omega⟩
      rw [h0] at this; exact absurd this (by simp)
  · exact braid_front_of_data i j hij t (key _ _ _ h0 h1 h2) sinitA_d0 sinitB_d0 spair_d0
      runA_d0 runB_d0 final_d0
  · exact braid_front_of_data i j hij t (key _ _ _ h0 h1 h2) sinitA_d12 sinitB_d12 spair_d12
      runA_d12 runB_d12 final_d12
  · exact braid_front_of_data i j hij t (key _ _ _ h0 h1 h2) sinitA_d1 sinitB_d1 spair_d1
      runA_d1 runB_d1 final_d1
  · exact braid_front_of_data i j hij t (key _ _ _ h0 h1 h2) sinitA_d2 sinitB_d2 spair_d2
      runA_d2 runB_d2 final_d2
  · exact braid_front_of_data i j hij t (key _ _ _ h0 h1 h2) sinitA_n sinitB_n spair_n
      runA_n runB_n final_n

end Blocks

/-- A step inside a context, from the same step at the front of the rotated word. -/
theorem fwd_in_context (u v X Y : SignedAdjacentWord m)
    (h : ∀ t, Fwd (X ++ t) (Y ++ t)) : Fwd (u ++ X ++ v) (u ++ Y ++ v) := by
  have h1 : Fwd (u ++ X ++ v) (X ++ (v ++ u)) := by
    have := fwd_rotate u (X ++ v)
    rw [List.append_assoc] at this
    rw [List.append_assoc]
    exact this
  have h2 : Fwd (Y ++ (v ++ u)) (u ++ Y ++ v) := by
    have := fwd_rotate (Y ++ v) u
    rw [List.append_assoc] at this
    rw [List.append_assoc]
    exact this
  exact (h1.trans (h (v ++ u))).trans h2

/-- **The positive braid relation in signed words.** -/
theorem fwd_braid (u v : SignedAdjacentWord m) (i j : Fin (m - 1)) (hij : j.val = i.val + 1) :
    Fwd (u ++ (i, 1) :: (j, 1) :: (i, 1) :: v) (u ++ (j, 1) :: (i, 1) :: (j, 1) :: v) ∧
      Fwd (u ++ (j, 1) :: (i, 1) :: (j, 1) :: v) (u ++ (i, 1) :: (j, 1) :: (i, 1) :: v) := by
  have e1 : u ++ (i, 1) :: (j, 1) :: (i, 1) :: v = u ++ [(i, 1), (j, 1), (i, 1)] ++ v := by simp
  have e2 : u ++ (j, 1) :: (i, 1) :: (j, 1) :: v = u ++ [(j, 1), (i, 1), (j, 1)] ++ v := by simp
  rw [e1, e2]
  exact ⟨fwd_in_context u v _ _ (fun t => (fwd_braid_front i j hij t).1),
    fwd_in_context u v _ _ (fun t => (fwd_braid_front i j hij t).2)⟩

end OnLeConjecture.KnotTheory.SignedGrid
