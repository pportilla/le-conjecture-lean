/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesCancel

/-! # Cancellation and insertion of inverse letters in signed words

The window data of the two cancellations `σ_r σ_r⁻¹` and `σ_r⁻¹ σ_r` (`SignedGrid.cancP`,
`SignedGrid.cancM`, checked by `decide`), and the resulting grid relation: if the ranks `r` and
`r + 1` occur in `u v`, every signed word grid of `u σ_r^e σ_r^{-e} v` is related by grid moves to
a signed word grid of `u v`, and conversely (`SignedGrid.fwd_cancel`). The move sequences were
found by a breadth-first search in the window model and are checked here by kernel evaluation;
the sequence for `σ_r σ_r⁻¹` follows the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 7, *Cancellation of consecutive inverse letters*). All
results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

/-! ### Window data -/

/-- The initial window state of `σ_r σ_r⁻¹`: labels `0, 3` for the half-integer arcs,
`1, 2` for the internal arcs of ranks `r` and `r + 1`, `20 + e` and `30 + e` for the incoming and
outgoing arcs of the rank `r + e`. -/
def cancP : WState :=
  ⟨[(0, 20), (1, 21), (2, 0), (3, 2), (31, 1), (30, 3)], [20, 1, 30, 0, 3, 2, 21, 31]⟩

/-- The move sequence of `σ_r σ_r⁻¹`. -/
def cancPMoves : List WMove :=
  [.c 4, .dO 3 2 2 3, .dX 2 3 3 0, .c 1, .dO 1 0 0 30, .r 1 30, .dX 1 2 1 21]

/-- The initial window state of `σ_r⁻¹ σ_r`. -/
def cancM : WState :=
  ⟨[(0, 21), (1, 20), (2, 0), (3, 2), (30, 1), (31, 3)], [20, 2, 30, 0, 3, 1, 21, 31]⟩

/-- The move sequence of `σ_r⁻¹ σ_r`. -/
def cancMMoves : List WMove :=
  [.r 2 30, .dX 2 3 2 0, .c 1, .dO 1 0 0 3, .r 3 1, .dO 2 1 1 30, .c 0, .dX 1 2 3 21]

theorem cancP_init : InitOKS 2 cancP [0, 0] [true, false] [true, true] := by decide

theorem cancP_run : run cancP cancPMoves = some Fbiv := by decide

theorem cancP_ok : CancelOK cancP [true, false] := by decide

theorem cancM_init : InitOKS 2 cancM [0, 0] [false, true] [true, true] := by decide

theorem cancM_run : run cancM cancMMoves = some Fbiv := by decide

theorem cancM_ok : CancelOK cancM [false, true] := by decide

/-! ### Ranks occurring in a word -/

/-- The rank `s` occurs in the signed word `x`. -/
def RankIn (x : SignedAdjacentWord m) (s : ℕ) : Prop := ∃ a ∈ x, s = a.1.val ∨ s = a.1.val + 1

theorem rankIn_iff (x : SignedAdjacentWord m) (s : ℕ) :
    RankIn x s ↔ ∃ k, ∃ hk : k < x.length, s = (x[k]).1.val ∨ s = (x[k]).1.val + 1 := by
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    exact ⟨k, hk, h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨x[k], List.getElem_mem hk, h⟩

theorem RankIn.mono {x y : SignedAdjacentWord m} {s : ℕ} (h : RankIn x s) (hxy : ∀ a ∈ x, a ∈ y) :
    RankIn y s := by
  obtain ⟨a, ha, h⟩ := h; exact ⟨a, hxy a ha, h⟩

/-! ### Cancellation at the front and in context -/

theorem block_cancel_S (r : Fin (m - 1)) (e : ℤˣ) (sg : List Bool) (t : SignedAdjacentWord m)
    (hsg : ∀ k (hk : k < 2), (([(r, e), (r, -e)] : SignedAdjacentWord m)[k]'(by simpa using hk)).2 = 1
      ↔ posB sg k = true)
    (h0 : RankIn t r.val) (h1 : RankIn t (r.val + 1)) :
    BlockS 2 1 r.val [0, 0] sg [(r, e), (r, -e)] t (flagOf [true, true]) where
  kpos := by norm_num
  len := rfl
  val k hk := by
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp
  sgn k hk := hsg k (by simpa using hk)
  offs_le k hk := by interval_cases k <;> simp
  fl_iff e' he' := by
    interval_cases e'
    · simp only [flagOf, List.getD_cons_zero, true_iff, Nat.add_zero]
      exact (rankIn_iff t _).mp h0
    · simp only [flagOf, List.getD_cons_succ, List.getD_cons_zero, true_iff]
      exact (rankIn_iff t _).mp h1

/-- **Cancellation at the front of a word.** -/
theorem fwd_cancel_front (r : Fin (m - 1)) (e : ℤˣ) (t : SignedAdjacentWord m)
    (h0 : RankIn t r.val) (h1 : RankIn t (r.val + 1)) :
    Fwd ([(r, e), (r, -e)] ++ t) t ∧ Fwd t ([(r, e), (r, -e)] ++ t) := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · have hB := block_cancel_S r 1 [true, false] t (fun k hk => by
      interval_cases k <;> simp [posB]) h0 h1
    obtain ⟨G, H, hG, hH, hm⟩ := cancel_front_of_data hB cancP cancP_init cancP_run cancP_ok
    exact fwd_of_grids hG hH hm
  · have hB := block_cancel_S r (-1) [false, true] t (fun k hk => by
      interval_cases k <;> simp [posB]) h0 h1
    obtain ⟨G, H, hG, hH, hm⟩ := cancel_front_of_data hB cancM cancM_init cancM_run cancM_ok
    exact fwd_of_grids hG hH hm

/-- **Cancellation and insertion of an inverse pair in a signed word.** -/
theorem fwd_cancel (u v : SignedAdjacentWord m) (r : Fin (m - 1)) (e : ℤˣ)
    (h0 : RankIn (u ++ v) r.val) (h1 : RankIn (u ++ v) (r.val + 1)) :
    Fwd (u ++ (r, e) :: (r, -e) :: v) (u ++ v) ∧ Fwd (u ++ v) (u ++ (r, e) :: (r, -e) :: v) := by
  have hperm : ∀ a, a ∈ u ++ v → a ∈ v ++ u := fun a ha => by
    simp only [List.mem_append] at ha ⊢; tauto
  have hf := fwd_cancel_front r e (v ++ u) (h0.mono hperm) (h1.mono hperm)
  have e1 : u ++ (r, e) :: (r, -e) :: v = u ++ ([(r, e), (r, -e)] ++ v) := by simp
  have r1 : Fwd (u ++ ([(r, e), (r, -e)] ++ v)) ([(r, e), (r, -e)] ++ (v ++ u)) := by
    have := fwd_rotate u ([(r, e), (r, -e)] ++ v)
    rw [List.append_assoc] at this; exact this
  have r2 : Fwd ([(r, e), (r, -e)] ++ (v ++ u)) (u ++ ([(r, e), (r, -e)] ++ v)) := by
    have := fwd_rotate ([(r, e), (r, -e)] ++ v) u
    rw [List.append_assoc] at this; exact this
  rw [e1]
  exact ⟨(r1.trans hf.1).trans (fwd_rotate v u), ((fwd_rotate u v).trans hf.2).trans r2⟩

end OnLeConjecture.KnotTheory.SignedGrid
