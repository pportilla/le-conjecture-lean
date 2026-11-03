/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.TorusWordGridHybrid

/-! # Absorption of one block

`docs/route-n/J11-torus-word-grid.tex`, Lemma *absorption*: the hybrid grid `H_{a,k}(β^{J+1})` is
related by grid moves to `H_{a,k+1}(β^J)`, with `a = A + 1` (`IsHybrid.exists_absorb`).

The proof follows the written one. The block reduction (`exists_blockReduction`) removes the
descending columns and the middle arcs of the first block. In stage 3 (`Stage3`,
`Stage3.exists_step`) the columns `B_r = (0, A - 1 - r, 2)` are merged into the `R`-columns
`ρ (N - 1 - r)` by `O`-destabilizations, for `r = 0, …, A - 1`. Then the arcs leaving the last
occurrences in the first block are exchanged with those of the last block
(`LabeledGrid.exists_swapOuts`), and the labels are renamed. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

theorem outArc_zero (A b : ℕ) : outArc A b 0 = arc b (A - 1) 1 := by simp [outArc]

theorem outArc_pos {A b r : ℕ} (hr : r ≠ 0) : outArc A b r = arc b (A - r) 2 := by
  simp [outArc, hr]

/-- The rows present during stage 3, after `s` merges. -/
def StRow (A k J s : ℕ) (x : TorusRow) : Prop :=
  x = rRow 0 ∨ (∃ t, A + 2 ≤ t ∧ t < A + 1 + k ∧ x = rRow t) ∨ (∃ r, s ≤ r ∧ r ≤ A ∧ x = iRow r) ∨
    (∃ r ≤ A, x = outArc A 0 r) ∨ ∃ b, 1 ≤ b ∧ b < J + 1 ∧ ∃ t < A, ∃ c : Fin 3, x = arc b t c

/-- The state after `s` merges of stage 3 in the absorption of the first of `J + 1` blocks. -/
structure Stage3 {n : ℕ} (A k J s : ℕ) (G : LabeledGrid n TorusCol TorusRow) : Prop where
  cols : G.cols = rCols (A + 1 + k) ++ blockBs 0 (A - s) ++ [cor 0 (A - 1) 1] ++ wordCols A 1 J
  O_r : ∀ i < A + 1 + k, G.O (rCol i) =
    if A + 1 + k ≤ i + s then arc 0 (i - k - 1) 2 else winO A (oRes A k i)
  O_c : ∀ b t c, cor b t c ∈ G.cols → G.O (cor b t c) = arc b t c
  X_r : ∀ i < A + 1 + k, G.X (rCol i) = winX A (J + 1) (xRes A k i)
  X_B : ∀ t < A - s, G.X (cor 0 t 2) = iRow (A - 1 - t)
  X_V : G.X (cor 0 (A - 1) 1) = iRow A
  X_w : ∀ c ∈ wordCols A 1 J, G.X c = hybX A k (J + 1) c
  rows_iff : ∀ x, x ∈ G.rows ↔ StRow A k J s x
  sorted : G.rows.Pairwise (hybLtS A (J + 1) 0)

theorem hybLtS_lvT_le {A J s : ℕ} {x y : TorusRow} (h : hybLtS A J s x y) : lvT A x ≤ lvT A y := by
  unfold hybLtS at h; omega

theorem IsHybrid.mem_cols_cor {n A k J b t : ℕ} {c : Fin 3} {G : LabeledGrid n TorusCol TorusRow}
    (hG : IsHybrid A k J G) (hb : b < J) (ht : t < A) : cor b t c ∈ G.cols := by
  rw [hG.cols, hybCols, List.mem_append, mem_wordCols]
  exact Or.inr ⟨b, by omega, by omega, t, ht, c, rfl⟩

theorem IsHybrid.mem_cols_rCol {n A k J i : ℕ} {G : LabeledGrid n TorusCol TorusRow}
    (hG : IsHybrid A k J G) (hi : i < A + 1 + k) : rCol i ∈ G.cols := by
  rw [hG.cols, hybCols, List.mem_append, mem_rCols]
  exact Or.inl ⟨i, hi, rfl⟩

/-- The first block of a hybrid grid is in block position. -/
theorem IsHybrid.blockData {n A k J : ℕ} {G : LabeledGrid n TorusCol TorusRow}
    (hG : IsHybrid A k (J + 1) G) :
    BlockData A G iRow (lvT A) (rCols (A + 1 + k)) (wordCols A 1 J) where
  cols := by rw [hG.cols, hybCols, wordCols_succ, blockCols_zero_eq, List.append_assoc]
  O_cor t ht c := by rw [hG.O_eq _ (hG.mem_cols_cor (by omega) ht), hybO_cor]
  X_cor0 t ht := by rw [hG.X_eq _ (hG.mem_cols_cor (by omega) ht), hybX_cor]; simp [corX, inRow]
  X_cor1 t ht := by
    rw [hG.X_eq _ (hG.mem_cols_cor (by omega) ht), hybX_cor]
    simp [corX, inRow]
  X_cor2 t ht := by rw [hG.X_eq _ (hG.mem_cols_cor (by omega) ht), hybX_cor]; simp [corX]
  inc_ne r t c := by simp [iRow, arc]
  sorted := hG.sorted.imp hybLtS_lvT_le
  lv_arc0 t _ := by simp [arcLv]
  lv_arc1 t _ := by simp [arcLv]
  lv_arc2 t _ := by simp [arcLv]
  lv_inc r _ := by simp

theorem pairwise_mid {α : Type*} {R : α → α → Prop} {l m₁ mid m₂ : List α} {x y z : α}
    (hl : l.Pairwise R) (h : l = m₁ ++ x :: (mid ++ y :: m₂)) (hz : z ∈ mid) : R x z ∧ R z y := by
  subst h
  rw [List.pairwise_append, List.pairwise_cons, List.pairwise_append] at hl
  exact ⟨hl.2.1.1 z (by simp [hz]), hl.2.1.2.2.2 z hz y (by simp)⟩

theorem blockBs_succ' {A : ℕ} (h : 1 ≤ A) : blockBs 0 A = blockBs 0 (A - 1) ++ [cor 0 (A - 1) 2] := by
  conv_lhs => rw [show A = A - 1 + 1 by omega]
  rw [blockBs_succ, zero_add]

theorem lvT_iRow_lt_outArc {A r : ℕ} (hA : 1 ≤ A) (hr : r < A) :
    lvT A (iRow r) < lvT A (outArc A 0 (r + 1)) := by
  rw [lvT_outArc hA (by omega)]; simp; omega

/-- Start of stage 3: the block reduction, and the column `V` moved to the right of `B_0`. -/
theorem IsHybrid.exists_stage3_start {n A k J : ℕ} (hA : 1 ≤ A)
    {G : LabeledGrid n TorusCol TorusRow} (hG : IsHybrid A k (J + 1) G) :
    ∃ (m : ℕ) (G' : LabeledGrid m TorusCol TorusRow), m + (2 * A - 1) = n ∧
      Stage3 A k J 0 G' ∧ G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨m, G₂, hm, hc₂, hsub₂, hmem₂, hO₂, hXV₂, hXB₂, hXo₂, hmv₂⟩ :=
    exists_blockReduction G hG.blockData hA
  have hsort₂ : G₂.rows.Pairwise (hybLtS A (J + 1) 0) := hG.sorted.sublist hsub₂
  have hlv₂ : G₂.rows.Pairwise (fun a b => lvT A a ≤ lvT A b) := hsort₂.imp hybLtS_lvT_le
  have hrow : ∀ x, x ∈ G₂.rows ↔ StRow A k J 0 x := by
    intro x
    rw [hmem₂, hG.rows_iff]
    constructor
    · rintro ⟨h | h | h | ⟨b, hb, t, ht, c, rfl⟩, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · obtain ⟨r, hr, rfl⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨r, Nat.zero_le _, hr, rfl⟩))
      · by_cases hb0 : b = 0
        · subst hb0
          have hc := c.isLt
          right; right; right; left
          rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with hc0 | hc1 | hc2
          · exact absurd (by rw [show c = 0 from Fin.ext hc0]) (h2 t ht)
          · by_cases htA : t < A - 1
            · exact absurd (by rw [show c = 1 from Fin.ext hc1]) (h1 t htA)
            · refine ⟨0, by omega, ?_⟩
              rw [outArc_zero, show c = 1 from Fin.ext hc1, show t = A - 1 by omega]
          · refine ⟨A - t, by omega, ?_⟩
            rw [outArc_pos (by omega), show c = 2 from Fin.ext hc2, show A - (A - t) = t by omega]
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b, by omega, hb, t, ht, c, rfl⟩)))
    · rintro (rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, -, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨b, hb1, hb, t, ht, c, rfl⟩)
      · exact ⟨Or.inl rfl, fun s _ h => arc_ne_rRow _ _ _ _ h.symm,
          fun s _ h => arc_ne_rRow _ _ _ _ h.symm⟩
      · exact ⟨Or.inr (Or.inl ⟨t, h1, h2, rfl⟩), fun s _ h => arc_ne_rRow _ _ _ _ h.symm,
          fun s _ h => arc_ne_rRow _ _ _ _ h.symm⟩
      · exact ⟨Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)), fun s _ h => arc_ne_iRow _ _ _ _ h.symm,
          fun s _ h => arc_ne_iRow _ _ _ _ h.symm⟩
      · by_cases hr0 : r = 0
        · subst hr0
          rw [outArc_zero]
          refine ⟨Or.inr (Or.inr (Or.inr ⟨0, by omega, A - 1, by omega, 1, rfl⟩)), ?_, ?_⟩
          · intro s hs h; simp only [arc_inj_iff] at h; omega
          · intro s hs h; simp only [arc_inj_iff] at h; exact absurd h.2.2 (by decide)
        · rw [outArc_pos hr0]
          refine ⟨Or.inr (Or.inr (Or.inr ⟨0, by omega, A - r, by omega, 2, rfl⟩)), ?_, ?_⟩
          · intro s hs h; simp only [arc_inj_iff] at h; exact absurd h.2.2 (by decide)
          · intro s hs h; simp only [arc_inj_iff] at h; exact absurd h.2.2 (by decide)
      · refine ⟨Or.inr (Or.inr (Or.inr ⟨b, hb, t, ht, c, rfl⟩)), ?_, ?_⟩
        · intro s hs h; simp only [arc_inj_iff] at h; omega
        · intro s hs h; simp only [arc_inj_iff] at h; omega
  have hV : cor 0 (A - 1) 1 ∈ G.cols := hG.mem_cols_cor (by omega) (by omega)
  have hB0 : cor 0 (A - 1) 2 ∈ G.cols := hG.mem_cols_cor (by omega) (by omega)
  have OV : G₂.O (cor 0 (A - 1) 1) = outArc A 0 0 := by
    rw [hO₂, hG.O_eq _ hV, hybO_cor, outArc_zero]
  have OB0 : G₂.O (cor 0 (A - 1) 2) = outArc A 0 1 := by
    rw [hO₂, hG.O_eq _ hB0, hybO_cor, outArc_pos one_ne_zero]
  have XB0 : G₂.X (cor 0 (A - 1) 2) = iRow 0 := by
    rw [hXB₂ (A - 1) (by omega), show A - 1 - (A - 1) = 0 by omega]
  have r1 : outArc A 0 0 ∈ G₂.rows :=
    (hrow _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨0, by omega, rfl⟩))))
  have r2 : outArc A 0 1 ∈ G₂.rows :=
    (hrow _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨1, by omega, rfl⟩))))
  have r3 : iRow 0 ∈ G₂.rows := (hrow _).mpr (Or.inr (Or.inr (Or.inl ⟨0, le_rfl, by omega, rfl⟩)))
  have r4 : iRow A ∈ G₂.rows := (hrow _).mpr (Or.inr (Or.inr (Or.inl ⟨A, by omega, le_rfl, rfl⟩)))
  have l1 := lvT_outArc (b := 0) (r := 0) hA (by omega)
  have l2 := lvT_outArc (b := 0) (r := 1) hA (by omega)
  obtain ⟨G₃, hc₃, hr₃, hO₃, hX₃, hmv₃⟩ := G₂.exists_moveColRight
    (l₁ := rCols (A + 1 + k) ++ blockBs 0 (A - 1)) (c := cor 0 (A - 1) 1)
    (mid := [cor 0 (A - 1) 2]) (l₂ := wordCols A 1 J) (by rw [hc₂]; simp) (by
      intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      subst hd
      unfold LabeledGrid.ColsNonint
      rw [OV, hXV₂, OB0, XB0]
      exact nonintN_nested_of_lt (idxOf_lt_of_level hlv₂ r1 r3 (by simp; omega))
        (idxOf_lt_of_level hlv₂ r3 r2 (by simp; omega))
        (idxOf_lt_of_level hlv₂ r2 r4 (by simp; omega)))
  -- columns of `G₃` are columns of `G`
  have hsubc : ∀ x ∈ G₃.cols, x ∈ G.cols := by
    intro x hx
    rw [hc₃] at hx
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with ((hx | hx) | hx) | hx | hx
    · rw [hG.cols, hybCols]; exact List.mem_append_left _ hx
    · obtain ⟨s, -, hs, rfl⟩ := mem_blockBs.mp hx; exact hG.mem_cols_cor (by omega) (by omega)
    · subst hx; exact hB0
    · subst hx; exact hV
    · rw [hG.cols, hybCols, wordCols_succ]; simp [hx]
  have hnotB : ∀ x ∈ wordCols A 1 J, x ≠ cor 0 (A - 1) 1 ∧ ∀ s < A, x ≠ cor 0 s 2 := by
    intro x hx
    obtain ⟨b, hb, -, t, -, c, rfl⟩ := mem_wordCols.mp hx
    exact ⟨fun h => by simp only [cor_inj_iff] at h; omega,
      fun s _ h => by simp only [cor_inj_iff] at h; omega⟩
  have hc₂m : ∀ x ∈ G₃.cols, x ∈ G₂.cols := fun x hx => by
    rw [hc₂]; rw [hc₃] at hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto
  refine ⟨m, G₃, hm, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hmv₂.trans hmv₃⟩
  · rw [hc₃, Nat.sub_zero, blockBs_succ' hA]; simp
  · intro i hi
    rw [if_neg (by omega), hO₃, hO₂, hG.O_eq _ (hG.mem_cols_rCol hi), hybO_rCol]
  · intro b t c hc
    rw [hO₃, hO₂, hG.O_eq _ (hsubc _ hc), hybO_cor]
  · intro i hi
    have hm' : rCol i ∈ G₃.cols := by rw [hc₃]; simp [mem_rCols, hi]
    rw [hX₃, hXo₂ _ (hc₂m _ hm') (by simp [rCol, cor]) (fun s _ => by simp [rCol, cor]),
      hG.X_eq _ (hG.mem_cols_rCol hi), hybX_rCol]
  · intro t ht; rw [hX₃, hXB₂ t (by omega)]
  · rw [hX₃, hXV₂]
  · intro c hc
    have hm' : c ∈ G₃.cols := by rw [hc₃]; simp [hc]
    rw [hX₃, hXo₂ _ (hc₂m _ hm') (hnotB c hc).1 (hnotB c hc).2, hG.X_eq _ (hsubc _ hm')]
  · intro x; rw [hr₃]; exact hrow x
  · rw [hr₃]; exact hsort₂

/-! ### Stage 3 -/

namespace Stage3

variable {n A k J s : ℕ} {G : LabeledGrid n TorusCol TorusRow}

/-- The columns before the blocks `1, …, J`. -/
def pre (A k s : ℕ) : List TorusCol :=
  rCols (A + 1 + k) ++ blockBs 0 (A - s) ++ [cor 0 (A - 1) 1]

theorem cols_eq (hG : Stage3 A k J s G) : G.cols = pre A k s ++ wordCols A 1 J := by
  rw [hG.cols, pre]

theorem O_pre (hG : Stage3 A k J s G) {d : TorusCol} (hd : d ∈ pre A k s) :
    (∃ t, G.O d = rRow t) ∨ (∃ r, G.O d = iRow r) ∨ ∃ t c, G.O d = arc 0 t c := by
  have hdm : d ∈ G.cols := by rw [hG.cols_eq]; exact List.mem_append_left _ hd
  simp only [pre, List.mem_append, List.mem_singleton] at hd
  rcases hd with (hd | hd) | rfl
  · obtain ⟨i, hi, rfl⟩ := mem_rCols.mp hd
    rw [hG.O_r i hi]
    split_ifs
    · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
    · unfold winO; split_ifs
      · exact Or.inr (Or.inl ⟨_, rfl⟩)
      · exact Or.inl ⟨_, rfl⟩
  · obtain ⟨t, -, -, rfl⟩ := mem_blockBs.mp hd
    exact Or.inr (Or.inr ⟨_, _, hG.O_c _ _ _ hdm⟩)
  · exact Or.inr (Or.inr ⟨_, _, hG.O_c _ _ _ hdm⟩)

theorem X_pre (hG : Stage3 A k J s G) {d : TorusCol} (hd : d ∈ pre A k s) :
    (∃ t, G.X d = rRow t) ∨ (∃ r, G.X d = iRow r) ∨ ∃ r, G.X d = outArc A J r := by
  simp only [pre, List.mem_append, List.mem_singleton] at hd
  rcases hd with (hd | hd) | rfl
  · obtain ⟨i, hi, rfl⟩ := mem_rCols.mp hd
    rw [hG.X_r i hi]
    unfold winX; split_ifs
    · exact Or.inr (Or.inr ⟨xRes A k i - 1, by simp [inRow]⟩)
    · exact Or.inl ⟨_, rfl⟩
  · obtain ⟨t, -, ht, rfl⟩ := mem_blockBs.mp hd
    exact Or.inr (Or.inl ⟨_, hG.X_B t (by omega)⟩)
  · exact Or.inr (Or.inl ⟨_, hG.X_V⟩)

theorem O_word (hG : Stage3 A k J s G) {d : TorusCol} (hd : d ∈ wordCols A 1 J) :
    ∃ b t c, 1 ≤ b ∧ G.O d = arc b t c := by
  have hdm : d ∈ G.cols := by rw [hG.cols_eq]; exact List.mem_append_right _ hd
  obtain ⟨b, hb, -, t, -, c, rfl⟩ := mem_wordCols.mp hd
  exact ⟨b, t, c, hb, hG.O_c _ _ _ hdm⟩

theorem X_word (hG : Stage3 A k J s G) {d : TorusCol} (hd : d ∈ wordCols A 1 J) :
    ∃ b t c, G.X d = arc b t c := by
  rw [hG.X_w d hd]
  obtain ⟨b, hb, -, t, -, c, rfl⟩ := mem_wordCols.mp hd
  rw [hybX_cor]
  unfold corX inRow outArc
  split_ifs <;> first | exact ⟨_, _, _, rfl⟩ | omega

theorem mem_word_of_not_pre (hG : Stage3 A k J s G) {d : TorusCol} (hd : d ∈ G.cols)
    (h : d ∉ pre A k s) : d ∈ wordCols A 1 J := by
  rw [hG.cols_eq, List.mem_append] at hd
  exact hd.resolve_left h

/-- A row `ι r` does not interleave an arc of a later block other than a last outgoing arc of the
last block. -/
theorem rowsNonint_iRow (hG : Stage3 A k J s G) (r : ℕ) {b t : ℕ} {c : Fin 3} (hb : 1 ≤ b)
    (hw : ∀ r', arc b t c ≠ outArc A J r') : G.RowsNonint (iRow r) (arc b t c) := by
  intro a a' e e' ha ha' he he' hOa hXa hOe hXe
  have h1 : a ∈ pre A k s := by
    by_contra hn
    obtain ⟨_, _, _, -, h⟩ := hG.O_word (hG.mem_word_of_not_pre ha hn)
    rw [hOa] at h; exact arc_ne_iRow _ _ _ _ h.symm
  have h2 : a' ∈ pre A k s := by
    by_contra hn
    obtain ⟨_, _, _, h⟩ := hG.X_word (hG.mem_word_of_not_pre ha' hn)
    rw [hXa] at h; exact arc_ne_iRow _ _ _ _ h.symm
  have h3 : e ∈ wordCols A 1 J := by
    refine hG.mem_word_of_not_pre he fun hn => ?_
    rcases hG.O_pre hn with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> rw [hOe] at h
    · exact arc_ne_rRow _ _ _ _ h
    · exact arc_ne_iRow _ _ _ _ h
    · simp only [arc_inj_iff] at h; omega
  have h4 : e' ∈ wordCols A 1 J := by
    refine hG.mem_word_of_not_pre he' fun hn => ?_
    rcases hG.X_pre hn with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hXe] at h
    · exact arc_ne_rRow _ _ _ _ h
    · exact arc_ne_iRow _ _ _ _ h
    · exact hw _ h
  have c1 := G.cpos_lt_length_of_mem hG.cols_eq h1
  have c2 := G.cpos_lt_length_of_mem hG.cols_eq h2
  have c3 := G.length_le_cpos_of_mem hG.cols_eq h3
  have c4 := G.length_le_cpos_of_mem hG.cols_eq h4
  apply nonintN_of_lt; left
  simp only [max_lt_iff, lt_min_iff]; omega

theorem outArc_norm {A : ℕ} (hA : 1 ≤ A) (b r : ℕ) :
    ∃ r' ≤ A, outArc A b r = outArc A b r' := by
  by_cases h : r ≤ A
  · exact ⟨r, h, rfl⟩
  · refine ⟨A, le_rfl, ?_⟩
    unfold outArc
    split_ifs <;> first | omega | (congr 1; omega)

theorem outArc_ne_iRow (A b r r' : ℕ) : outArc A b r ≠ iRow r' := by
  unfold outArc; split_ifs <;> exact arc_ne_iRow _ _ _ _

theorem stRow_succ_iff {x : TorusRow} : StRow A k J (s + 1) x ↔ StRow A k J s x ∧ x ≠ iRow s := by
  unfold StRow
  constructor
  · rintro (rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, h1, h2, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨b, hb1, hb, t, ht, c, rfl⟩)
    · exact ⟨Or.inl rfl, fun h => iRow_ne_rRow _ _ h.symm⟩
    · exact ⟨Or.inr (Or.inl ⟨t, h1, h2, rfl⟩), fun h => iRow_ne_rRow _ _ h.symm⟩
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨r, by omega, h2, rfl⟩)), fun h => by
        simp only [iRow_inj_iff] at h; omega⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩))), outArc_ne_iRow _ _ _ _⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨b, hb1, hb, t, ht, c, rfl⟩))),
        arc_ne_iRow _ _ _ _⟩
  · rintro ⟨rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, h1, h2, rfl⟩ | h | h, hne⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨t, h1, h2, rfl⟩)
    · have : r ≠ s := fun h => hne (by rw [h])
      exact Or.inr (Or.inr (Or.inl ⟨r, by omega, h2, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem X_r_ne (hG : Stage3 A k J s G) (hs : s < A) {i : ℕ} (h1 : A + 1 + k - 1 - s ≤ i)
    (h2 : i < A + 1 + k) : G.X (rCol i) ≠ outArc A 0 (s + 1) ∧ ∀ r, G.X (rCol i) ≠ iRow r := by
  rw [hG.X_r i h2]
  unfold winX xRes
  constructor
  · split_ifs with ha hb hb
    · simp only [inRow, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
        Nat.add_sub_cancel]
      unfold outArc
      split_ifs <;> simp only [ne_eq, arc_inj_iff, Fin.ext_iff, Fin.val_one, Fin.val_two] <;>
        intro hc <;> simp at hc <;> omega
    · intro h; unfold outArc at h; split_ifs at h <;> exact arc_ne_rRow _ _ _ _ h.symm
    · simp only [inRow, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
        Nat.add_sub_cancel]
      unfold outArc
      split_ifs <;> simp only [ne_eq, arc_inj_iff, Fin.ext_iff, Fin.val_one, Fin.val_two] <;>
        intro hc <;> simp at hc <;> omega
    · intro h; unfold outArc at h; split_ifs at h <;> exact arc_ne_rRow _ _ _ _ h.symm
  · intro r
    split_ifs
    · simp only [inRow, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
      exact outArc_ne_iRow _ _ _ _
    · exact fun h => iRow_ne_rRow _ _ h.symm
    · simp only [inRow, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
      exact outArc_ne_iRow _ _ _ _
    · exact fun h => iRow_ne_rRow _ _ h.symm

/-- **One merge of stage 3.** The row `ι s` is moved up to `B_s`'s `O`-row, the column `B_s` is
moved left to `ρ (N - 1 - s)`, and an `O`-destabilization deletes `B_s` and `ι s`. -/
theorem exists_step {m : ℕ} (hA : 1 ≤ A) (hs : s < A) {G : LabeledGrid (m + 1) TorusCol TorusRow}
    (hG : Stage3 A k J s G) :
    ∃ G' : LabeledGrid m TorusCol TorusRow, Stage3 A k J (s + 1) G' ∧
      G.toGrid.MovesTo G'.toGrid := by
  have hBmem : cor 0 (A - 1 - s) 2 ∈ G.cols := by
    rw [hG.cols]; simp only [List.mem_append]; left; left; right
    exact mem_blockBs.mpr ⟨A - 1 - s, by omega, by omega, rfl⟩
  have ho : outArc A 0 (s + 1) = arc 0 (A - 1 - s) 2 := by
    rw [outArc_pos (by omega)]; congr 1; omega
  have hOB : G.O (cor 0 (A - 1 - s) 2) = outArc A 0 (s + 1) := by rw [hG.O_c _ _ _ hBmem, ho]
  have hXB : G.X (cor 0 (A - 1 - s) 2) = iRow s := by rw [hG.X_B _ (by omega)]; congr 1; omega
  have hOd : G.O (rCol (A + 1 + k - 1 - s)) = iRow s := by
    rw [hG.O_r _ (by omega), if_neg (by omega),
      show oRes A k (A + 1 + k - 1 - s) = s + 1 by unfold oRes; split_ifs <;> omega]
    unfold winO; rw [if_pos (by omega)]; simp
  have hι : iRow s ∈ G.rows :=
    (hG.rows_iff _).mpr (Or.inr (Or.inr (Or.inl ⟨s, le_rfl, by omega, rfl⟩)))
  have hom : outArc A 0 (s + 1) ∈ G.rows :=
    (hG.rows_iff _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s + 1, by omega, rfl⟩))))
  have hlv : G.rows.Pairwise (fun a b => lvT A a ≤ lvT A b) := hG.sorted.imp hybLtS_lvT_le
  obtain ⟨m₁, mid, m₂, hsplit⟩ := exists_split_of_idxOf_lt hι hom
    (idxOf_lt_of_level hlv hι hom (lvT_iRow_lt_outArc hA hs))
  -- the rows crossed by `ι s` are arcs of later blocks
  have hmid : ∀ z ∈ mid, G.RowsNonint (iRow s) z := by
    intro z hz
    obtain ⟨h1, h2⟩ := pairwise_mid hG.sorted hsplit hz
    have hzr : z ∈ G.rows := by rw [hsplit]; simp [hz]
    rw [ho] at h2
    rcases (hG.rows_iff z).mp hzr with rfl | ⟨t, ht1, ht2, rfl⟩ | ⟨r, hr1, hr2, rfl⟩ |
        ⟨r, hr, rfl⟩ | ⟨b, hb1, hb, t, ht, c, rfl⟩
    · exfalso; unfold hybLtS at h1; simp at h1
    · exfalso; unfold hybLtS at h2; simp [arcLv, show t ≠ 0 by omega] at h2; omega
    · exfalso; unfold hybLtS at h1 h2; simp [arcLv] at h1 h2; omega
    · exfalso
      rw [← ho] at h2
      unfold hybLtS at h1 h2
      rw [lvT_outArc hA hr, lvT_iRow] at h1
      rw [lvT_outArc hA hr, lvT_outArc hA (by omega)] at h2
      have : r = s + 1 := by omega
      subst this
      omega
    · refine hG.rowsNonint_iRow s hb1 fun r' hr' => ?_
      obtain ⟨r'', hr'', he⟩ := outArc_norm hA J r'
      rw [← ho, hr', he] at h2
      rw [hr', he] at h1
      unfold hybLtS at h1 h2
      rw [lvT_outArc hA hr'', lvT_iRow] at h1
      rw [lvT_outArc hA hr'', lvT_outArc hA (by omega), subSw_outArc hA hr'',
        subSw_outArc hA (by omega)] at h2
      split_ifs at h2 <;> omega
  obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hmv₁⟩ := G.exists_moveRowUp hsplit hmid
  -- move `B_s` left
  have e1 : rCols (A + 1 + k) = rCols (A + 1 + k - s) ++ rColsR (A + 1 + k - s) s := by
    have := rColsR_append 0 (A + 1 + k - s) s
    rw [zero_add, Nat.sub_add_cancel (by omega)] at this
    exact this
  have e2 : blockBs 0 (A - s) = blockBs 0 (A - 1 - s) ++ [cor 0 (A - 1 - s) 2] := by
    rw [show A - s = A - 1 - s + 1 by omega, blockBs_succ, zero_add]
  have hcolsG : G₁.cols = rCols (A + 1 + k - s) ++ (rColsR (A + 1 + k - s) s ++
      blockBs 0 (A - 1 - s)) ++ cor 0 (A - 1 - s) 2 :: (cor 0 (A - 1) 1 :: wordCols A 1 J) := by
    rw [hc₁, hG.cols, e1, e2]; simp
  have hadj : G₁.rpos (G₁.X (cor 0 (A - 1 - s) 2)) = G₁.rpos (G₁.O (cor 0 (A - 1 - s) 2)) + 1 ∨
      G₁.rpos (G₁.O (cor 0 (A - 1 - s) 2)) = G₁.rpos (G₁.X (cor 0 (A - 1 - s) 2)) + 1 := by
    rw [hO₁, hX₁, hOB, hXB]; right
    exact G₁.rpos_succ_of_rows (m₁ := m₁ ++ mid) (by rw [hr₁])
  obtain ⟨G₂, hc₂, hr₂, hO₂, hX₂, hmv₂⟩ := G₁.exists_moveColLeft (l₁ := rCols (A + 1 + k - s))
    (mid := rColsR (A + 1 + k - s) s ++ blockBs 0 (A - 1 - s)) (c := cor 0 (A - 1 - s) 2)
    (l₂ := cor 0 (A - 1) 1 :: wordCols A 1 J) hcolsG (by
      intro d hd
      have hdm : d ∈ G₁.cols := by
        rw [hcolsG, List.mem_append, List.mem_append]; exact Or.inl (Or.inr hd)
      rw [G₁.colsNonint_comm]
      refine G₁.colsNonint_of_short (hc₁ ▸ hBmem) hdm hadj ?_ ?_ ?_ ?_ <;>
        simp only [hO₁, hX₁, hOB, hXB] <;> rw [List.mem_append] at hd
      · rcases hd with hd | hd
        · obtain ⟨i, hi1, hi2, rfl⟩ := mem_rColsR.mp hd
          rw [hG.O_r i (by omega), if_pos (by omega), ho]
          simp only [ne_eq, arc_inj_iff]; omega
        · obtain ⟨t, -, ht, rfl⟩ := mem_blockBs.mp hd
          rw [hG.O_c _ _ _ (hc₁ ▸ hdm), ho]; simp only [ne_eq, arc_inj_iff]; omega
      · rcases hd with hd | hd
        · obtain ⟨i, hi1, hi2, rfl⟩ := mem_rColsR.mp hd
          rw [hG.O_r i (by omega), if_pos (by omega)]; exact arc_ne_iRow _ _ _ _
        · obtain ⟨t, -, ht, rfl⟩ := mem_blockBs.mp hd
          rw [hG.O_c _ _ _ (hc₁ ▸ hdm)]; exact arc_ne_iRow _ _ _ _
      · rcases hd with hd | hd
        · obtain ⟨i, hi1, hi2, rfl⟩ := mem_rColsR.mp hd
          exact (hG.X_r_ne hs (by omega) (by omega)).1
        · obtain ⟨t, -, ht, rfl⟩ := mem_blockBs.mp hd
          rw [hG.X_B t (by omega)]; exact (outArc_ne_iRow _ _ _ _).symm
      · rcases hd with hd | hd
        · obtain ⟨i, hi1, hi2, rfl⟩ := mem_rColsR.mp hd
          exact (hG.X_r_ne hs (by omega) (by omega)).2 s
        · obtain ⟨t, -, ht, rfl⟩ := mem_blockBs.mp hd
          rw [hG.X_B t (by omega)]; simp only [ne_eq, iRow_inj_iff]; omega)
  -- the `O`-destabilization
  have e3 : rCols (A + 1 + k - s) = rCols (A + 1 + k - 1 - s) ++ [rCol (A + 1 + k - 1 - s)] := by
    rw [show A + 1 + k - s = A + 1 + k - 1 - s + 1 by omega, rCols_succ]
  have hcols₂ : G₂.cols = rCols (A + 1 + k - 1 - s) ++ rCol (A + 1 + k - 1 - s) ::
      cor 0 (A - 1 - s) 2 :: (rColsR (A + 1 + k - s) s ++ blockBs 0 (A - 1 - s) ++
        cor 0 (A - 1) 1 :: wordCols A 1 J) := by
    rw [hc₂, e3]; simp
  have hrows₂ : G₂.rows = (m₁ ++ mid) ++ iRow s :: ([] ++ outArc A 0 (s + 1) :: m₂) := by
    rw [hr₂, hr₁]; simp
  obtain ⟨G₃, hc₃, hr₃, hO₃, hX₃, hmv₃⟩ := G₂.exists_mergeO_up (c := cor 0 (A - 1 - s) 2)
    (d := rCol (A + 1 + k - 1 - s)) (e := iRow s) (z := outArc A 0 (s + 1)) (mid := [])
    (Or.inr hcols₂) hrows₂ (by rw [hX₂, hX₁, hXB]) (by rw [hO₂, hO₁, hOB])
    (by rw [hO₂, hO₁, hOd]) (by rw [hX₂, hX₁]; exact (hG.X_r_ne hs le_rfl (by omega)).1)
    (by simp)
  -- the new state
  have hsubc : ∀ x ∈ G₃.cols, x ∈ G.cols := by
    intro x hx
    rw [hc₃] at hx
    have h2m : x ∈ G₂.cols := by
      rw [hcols₂]
      exact (((List.sublist_cons_self _ _).cons₂ _).append_left _).subset hx
    have h1m : x ∈ G₁.cols := by
      rw [hcolsG, List.append_assoc]; rw [hc₂] at h2m
      exact ((List.perm_middle).symm.append_left _).subset h2m
    rwa [hc₁] at h1m
  have hnd := G.rows_nodup
  rw [hsplit] at hnd
  have hιm₁ : iRow s ∉ m₁ := fun h => (List.nodup_append.mp hnd).2.2 _ h _ (by simp) rfl
  have hιr : iRow s ∉ mid ++ outArc A 0 (s + 1) :: m₂ := (List.nodup_cons.mp
    (List.nodup_append.mp hnd).2.1).1
  refine ⟨G₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hmv₁.trans (hmv₂.trans hmv₃)⟩
  · rw [hc₃, show A - (s + 1) = A - 1 - s by omega, e1, e3]
    simp
  · intro i hi
    rw [hO₃, hO₂, hO₁]
    by_cases hie : i = A + 1 + k - 1 - s
    · subst hie
      rw [Function.update_self, if_pos (by omega), ho]; congr 1; omega
    · rw [Function.update_of_ne (by simpa using hie), hG.O_r i hi]
      by_cases hc : A + 1 + k ≤ i + s
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]
  · intro b t c hc
    rw [hO₃, hO₂, hO₁, Function.update_of_ne (cor_ne_rCol _ _ _ _), hG.O_c _ _ _ (hsubc _ hc)]
  · intro i hi; rw [hX₃, hX₂, hX₁, hG.X_r i hi]
  · intro t ht; rw [hX₃, hX₂, hX₁, hG.X_B t (by omega)]
  · rw [hX₃, hX₂, hX₁, hG.X_V]
  · intro c hc; rw [hX₃, hX₂, hX₁, hG.X_w c hc]
  · intro x
    rw [stRow_succ_iff, ← hG.rows_iff, hr₃, hsplit]
    have hιr' := hιr
    simp only [List.mem_append, List.mem_cons, not_or] at hιr'
    obtain ⟨hιmid, hιo, hιm₂⟩ := hιr'
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
    constructor
    · intro h
      refine ⟨by tauto, ?_⟩
      rintro rfl
      rcases h with (h | h) | h | h
      · exact hιm₁ h
      · exact hιmid h
      · exact hιo h
      · exact hιm₂ h
    · rintro ⟨h, hne⟩
      rcases h with h | h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact absurd h hne
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rw [hr₃]
    refine hG.sorted.sublist ?_
    rw [hsplit]
    simp only [List.nil_append, List.append_assoc]
    exact (List.sublist_cons_self _ _).append_left m₁

/-- **Stage 3.** All `A` merges. -/
theorem exists_all {m : ℕ} (hA : 1 ≤ A) {G : LabeledGrid m TorusCol TorusRow}
    (hG : Stage3 A k J 0 G) :
    ∃ (m' : ℕ) (G' : LabeledGrid m' TorusCol TorusRow), m' + A = m ∧ Stage3 A k J A G' ∧
      G.toGrid.MovesTo G'.toGrid := by
  suffices H : ∀ s ≤ A, ∃ (m' : ℕ) (G' : LabeledGrid m' TorusCol TorusRow), m' + s = m ∧
      Stage3 A k J s G' ∧ G.toGrid.MovesTo G'.toGrid from H A le_rfl
  intro s
  induction s with
  | zero => exact fun _ => ⟨m, G, rfl, hG, GridDiagram.MovesTo.refl _⟩
  | succ s ih =>
    intro hs
    obtain ⟨m', G', hm', hG', hmv⟩ := ih (by omega)
    have hV : cor 0 (A - 1) 1 ∈ G'.cols := by rw [hG'.cols]; simp
    obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by have := G'.cpos_lt hV; omega⟩
    obtain ⟨G'', hG'', hmv'⟩ := hG'.exists_step hA (by omega)
    exact ⟨m'', G'', by omega, hG'', hmv.trans hmv'⟩

end Stage3

/-! ### Renaming after the absorption -/

/-- Renaming of the columns after the absorption: `V ↦ ρ N` and the blocks move down by one. -/
def absF (A k : ℕ) : TorusCol → TorusCol
  | Sum.inl c => rCol c
  | Sum.inr (b, t, c) => if b = 0 then rCol (A + 1 + k) else cor (b - 1) t c

/-- A left inverse of `absF` on the columns after stage 3. -/
def absFinv (A k : ℕ) : TorusCol → TorusCol
  | Sum.inl c => if c = A + 1 + k then cor 0 (A - 1) 1 else rCol c
  | Sum.inr (b, t, c) => cor (b + 1) t c

/-- Renaming of the rows after the absorption. -/
def absG (A : ℕ) : TorusRow → TorusRow
  | Sum.inl t => if t = 0 then rRow 0 else rRow (t + 1)
  | Sum.inr (Sum.inl _) => rRow (A + 2)
  | Sum.inr (Sum.inr (b, t, c)) =>
    if b = 0 then (if c = 2 then iRow (A - t) else iRow 0) else arc (b - 1) t c

/-- A left inverse of `absG` on the rows after stage 3. -/
def absGinv (A : ℕ) : TorusRow → TorusRow
  | Sum.inl t => if t = 0 then rRow 0 else if t = A + 2 then iRow A else rRow (t - 1)
  | Sum.inr (Sum.inl r) => outArc A 0 r
  | Sum.inr (Sum.inr (b, t, c)) => arc (b + 1) t c

@[simp] theorem absF_rCol (A k c : ℕ) : absF A k (rCol c) = rCol c := rfl

theorem absF_cor (A k b t : ℕ) (c : Fin 3) :
    absF A k (cor b t c) = if b = 0 then rCol (A + 1 + k) else cor (b - 1) t c := rfl

theorem absG_rRow (A t : ℕ) : absG A (rRow t) = if t = 0 then rRow 0 else rRow (t + 1) := rfl

@[simp] theorem absG_iRow (A r : ℕ) : absG A (iRow r) = rRow (A + 2) := rfl

theorem absG_arc (A b t : ℕ) (c : Fin 3) : absG A (arc b t c) =
    if b = 0 then (if c = 2 then iRow (A - t) else iRow 0) else arc (b - 1) t c := rfl

theorem absG_outArc {A r : ℕ} (hA : 1 ≤ A) (hr : r ≤ A) (b : ℕ) :
    absG A (outArc A b r) = inRow A b r := by
  by_cases hb : b = 0
  · subst hb
    simp only [inRow, if_true]
    by_cases h0 : r = 0
    · subst h0; rw [outArc_zero, absG_arc]; simp
    · rw [outArc_pos h0, absG_arc]; simp; omega
  · simp only [inRow, hb, if_false]
    by_cases h0 : r = 0
    · subst h0; rw [outArc_zero, absG_arc, if_neg hb, outArc_zero]
    · rw [outArc_pos h0, absG_arc, if_neg hb, outArc_pos h0]

theorem absFinv_rCol (A k c : ℕ) :
    absFinv A k (rCol c) = if c = A + 1 + k then cor 0 (A - 1) 1 else rCol c := rfl

@[simp] theorem absFinv_cor (A k b t : ℕ) (c : Fin 3) : absFinv A k (cor b t c) = cor (b + 1) t c :=
  rfl

theorem absGinv_rRow (A t : ℕ) :
    absGinv A (rRow t) = if t = 0 then rRow 0 else if t = A + 2 then iRow A else rRow (t - 1) := rfl

@[simp] theorem absGinv_iRow (A r : ℕ) : absGinv A (iRow r) = outArc A 0 r := rfl

@[simp] theorem absGinv_arc (A b t : ℕ) (c : Fin 3) : absGinv A (arc b t c) = arc (b + 1) t c :=
  rfl

theorem map_absF_blockCols (A k b : ℕ) : (blockCols A (b + 1)).map (absF A k) = blockCols A b := by
  simp [blockCols, blockColsR, List.map_flatMap, absF_cor]

theorem map_absF_wordCols (A k J : ℕ) :
    ∀ b₀, (wordCols A (b₀ + 1) J).map (absF A k) = wordCols A b₀ J := by
  induction J with
  | zero => intro b₀; simp [wordCols]
  | succ J ih =>
    intro b₀
    rw [wordCols_succ, List.map_append, map_absF_blockCols, ih (b₀ + 1), wordCols_succ]

theorem map_absF_rCols (A k N : ℕ) : (rCols N).map (absF A k) = rCols N := by
  simp only [rCols, rColsR, List.map_map]
  rfl

/-- Levels and orders of the rows after stage 3 and of their renamings. -/
theorem absorb_vals {A k J : ℕ} (hA : 1 ≤ A) {y : TorusRow} (hy : StRow A k J A y) :
    (lvT A y = 0 ∧ subSw A (J + 1) (A + 1) y = 0 ∧ lvT A (absG A y) = 0 ∧
        subSw A J 0 (absG A y) = 0) ∨
      (5 * A + 6 ≤ lvT A y ∧ subSw A (J + 1) (A + 1) y = 0 ∧ lvT A (absG A y) = lvT A y + 1 ∧
        subSw A J 0 (absG A y) = 0) ∨
      (lvT A y = 4 * A + 1 ∧ subSw A (J + 1) (A + 1) y = 0 ∧ lvT A (absG A y) = 5 * A + 6 ∧
        subSw A J 0 (absG A y) = 0) ∨
      (lvT A y % 4 = 0 ∧ lvT A y ≤ 4 * A ∧ subSw A (J + 1) (A + 1) y = 4 * J + 8 ∧
        lvT A (absG A y) = lvT A y + 1 ∧ subSw A J 0 (absG A y) = 0) ∨
      ((lvT A y % 4 = 0 ∨ lvT A y % 4 = 2) ∧ lvT A y ≤ 4 * A ∧ lvT A (absG A y) = lvT A y ∧
        ((subSw A (J + 1) (A + 1) y = 4 * J + 7 ∧ subSw A J 0 (absG A y) = 4 * J + 3) ∨
          (subSw A (J + 1) (A + 1) y ≤ 4 * J + 2 ∧
            subSw A J 0 (absG A y) = subSw A (J + 1) (A + 1) y))) := by
  rcases hy with rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, h1, h2, rfl⟩ | ⟨r, hr, rfl⟩ |
      ⟨b, hb1, hb, t, ht, c, rfl⟩
  · left; simp [absG_rRow]
  · right; left; simp [absG_rRow, show t ≠ 0 by omega]; omega
  · right; right; left
    obtain rfl : r = A := by omega
    simp; omega
  · right; right; right; left
    rw [absG_outArc hA hr, lvT_outArc hA hr, subSw_outArc hA hr]
    simp [inRow, show r < A + 1 by omega]; omega
  · right; right; right; right
    rw [absG_arc, if_neg (by omega)]
    simp only [lvT_arc, subSw_arc, arcLv, arcSub]
    have hc := c.isLt
    rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with hc | hc | hc <;>
      simp only [hc] <;> split_ifs <;>
      simp only [false_or, false_and, and_false, or_false, true_and, and_true, true_or,
        or_true] at * <;> first | contradiction | omega

theorem absorb_mono {A k J : ℕ} (hA : 1 ≤ A) {a b : TorusRow} (ha : StRow A k J A a)
    (hb : StRow A k J A b) (h : hybLtS A (J + 1) (A + 1) a b) :
    hybLtS A J 0 (absG A a) (absG A b) := by
  have va := absorb_vals hA ha
  have vb := absorb_vals hA hb
  unfold hybLtS at h ⊢
  omega

/-- With one block, the orders `hybLtS A 1 0` and `hybLtS A 1 (A + 1)` agree on the rows after
stage 3. -/
theorem absorb_mono_zero {A k : ℕ} (hA : 1 ≤ A) {a b : TorusRow} (ha : StRow A k 0 A a)
    (hb : StRow A k 0 A b) (h : hybLtS A 1 0 a b) : hybLtS A 1 (A + 1) a b := by
  have key : ∀ y, StRow A k 0 A y → (subSw A 1 0 y = 0 ∧ subSw A 1 (A + 1) y = 0) ∨
      (subSw A 1 0 y = 7 ∧ subSw A 1 (A + 1) y = 8) := by
    rintro y (rfl | ⟨t, -, -, rfl⟩ | ⟨r, -, -, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨b, hb1, hb, -⟩)
    · simp
    · simp
    · simp
    · right; rw [subSw_outArc hA hr, subSw_outArc hA hr]; simp; omega
    · omega
  have va := key a ha
  have vb := key b hb
  unfold hybLtS at h ⊢
  omega

namespace Stage3

variable {m A k J : ℕ} {G : LabeledGrid m TorusCol TorusRow}

theorem cols_final (hG : Stage3 A k J A G) :
    G.cols = rCols (A + 1 + k) ++ cor 0 (A - 1) 1 :: wordCols A 1 J := by
  rw [hG.cols]; simp [blockBs]

/-- After stage 3, the last outgoing arc of rank `r` of the first block lies inside the one of the
last block. -/
theorem rowsNonint_outArc (hG : Stage3 A k J A G) (hA : 1 ≤ A) (hk : 1 ≤ k) (hJ : 1 ≤ J) {r : ℕ}
    (hr : r ≤ A) : G.RowsNonint (outArc A 0 r) (outArc A J r) := by
  have hcols := hG.cols_final
  have hcols' : G.cols = (rCols (A + 1 + k) ++ [cor 0 (A - 1) 1]) ++ wordCols A 1 J := by
    rw [hcols]; simp
  have hVm : cor 0 (A - 1) 1 ∈ G.cols := by rw [hcols]; simp
  have cV : G.cpos (cor 0 (A - 1) 1) = A + 1 + k := by
    rw [G.cpos_of_cols_eq hcols, rCols_length]
  -- the `O`-column of the inner arc
  obtain ⟨ox, hox, eox, pox⟩ : ∃ ox ∈ G.cols, G.O ox = outArc A 0 r ∧ A - r < G.cpos ox ∧
      G.cpos ox ≤ A + 1 + k := by
    by_cases h0 : r = 0
    · subst h0
      exact ⟨_, hVm, by rw [hG.O_c _ _ _ hVm, outArc_zero], by rw [cV]; omega, by rw [cV]⟩
    · have hm : rCol (A + 1 + k - r) ∈ G.cols := by
        rw [hcols, List.mem_append, mem_rCols]; exact Or.inl ⟨_, by omega, rfl⟩
      refine ⟨_, hm, ?_, ?_⟩
      · rw [hG.O_r _ (by omega), if_pos (by omega), outArc_pos h0]; congr 1; omega
      · rw [cpos_rCol G hcols (by omega)]; omega
  -- the `X`-column of the inner arc, in block `1`
  obtain ⟨tx, cx, htx, exx, hxpos⟩ : ∃ (tx : ℕ) (cx : Fin 3), tx < A ∧
      G.X (cor 1 tx cx) = outArc A 0 r ∧ 3 * tx + cx.val = if r = A then 1 else 3 * (A - 1 - r) := by
    by_cases hrA : r = A
    · subst hrA
      refine ⟨0, 1, by omega, ?_, by simp⟩
      rw [hG.X_w _ (mem_wordCols.mpr ⟨1, le_rfl, by omega, 0, by omega, 1, rfl⟩), hybX_cor]
      simp [corX, inRow]
    · refine ⟨A - 1 - r, 0, by omega, ?_, by simp [hrA]⟩
      rw [hG.X_w _ (mem_wordCols.mpr ⟨1, le_rfl, by omega, A - 1 - r, by omega, 0, rfl⟩), hybX_cor]
      simp only [corX, if_true, inRow, one_ne_zero, if_false, Nat.sub_self]
      congr 1; omega
  -- the `O`-column of the outer arc, in block `J`
  obtain ⟨ty, cy, hty, eoy, hypos⟩ : ∃ (ty : ℕ) (cy : Fin 3), ty < A ∧
      G.O (cor J ty cy) = outArc A J r ∧ 3 * ty + cy.val = if r = 0 then 3 * (A - 1) + 1
        else 3 * (A - r) + 2 := by
    have hm : ∀ t < A, ∀ c : Fin 3, cor J t c ∈ G.cols := fun t ht c => by
      rw [hcols', List.mem_append, mem_wordCols]; exact Or.inr ⟨J, hJ, by omega, t, ht, c, rfl⟩
    by_cases h0 : r = 0
    · subst h0
      exact ⟨A - 1, 1, by omega, by rw [hG.O_c _ _ _ (hm _ (by omega) _), outArc_zero], by simp⟩
    · exact ⟨A - r, 2, by omega, by rw [hG.O_c _ _ _ (hm _ (by omega) _), outArc_pos h0],
        by simp [h0]⟩
  have hxm : cor 1 tx cx ∈ wordCols A 1 J := mem_wordCols.mpr ⟨1, le_rfl, by omega, tx, htx, cx, rfl⟩
  have hym : cor J ty cy ∈ wordCols A 1 J := mem_wordCols.mpr ⟨J, hJ, by omega, ty, hty, cy, rfl⟩
  have hxym : rCol (A - r) ∈ G.cols := by
    rw [hcols, List.mem_append, mem_rCols]; exact Or.inl ⟨_, by omega, rfl⟩
  have exy : G.X (rCol (A - r)) = outArc A J r := by
    rw [hG.X_r _ (by omega), show xRes A k (A - r) = r + 1 by unfold xRes; split_ifs <;> omega]
    unfold winX; rw [if_pos (by omega)]; simp [inRow]
  have p1 := G.length_le_cpos_of_mem hcols' hxm
  simp only [List.length_append, rCols_length, List.length_singleton] at p1
  have p2 : G.cpos (cor 1 tx cx) < G.cpos (cor J ty cy) := by
    by_cases hJ1 : J = 1
    · subst hJ1
      have hc1 : G.cols = (rCols (A + 1 + k) ++ [cor 0 (A - 1) 1]) ++ blockCols A 1 ++ [] := by
        rw [hcols', wordCols_succ]; simp [wordCols]
      rw [cpos_cor G hc1 htx, cpos_cor G hc1 hty]
      split_ifs at hxpos hypos <;> omega
    · have hc2 : G.cols = (rCols (A + 1 + k) ++ [cor 0 (A - 1) 1] ++ wordCols A 1 (J - 1)) ++
          blockCols A J := by
        rw [hcols']
        conv_lhs => rw [show J = J - 1 + 1 by omega, wordCols_succ', show 1 + (J - 1) = J by omega]
        simp
      exact G.cpos_lt_of_mem_append hc2
        (List.mem_append_right _ (mem_wordCols.mpr ⟨1, le_rfl, by omega, tx, htx, cx, rfl⟩))
        (mem_blockCols.mpr ⟨ty, hty, cy, rfl⟩)
  have p3 : G.cpos (rCol (A - r)) = A - r := cpos_rCol G hcols (by omega)
  refine G.rowsNonint_of_cols hox (hG.cols_eq ▸ List.mem_append_right _ hxm) ?_ hxym eox exx eoy exy ?_
  · rw [hcols']; exact List.mem_append_right _ hym
  · apply nonintN_of_nested; left
    rw [p3]
    constructor <;> simp only [min_def, max_def] <;> split_ifs <;> omega

/-- After stage 3, the exchanges of the last outgoing arcs. -/
theorem exists_swapped (hG : Stage3 A k J A G) (hA : 1 ≤ A) (hk : 1 ≤ k) :
    ∃ G₁ : LabeledGrid m TorusCol TorusRow, G₁.cols = G.cols ∧ G₁.O = G.O ∧ G₁.X = G.X ∧
      (∀ x, x ∈ G₁.rows ↔ StRow A k J A x) ∧ G₁.rows.Pairwise (hybLtS A (J + 1) (A + 1)) ∧
      G.toGrid.MovesTo G₁.toGrid := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · exact ⟨G, rfl, rfl, rfl, hG.rows_iff, hG.sorted.imp_of_mem fun ha hb h =>
      absorb_mono_zero hA ((hG.rows_iff _).mp ha) ((hG.rows_iff _).mp hb) h,
      GridDiagram.MovesTo.refl _⟩
  · have hshape : ∀ z ∈ G.rows, RowShape A (J + 1) z := by
      intro z hz
      rcases (hG.rows_iff z).mp hz with rfl | ⟨t, -, -, rfl⟩ | ⟨r, -, -, rfl⟩ | ⟨r, hr, rfl⟩ |
          ⟨b, -, hb, t, ht, c, rfl⟩
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inl ⟨t, rfl⟩
      · exact Or.inr (Or.inl ⟨r, rfl⟩)
      · unfold outArc
        split_ifs
        · exact Or.inr (Or.inr ⟨0, by omega, A - 1, by omega, 1, rfl⟩)
        · exact Or.inr (Or.inr ⟨0, by omega, A - r, by omega, 2, rfl⟩)
      · exact Or.inr (Or.inr ⟨b, hb, t, ht, c, rfl⟩)
    have hJ' : J + 1 - 1 = J := by omega
    obtain ⟨G₁, hc, hO, hX, hm, hs, hmv⟩ := G.exists_swapOuts hA (by omega) hshape hG.sorted
      (fun r hr => by
        rw [hJ']
        refine ⟨(hG.rows_iff _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)))),
          (hG.rows_iff _).mpr ?_⟩
        right; right; right; right
        unfold outArc
        split_ifs
        · exact ⟨J, hJ, by omega, A - 1, by omega, 1, rfl⟩
        · exact ⟨J, hJ, by omega, A - r, by omega, 2, rfl⟩)
      (fun r hr => by rw [hJ']; exact hG.rowsNonint_outArc hA hk hJ hr)
    exact ⟨G₁, hc, hO, hX, fun x => (hm x).trans (hG.rows_iff x), hs, hmv⟩

end Stage3

/-! ### Identification with the next hybrid grid -/

theorem absG_O_rCol {A k i : ℕ} (hi : i < A + 1 + k) :
    absG A (if A + 1 + k ≤ i + A then arc 0 (i - k - 1) 2 else winO A (oRes A k i)) =
      winO A (oRes A (k + 1) i) := by
  by_cases hiA : A + 1 + k ≤ i + A
  · have h1 : oRes A (k + 1) i = A + 2 + k - i := by unfold oRes; split_ifs <;> omega
    rw [if_pos hiA, absG_arc, h1]
    simp only [if_true]
    unfold winO
    rw [if_pos (by omega)]
    congr 1; omega
  · rw [if_neg hiA]
    by_cases h0 : i = 0
    · subst h0; simp [oRes, winO, absG_rRow]
    · have h1 : oRes A (k + 1) i = A + 2 + k - i := by unfold oRes; split_ifs <;> omega
      have h2 : oRes A k i = A + 1 + k - i := by unfold oRes; split_ifs <;> omega
      rw [h1, h2]
      unfold winO
      by_cases hik : i = k
      · rw [if_pos (by omega), if_neg (by omega), absG_iRow]; congr 1; omega
      · rw [if_neg (by omega), if_neg (by omega), absG_rRow, if_neg (by omega)]; congr 1; omega

theorem absG_X_rCol {A k J i : ℕ} (hA : 1 ≤ A) (hk : 1 ≤ k) (hi : i < A + 1 + k) :
    absG A (winX A (J + 1) (xRes A k i)) = winX A J (xRes A (k + 1) i) := by
  unfold winX xRes
  by_cases hi1 : i ≤ A + 1
  · rw [if_pos hi1, if_pos hi1]
    split_ifs with hw
    · rw [show inRow A (J + 1) (A + 1 - i - 1) = outArc A J (A + 1 - i - 1) by simp [inRow],
        absG_outArc hA (by omega)]
    · rw [absG_rRow, if_pos (by omega), show A + 1 - i = 0 by omega]
  · rw [if_neg hi1, if_neg hi1, if_neg (by omega), if_neg (by omega), absG_rRow, if_neg (by omega)]
    congr 1; omega

theorem absG_corX {A b t : ℕ} (hA : 1 ≤ A) (hb : 1 ≤ b) (ht : t < A) (c : Fin 3) :
    absG A (corX A (inRow A) b t c) = corX A (inRow A) (b - 1) t c := by
  have hin : ∀ r ≤ A, absG A (inRow A b r) = inRow A (b - 1) r := fun r hr => by
    rw [show inRow A b r = outArc A (b - 1) r by simp [inRow, show b ≠ 0 by omega],
      absG_outArc hA hr]
  unfold corX
  split_ifs with h0 h1 h2
  · exact hin _ (by omega)
  · exact hin _ le_rfl
  · rw [absG_arc, if_neg (by omega)]
  · rw [absG_arc, if_neg (by omega)]

namespace Stage3

variable {m A k J : ℕ} {G : LabeledGrid m TorusCol TorusRow}

/-- After the exchanges, renaming the labels gives the hybrid grid with one block less. -/
theorem exists_isHybrid (hG : Stage3 A k J A G) (hA : 1 ≤ A) (hk : 1 ≤ k)
    {G₁ : LabeledGrid m TorusCol TorusRow} (hc : G₁.cols = G.cols) (hO : G₁.O = G.O)
    (hX : G₁.X = G.X) (hrows : ∀ x, x ∈ G₁.rows ↔ StRow A k J A x)
    (hsort : G₁.rows.Pairwise (hybLtS A (J + 1) (A + 1))) :
    ∃ G' : LabeledGrid m TorusCol TorusRow, IsHybrid A (k + 1) J G' ∧ G'.toGrid = G₁.toGrid := by
  have hcols : G₁.cols = rCols (A + 1 + k) ++ cor 0 (A - 1) 1 :: wordCols A 1 J :=
    hc.trans hG.cols_final
  have hmemc : ∀ c ∈ G₁.cols, (∃ i < A + 1 + k, c = rCol i) ∨ c = cor 0 (A - 1) 1 ∨
      ∃ b, 1 ≤ b ∧ b < 1 + J ∧ ∃ t < A, ∃ c' : Fin 3, c = cor b t c' := by
    intro c hcm
    rw [hcols, List.mem_append, List.mem_cons, mem_rCols, mem_wordCols] at hcm
    rcases hcm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hGm : ∀ c ∈ G₁.cols, c ∈ G.cols := fun c h => hc ▸ h
  have hf : ∀ c ∈ G₁.cols, absFinv A k (absF A k c) = c := by
    intro c hcm
    rcases hmemc c hcm with ⟨i, hi, rfl⟩ | rfl | ⟨b, hb1, -, t, -, c', rfl⟩
    · rw [absF_rCol, absFinv_rCol, if_neg (by omega)]
    · rw [absF_cor, if_pos rfl, absFinv_rCol, if_pos rfl]
    · rw [absF_cor, if_neg (by omega), absFinv_cor, Nat.sub_add_cancel hb1]
  have hg : ∀ x ∈ G₁.rows, absGinv A (absG A x) = x := by
    intro x hx
    rcases (hrows x).mp hx with rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, h1, h2, rfl⟩ | ⟨r, hr, rfl⟩ |
        ⟨b, hb1, hb, t, ht, c, rfl⟩
    · rfl
    · rw [absG_rRow, if_neg (by omega), absGinv_rRow, if_neg (by omega), if_neg (by omega),
        Nat.add_sub_cancel]
    · obtain rfl : r = A := by omega
      rw [absG_iRow, absGinv_rRow, if_neg (by omega), if_pos rfl]
    · rw [absG_outArc hA hr]; simp [inRow]
    · rw [absG_arc, if_neg (by omega), absGinv_arc, Nat.sub_add_cancel hb1]
  refine ⟨G₁.relabel (absF A k) (absFinv A k) (absG A) (absGinv A) hf hg, ⟨?_, ?_, ?_, ?_, ?_⟩,
    LabeledGrid.toGrid_relabel _ _ _ _ _ _ _⟩
  · show G₁.cols.map (absF A k) = hybCols A (k + 1) J
    rw [hcols, List.map_append, List.map_cons, map_absF_rCols, map_absF_wordCols A k J 0,
      hybCols, absF_cor, if_pos rfl, show A + 1 + (k + 1) = A + 1 + k + 1 by omega, rCols_succ]
    simp
  · intro c hcm
    change absG A (G₁.O (absFinv A k c)) = hybO A (k + 1) c
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hcm
    rw [hf c₀ hc₀, hO]
    rcases hmemc c₀ hc₀ with ⟨i, hi, rfl⟩ | rfl | ⟨b, hb1, -, t, -, c', rfl⟩
    · rw [hG.O_r i hi, absF_rCol, hybO_rCol, absG_O_rCol hi]
    · have h1 : oRes A (k + 1) (A + 1 + k) = 1 := by unfold oRes; split_ifs <;> omega
      rw [hG.O_c _ _ _ (hGm _ hc₀), absF_cor, if_pos rfl, hybO_rCol, absG_arc, h1]
      simp [winO]
    · rw [hG.O_c _ _ _ (hGm _ hc₀), absF_cor, if_neg (by omega), hybO_cor, absG_arc,
        if_neg (by omega)]
  · intro c hcm
    change absG A (G₁.X (absFinv A k c)) = hybX A (k + 1) J c
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hcm
    rw [hf c₀ hc₀, hX]
    rcases hmemc c₀ hc₀ with ⟨i, hi, rfl⟩ | rfl | ⟨b, hb1, hbJ, t, ht, c', rfl⟩
    · rw [hG.X_r i hi, absF_rCol, hybX_rCol, absG_X_rCol hA hk hi]
    · have h2 : xRes A (k + 1) (A + 1 + k) = A + 2 := by unfold xRes; split_ifs <;> omega
      rw [hG.X_V, absF_cor, if_pos rfl, hybX_rCol, absG_iRow, h2]
      simp [winX]
    · rw [hG.X_w _ (mem_wordCols.mpr ⟨b, hb1, hbJ, t, ht, c', rfl⟩), hybX_cor, absF_cor,
        if_neg (by omega), hybX_cor, absG_corX hA hb1 ht]
  · intro x
    change x ∈ G₁.rows.map (absG A) ↔ HybRow A (k + 1) J x
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (hrows y).mp hy with rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, h1, h2, rfl⟩ | ⟨r, hr, rfl⟩ |
          ⟨b, hb1, hb, t, ht, c, rfl⟩
      · exact Or.inl rfl
      · rw [absG_rRow, if_neg (by omega)]; exact Or.inr (Or.inl ⟨t + 1, by omega, by omega, rfl⟩)
      · rw [absG_iRow]; exact Or.inr (Or.inl ⟨A + 2, le_rfl, by omega, rfl⟩)
      · rw [absG_outArc hA hr]; exact Or.inr (Or.inr (Or.inl ⟨r, hr, by simp [inRow]⟩))
      · rw [absG_arc, if_neg (by omega)]
        exact Or.inr (Or.inr (Or.inr ⟨b - 1, by omega, t, ht, c, rfl⟩))
    · rintro (rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨b, hb, t, ht, c, rfl⟩)
      · exact ⟨rRow 0, (hrows _).mpr (Or.inl rfl), rfl⟩
      · by_cases htA : t = A + 2
        · subst htA
          exact ⟨iRow A, (hrows _).mpr (Or.inr (Or.inr (Or.inl ⟨A, le_rfl, le_rfl, rfl⟩))), rfl⟩
        · refine ⟨rRow (t - 1), (hrows _).mpr (Or.inr (Or.inl ⟨t - 1, by omega, by omega, rfl⟩)),
            ?_⟩
          rw [absG_rRow, if_neg (by omega)]; congr 1; omega
      · exact ⟨outArc A 0 r, (hrows _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)))),
          by rw [absG_outArc hA hr]; simp [inRow]⟩
      · refine ⟨arc (b + 1) t c, (hrows _).mpr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨b + 1, by omega, by omega, t, ht, c, rfl⟩)))), ?_⟩
        rw [absG_arc, if_neg (by omega)]; rfl
  · show (G₁.rows.map (absG A)).Pairwise (hybLtS A J 0)
    exact List.pairwise_map.mpr (hsort.imp_of_mem fun ha hb h =>
      absorb_mono hA ((hrows _).mp ha) ((hrows _).mp hb) h)

end Stage3

/-- **Lemma absorption.** `H_{A+1,k}(β^{J+1})` is related by grid moves to
`H_{A+1,k+1}(β^J)`. -/
theorem IsHybrid.exists_absorb {n A k J : ℕ} (hA : 1 ≤ A) (hk : 1 ≤ k)
    {G : LabeledGrid n TorusCol TorusRow} (hG : IsHybrid A k (J + 1) G) :
    ∃ (n' : ℕ) (G' : LabeledGrid n' TorusCol TorusRow), IsHybrid A (k + 1) J G' ∧
      G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨m, G₀, -, h₀, hmv₀⟩ := hG.exists_stage3_start hA
  obtain ⟨m', G₂, -, h₂, hmv₂⟩ := h₀.exists_all hA
  obtain ⟨G₃, hc₃, hO₃, hX₃, hr₃, hs₃, hmv₃⟩ := h₂.exists_swapped hA hk
  obtain ⟨G₄, h₄, he₄⟩ := h₂.exists_isHybrid hA hk hc₃ hO₃ hX₃ hr₃ hs₃
  refine ⟨m', G₄, h₄, hmv₀.trans (hmv₂.trans ?_)⟩
  rw [he₄]
  exact hmv₃

end OnLeConjecture.KnotTheory
