/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesMacros

/-!
# Inserting a protected grid into a row of a labeled grid

The marked inverse cancellation of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 8) carries a protected grid `H` along one horizontal
arc. Here `H` is a grid diagram of size `m + 1` with `H.X 0 = 0` and `H.O (last m) = 0`, as for the
left factor of the binary seam. Its row `0` contains the `X` marking of the first column and the
`O` marking of the last column. A *protected block* (`ProtBlock`) labels the `m + 1` columns of `H`
and `m + 2` rows: the input row (the half of row `0` carrying the `X` marking of the first column),
the internal rows `1, …, m`, and the output row (the half of row `0` carrying the `O` marking of the
last column). This is the framed insertion of the written proof: the first column of `H` has its
`X` marking in the input row, its last column has its `O` marking in the output row, and every
other marking of `H` is in an internal row.

`insertBlock G α P D` inserts the block `P` into the row `α` of a labeled grid `G`: the block
columns are inserted at a chosen position of the column list, and the row `α` is replaced by the
rows of the block, in their order. The column of `G` carrying the `O` marking of `α` now has its `O`
marking in the input row, and the column carrying the `X` marking of `α` has its `X` marking in the
output row. The labels of the block rows may reuse the label `α` for the input or the output row,
so that a half of `α` meeting a window keeps its window label.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory

/-- A protected block with column labels in `C` and row labels in `R`: a grid diagram `H` of size
`m + 1` prepared as the left factor of a binary seam, with labels for its `m + 1` columns and for
its `m + 2` rows (input row, internal rows `1, …, m`, output row). -/
structure ProtBlock (m : ℕ) (C R : Type*) where
  /-- The protected grid. -/
  H : GridDiagram (m + 1)
  /-- The labels of the columns of `H`. -/
  hc : Fin (m + 1) → C
  /-- The labels of the rows: `hr 0` is the input row, `hr k` for `1 ≤ k ≤ m` the internal row
  `k` of `H`, and `hr (last (m + 1))` the output row. -/
  hr : Fin (m + 2) → R
  hc_inj : Function.Injective hc
  hr_inj : Function.Injective hr
  X_zero : H.X 0 = 0
  O_last : H.O (Fin.last m) = 0

namespace ProtBlock

variable {m : ℕ} {C R : Type*} (P : ProtBlock m C R)

/-- The `O` row of a block column: the output row for the last column. -/
def oRow (j : Fin (m + 1)) : R :=
  if P.H.O j = 0 then P.hr (Fin.last (m + 1)) else P.hr (P.H.O j).castSucc

/-- The `X` row of a block column: the input row for the first column. -/
def xRow (j : Fin (m + 1)) : R := P.hr (P.H.X j).castSucc

theorem oRow_ne_input (j : Fin (m + 1)) : P.oRow j ≠ P.hr 0 := by
  unfold oRow
  split_ifs with h
  · exact fun h' => (Fin.last_pos (n := m)).ne' (P.hr_inj h')
  · intro h'
    have := P.hr_inj h'
    exact h (Fin.castSucc_injective _ (this.trans Fin.castSucc_zero.symm))

theorem xRow_ne_output (j : Fin (m + 1)) : P.xRow j ≠ P.hr (Fin.last (m + 1)) := fun h =>
  Fin.castSucc_ne_last _ (P.hr_inj h)

theorem oRow_inj {j j' : Fin (m + 1)} (h : P.oRow j = P.oRow j') : j = j' := by
  unfold oRow at h
  split_ifs at h with h1 h2 h2
  · exact P.H.O.toPerm.injective (h1.trans h2.symm)
  · exact absurd (P.hr_inj h).symm (Fin.castSucc_ne_last _)
  · exact absurd (P.hr_inj h) (Fin.castSucc_ne_last _)
  · exact P.H.O.toPerm.injective (Fin.castSucc_injective _ (P.hr_inj h))

theorem xRow_inj {j j' : Fin (m + 1)} (h : P.xRow j = P.xRow j') : j = j' :=
  P.H.X.toPerm.injective (Fin.castSucc_injective _ (P.hr_inj h))

theorem oRow_ne_xRow (j : Fin (m + 1)) : P.oRow j ≠ P.xRow j := by
  unfold oRow xRow
  split_ifs with h
  · exact fun h' => Fin.castSucc_ne_last _ (P.hr_inj h').symm
  · exact fun h' => P.H.disjoint j (Fin.castSucc_injective _ (P.hr_inj h'))

theorem input_ne_output : P.hr 0 ≠ P.hr (Fin.last (m + 1)) := fun h =>
  (Fin.last_pos (n := m)).ne (P.hr_inj h)

/-- The first column carries the input row. -/
theorem xRow_zero : P.xRow 0 = P.hr 0 := by
  unfold xRow; rw [P.X_zero, Fin.castSucc_zero]

/-- The last column carries the output row. -/
theorem oRow_last : P.oRow (Fin.last m) = P.hr (Fin.last (m + 1)) := by
  unfold oRow; rw [if_pos P.O_last]

/-- The column labels of the block. -/
def cols : List C := List.ofFn P.hc

/-- The row labels of the block, from the input row to the output row. -/
def rows : List R := List.ofFn P.hr

theorem cols_length : P.cols.length = m + 1 := by simp [cols]

theorem rows_length : P.rows.length = m + 2 := by simp [rows]

theorem cols_nodup : P.cols.Nodup := List.nodup_ofFn.mpr P.hc_inj

theorem rows_nodup : P.rows.Nodup := List.nodup_ofFn.mpr P.hr_inj

theorem mem_cols {c : C} : c ∈ P.cols ↔ ∃ j, P.hc j = c := by
  unfold cols; exact List.mem_ofFn

theorem mem_rows {x : R} : x ∈ P.rows ↔ ∃ k, P.hr k = x := by
  unfold rows; exact List.mem_ofFn

theorem hc_mem (j : Fin (m + 1)) : P.hc j ∈ P.cols := P.mem_cols.mpr ⟨j, rfl⟩

theorem hr_mem (k : Fin (m + 2)) : P.hr k ∈ P.rows := P.mem_rows.mpr ⟨k, rfl⟩

/-- The index of a block column label. -/
def bidx [DecidableEq C] (c : C) : ℕ := P.cols.idxOf c

theorem bidx_hc [DecidableEq C] (j : Fin (m + 1)) : P.bidx (P.hc j) = j.val := by
  unfold bidx
  have h := P.cols_nodup.idxOf_getElem j.val (by rw [P.cols_length]; exact j.isLt)
  simp only [cols, List.getElem_ofFn] at h
  exact h

theorem bidx_lt [DecidableEq C] {c : C} (h : c ∈ P.cols) : P.bidx c < m + 1 := by
  have := List.idxOf_lt_length_iff.mpr h; rw [P.cols_length] at this; exact this

end ProtBlock

/-! ### The insertion -/

section Insert

variable {n m : ℕ} {C R : Type*}

/-- The data of an insertion of a protected block into the row `α` of `G`: the row `α` splits
the rows as `m₁ ++ α :: m₂`, the block columns are inserted between `l₁` and `l₂`, the block
columns are new, and the block row labels are new except that the input or the output row may be
labelled `α`. -/
structure InsertData (G : LabeledGrid n C R) (α : R) (P : ProtBlock m C R) : Type _ where
  l₁ : List C
  l₂ : List C
  m₁ : List R
  m₂ : List R
  cols_eq : G.cols = l₁ ++ l₂
  rows_eq : G.rows = m₁ ++ α :: m₂
  cols_fresh : ∀ j, P.hc j ∉ G.cols
  rows_fresh : ∀ k, P.hr k ∈ G.rows → P.hr k = α

variable {G : LabeledGrid n C R} {α : R} {P : ProtBlock m C R}

variable (G α P) in
/-- The `O` row of a column after the insertion. -/
def blockO [DecidableEq C] [DecidableEq R] (c : C) : R :=
  if h : c ∈ P.cols then P.oRow ⟨P.bidx c, P.bidx_lt h⟩
  else if G.O c = α then P.hr 0 else G.O c

variable (G α P) in
/-- The `X` row of a column after the insertion. -/
def blockX [DecidableEq C] [DecidableEq R] (c : C) : R :=
  if h : c ∈ P.cols then P.xRow ⟨P.bidx c, P.bidx_lt h⟩
  else if G.X c = α then P.hr (Fin.last (m + 1)) else G.X c

theorem blockO_hc [DecidableEq C] [DecidableEq R] (j : Fin (m + 1)) :
    blockO G α P (P.hc j) = P.oRow j := by
  unfold blockO
  rw [dif_pos (P.hc_mem j)]
  congr 1
  exact Fin.ext (P.bidx_hc j)

theorem blockX_hc [DecidableEq C] [DecidableEq R] (j : Fin (m + 1)) :
    blockX G α P (P.hc j) = P.xRow j := by
  unfold blockX
  rw [dif_pos (P.hc_mem j)]
  congr 1
  exact Fin.ext (P.bidx_hc j)

namespace InsertData

variable (D : InsertData G α P)
include D

theorem not_mem_block_of_mem {c : C} (hc : c ∈ G.cols) : c ∉ P.cols := by
  intro h
  obtain ⟨j, rfl⟩ := P.mem_cols.mp h
  exact D.cols_fresh j hc

theorem blockO_old [DecidableEq C] [DecidableEq R] {c : C} (hc : c ∈ G.cols) :
    blockO G α P c = if G.O c = α then P.hr 0 else G.O c := by
  unfold blockO; rw [dif_neg (D.not_mem_block_of_mem hc)]

theorem blockX_old [DecidableEq C] [DecidableEq R] {c : C} (hc : c ∈ G.cols) :
    blockX G α P c = if G.X c = α then P.hr (Fin.last (m + 1)) else G.X c := by
  unfold blockX; rw [dif_neg (D.not_mem_block_of_mem hc)]

theorem alpha_mem : α ∈ G.rows := by rw [D.rows_eq]; simp

theorem not_mem_m₁ : α ∉ D.m₁ := by
  have h := G.rows_nodup; rw [D.rows_eq] at h
  exact fun h' => LabeledGrid.not_mem_of_nodup_middle h (List.mem_append_left _ h')

theorem not_mem_m₂ : α ∉ D.m₂ := by
  have h := G.rows_nodup; rw [D.rows_eq] at h
  exact fun h' => LabeledGrid.not_mem_of_nodup_middle h (List.mem_append_right _ h')

/-- A block row label met in an old row other than `α` is impossible. -/
theorem hr_not_mem_of_ne {k : Fin (m + 2)} {x : R} (hx : x ∈ G.rows) (hxα : x ≠ α) :
    P.hr k ≠ x := by
  intro h; subst h; exact hxα (D.rows_fresh k hx)

/-- The new list of columns. -/
def newCols : List C := D.l₁ ++ P.cols ++ D.l₂

/-- The new list of rows. -/
def newRows : List R := D.m₁ ++ P.rows ++ D.m₂

theorem mem_newCols {c : C} : c ∈ D.newCols ↔ c ∈ G.cols ∨ c ∈ P.cols := by
  rw [D.cols_eq]
  simp only [newCols, List.mem_append]
  tauto

theorem mem_newRows_of_mem {x : R} (hx : x ∈ G.rows) (hxα : x ≠ α) : x ∈ D.newRows := by
  rw [D.rows_eq] at hx
  simp only [newRows, List.mem_append, List.mem_cons] at hx ⊢
  tauto

theorem hr_mem_newRows (k : Fin (m + 2)) : P.hr k ∈ D.newRows := by
  simp only [newRows, List.mem_append]; exact Or.inl (Or.inr (P.hr_mem k))

theorem newCols_nodup : D.newCols.Nodup := by
  have hG := G.cols_nodup
  rw [D.cols_eq] at hG
  have hdisj : ∀ c ∈ P.cols, c ∉ D.l₁ ++ D.l₂ := by
    intro c hc hc'
    rw [← D.cols_eq] at hc'
    exact D.not_mem_block_of_mem hc' hc
  unfold newCols
  rw [List.nodup_append, List.nodup_append]
  rw [List.nodup_append] at hG
  refine ⟨⟨hG.1, P.cols_nodup, ?_⟩, hG.2.1, ?_⟩
  · intro a ha b hb hab; subst hab; exact hdisj a hb (List.mem_append_left _ ha)
  · intro a ha b hb hab; subst hab
    simp only [List.mem_append] at ha
    rcases ha with ha | ha
    · exact hG.2.2 a ha a hb rfl
    · exact hdisj a ha (List.mem_append_right _ hb)

theorem newRows_nodup : D.newRows.Nodup := by
  have hG := G.rows_nodup
  rw [D.rows_eq] at hG
  have h1 : (D.m₁ ++ D.m₂).Nodup := LabeledGrid.nodup_of_nodup_middle hG
  have hdisj : ∀ x ∈ P.rows, x ∉ D.m₁ ++ D.m₂ := by
    intro x hx hx'
    obtain ⟨k, rfl⟩ := P.mem_rows.mp hx
    have hmem : P.hr k ∈ G.rows := by
      rw [D.rows_eq]; exact LabeledGrid.mem_middle_of_mem hx'
    have := D.rows_fresh k hmem
    rw [this] at hx'
    simp only [List.mem_append] at hx'
    rcases hx' with h | h
    · exact D.not_mem_m₁ h
    · exact D.not_mem_m₂ h
  unfold newRows
  rw [List.nodup_append, List.nodup_append]
  rw [List.nodup_append] at h1
  refine ⟨⟨h1.1, P.rows_nodup, ?_⟩, h1.2.1, ?_⟩
  · intro a ha b hb hab; subst hab; exact hdisj a hb (List.mem_append_left _ ha)
  · intro a ha b hb hab; subst hab
    simp only [List.mem_append] at ha
    rcases ha with ha | ha
    · exact h1.2.2 a ha a hb rfl
    · exact hdisj a ha (List.mem_append_right _ hb)

end InsertData

/-- **The insertion of a protected block into a row.** -/
def insertBlock [DecidableEq C] [DecidableEq R] (G : LabeledGrid n C R) (α : R)
    (P : ProtBlock m C R) (D : InsertData G α P) : LabeledGrid (n + m + 1) C R where
  cols := D.newCols
  rows := D.newRows
  O := blockO G α P
  X := blockX G α P
  cols_length := by
    have h := G.cols_length
    rw [D.cols_eq, List.length_append] at h
    simp only [InsertData.newCols, List.length_append, P.cols_length]; omega
  rows_length := by
    have h := G.rows_length
    rw [D.rows_eq] at h
    simp only [InsertData.newRows, List.length_append, List.length_cons] at h ⊢
    rw [P.rows_length]; omega
  cols_nodup := D.newCols_nodup
  rows_nodup := D.newRows_nodup
  O_mem c hc := by
    rcases D.mem_newCols.mp hc with hc | hc
    · rw [D.blockO_old hc]
      split_ifs with h
      · exact D.hr_mem_newRows 0
      · exact D.mem_newRows_of_mem (G.O_mem c hc) h
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc
      rw [blockO_hc]
      unfold ProtBlock.oRow
      split_ifs <;> exact D.hr_mem_newRows _
  X_mem c hc := by
    rcases D.mem_newCols.mp hc with hc | hc
    · rw [D.blockX_old hc]
      split_ifs with h
      · exact D.hr_mem_newRows _
      · exact D.mem_newRows_of_mem (G.X_mem c hc) h
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc
      rw [blockX_hc]; exact D.hr_mem_newRows _
  O_inj c hc c' hc' h := by
    rcases D.mem_newCols.mp hc with hc | hc <;> rcases D.mem_newCols.mp hc' with hc' | hc'
    · rw [D.blockO_old hc, D.blockO_old hc'] at h
      split_ifs at h with h1 h2 h2
      · exact G.O_inj c hc c' hc' (h1.trans h2.symm)
      · exact absurd h (D.hr_not_mem_of_ne (G.O_mem c' hc') h2)
      · exact absurd h.symm (D.hr_not_mem_of_ne (G.O_mem c hc) h1)
      · exact G.O_inj c hc c' hc' h
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc'
      rw [D.blockO_old hc, blockO_hc] at h
      split_ifs at h with h1
      · exact absurd h.symm (P.oRow_ne_input j)
      · exfalso
        unfold ProtBlock.oRow at h
        split_ifs at h <;> exact D.hr_not_mem_of_ne (G.O_mem c hc) h1 h.symm
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc
      rw [D.blockO_old hc', blockO_hc] at h
      split_ifs at h with h1
      · exact absurd h (P.oRow_ne_input j)
      · exfalso
        unfold ProtBlock.oRow at h
        split_ifs at h <;> exact D.hr_not_mem_of_ne (G.O_mem c' hc') h1 h
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc
      obtain ⟨j', rfl⟩ := P.mem_cols.mp hc'
      rw [blockO_hc, blockO_hc] at h
      rw [P.oRow_inj h]
  X_inj c hc c' hc' h := by
    rcases D.mem_newCols.mp hc with hc | hc <;> rcases D.mem_newCols.mp hc' with hc' | hc'
    · rw [D.blockX_old hc, D.blockX_old hc'] at h
      split_ifs at h with h1 h2 h2
      · exact G.X_inj c hc c' hc' (h1.trans h2.symm)
      · exact absurd h (D.hr_not_mem_of_ne (G.X_mem c' hc') h2)
      · exact absurd h.symm (D.hr_not_mem_of_ne (G.X_mem c hc) h1)
      · exact G.X_inj c hc c' hc' h
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc'
      rw [D.blockX_old hc, blockX_hc] at h
      split_ifs at h with h1
      · exact absurd h.symm (P.xRow_ne_output j)
      · exact absurd h.symm (D.hr_not_mem_of_ne (G.X_mem c hc) h1)
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc
      rw [D.blockX_old hc', blockX_hc] at h
      split_ifs at h with h1
      · exact absurd h (P.xRow_ne_output j)
      · exact absurd h (D.hr_not_mem_of_ne (G.X_mem c' hc') h1)
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc
      obtain ⟨j', rfl⟩ := P.mem_cols.mp hc'
      rw [blockX_hc, blockX_hc] at h
      rw [P.xRow_inj h]
  O_ne_X c hc := by
    rcases D.mem_newCols.mp hc with hc | hc
    · rw [D.blockO_old hc, D.blockX_old hc]
      have hne := G.O_ne_X c hc
      split_ifs with h1 h2 h2
      · exact absurd (h1.trans h2.symm) hne
      · exact D.hr_not_mem_of_ne (G.X_mem c hc) h2
      · exact Ne.symm (D.hr_not_mem_of_ne (G.O_mem c hc) h1)
      · exact hne
    · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc
      rw [blockO_hc, blockX_hc]; exact P.oRow_ne_xRow j

end Insert

end OnLeConjecture.KnotTheory.MarkedCancel
