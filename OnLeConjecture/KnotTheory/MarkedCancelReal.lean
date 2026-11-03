/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelInsert
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationReal

/-!
# Window realizations of grids with a protected block

Let `G` realize a window state `S` (`BraidWindow.Real S G W Q`): the window columns come first,
with the labels and markings of `S`, followed by the outside columns. Inserting a protected block
into a row of `G` (`insertBlock`, `MarkedCancelInsert`) places the block columns among the outside
columns. The inserted grid realizes a window state `S'` with the same number of columns as soon
as the window columns carry the markings of `S'` and the window rows are the rows of `S'`
(`real_insertBlock`). Two cases are used for the marked inverse cancellation of the written proof
of Statement E (`statement_E_complete_proof.tex`, Section 8):

* the row `α` meets no window column (`real_insertBlock_of_outside`): `S' = S`;
* the row `α` is a window label: the window columns carrying its `O` and `X` markings now carry
  the input and the output rows of the block (`blockO_window`, `blockX_window`).

The rows of the inserted grid are described by `lefts_newRows`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory BraidWindow

variable {n m : ℕ} {S S' : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
  {Q : List (ℕ × Fin 3)} {α : BRow} {P : ProtBlock m BCol BRow}

/-- **The window realization of an inserted grid.** The block columns are inserted among the
outside columns. -/
theorem real_insertBlock (hR : Real S G W Q) (D : InsertData G α P) {Q₁ Q₂ qH : List (ℕ × Fin 3)}
    (hl₁ : D.l₁ = W.map Sum.inl ++ Q₁.map Sum.inr) (hl₂ : D.l₂ = Q₂.map Sum.inr)
    (hcols : P.cols = qH.map Sum.inr) (hlen : S'.cols.length = S.cols.length)
    (hmarks : ∀ p ∈ W.zip S'.cols, blockO G α P (Sum.inl p.1) = Sum.inl p.2.1 ∧
      blockX G α P (Sum.inl p.1) = Sum.inl p.2.2)
    (hrows : lefts D.newRows = S'.rows) :
    Real S' (insertBlock G α P D) W (Q₁ ++ qH ++ Q₂) where
  cols := by
    change D.l₁ ++ P.cols ++ D.l₂ = _
    rw [hl₁, hl₂, hcols]
    simp only [List.map_append, List.append_assoc]
  len := hR.len.trans hlen.symm
  marks := hmarks
  rows := hrows

theorem mem_cols_of_mem_W (hR : Real S G W Q) {w : ℕ} (hw : w ∈ W) : Sum.inl w ∈ G.cols := by
  rw [hR.cols]; exact List.mem_append_left _ (List.mem_map_of_mem hw)

/-- The window `O` markings after the insertion. -/
theorem blockO_window (hR : Real S G W Q) (D : InsertData G α P) {w : ℕ} (hw : w ∈ W) :
    blockO G α P (Sum.inl w) =
      if G.O (Sum.inl w) = α then P.hr 0 else G.O (Sum.inl w) :=
  D.blockO_old (mem_cols_of_mem_W hR hw)

/-- The window `X` markings after the insertion. -/
theorem blockX_window (hR : Real S G W Q) (D : InsertData G α P) {w : ℕ} (hw : w ∈ W) :
    blockX G α P (Sum.inl w) =
      if G.X (Sum.inl w) = α then P.hr (Fin.last (m + 1)) else G.X (Sum.inl w) :=
  D.blockX_old (mem_cols_of_mem_W hR hw)

/-- The window rows after the insertion. -/
theorem lefts_newRows (D : InsertData G α P) :
    lefts D.newRows = lefts D.m₁ ++ lefts P.rows ++ lefts D.m₂ := by
  simp only [InsertData.newRows, lefts_append]

theorem lefts_rows_eq (D : InsertData G α P) :
    lefts G.rows = lefts D.m₁ ++ lefts [α] ++ lefts D.m₂ := by
  rw [D.rows_eq, show D.m₁ ++ α :: D.m₂ = D.m₁ ++ [α] ++ D.m₂ by simp]
  simp only [lefts_append]

/-- **Insertion into a row outside the window.** If the row `α` and the block rows are outside
labels, the inserted grid realizes the same window state. -/
theorem real_insertBlock_of_outside (hR : Real S G W Q) (D : InsertData G α P)
    {Q₁ Q₂ qH : List (ℕ × Fin 3)} (hl₁ : D.l₁ = W.map Sum.inl ++ Q₁.map Sum.inr)
    (hl₂ : D.l₂ = Q₂.map Sum.inr) (hcols : P.cols = qH.map Sum.inr) (hα : ∃ a, α = Sum.inr a)
    (hP : ∀ k, ∃ a, P.hr k = Sum.inr a) :
    Real S (insertBlock G α P D) W (Q₁ ++ qH ++ Q₂) := by
  obtain ⟨a, rfl⟩ := hα
  refine real_insertBlock hR D hl₁ hl₂ hcols rfl (fun p hp => ?_) ?_
  · have hw : p.1 ∈ W := (List.of_mem_zip hp).1
    obtain ⟨h1, h2⟩ := hR.marks p hp
    rw [blockO_window hR D hw, blockX_window hR D hw, h1, h2]
    simp
  · have hl : lefts P.rows = [] := by
      simp only [lefts, List.filterMap_eq_nil_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := P.mem_rows.mp hx
      obtain ⟨b, hb⟩ := hP k
      rw [hb]; rfl
    have hα' : lefts [(Sum.inr a : BRow)] = [] := rfl
    rw [lefts_newRows, hl, ← hR.rows, lefts_rows_eq D, hα']

end OnLeConjecture.KnotTheory.MarkedCancel
