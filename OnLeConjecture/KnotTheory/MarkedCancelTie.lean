/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelGrid
public import OnLeConjecture.KnotTheory.EndpointCleanupSort

/-!
# Positions in marked word grids

This file collects the facts about the positions of columns and rows in a marked word grid
(`markedGrid`, `MarkedCancelGrid`) used to compare marked word grids with different tie orders.

* `nonintN_map_strictMono`: non-interleaving of two pairs of positions only depends on their
  relative order, so it is preserved by strictly monotone maps.
* `markedGrid_cpos_word`, `markedGrid_cpos_block`: the block columns follow the column of the
  marked corner `p`; the word columns after it are shifted by the size of the block.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow

/-! ### Order invariance of non-interleaving -/

theorem cIooN_map_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (a b x : ℕ) :
    CIooN (f a) (f b) (f x) ↔ CIooN a b x := by
  unfold CIooN
  simp only [hf.injective.ne_iff, hf.lt_iff_lt]

theorem nonintN_map_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (a₀ a₁ b₀ b₁ : ℕ) :
    NonintN (f a₀) (f a₁) (f b₀) (f b₁) ↔ NonintN a₀ a₁ b₀ b₁ := by
  unfold NonintN
  rw [cIooN_map_strictMono hf, cIooN_map_strictMono hf, cIooN_map_strictMono hf,
    cIooN_map_strictMono hf]

/-- The shift of positions by `d` after the position `s`. -/
def shiftAfter (s d i : ℕ) : ℕ := if i ≤ s then i else i + d

/-- The shift of positions by `d` from the position `s` on. -/
def shiftFrom (s d i : ℕ) : ℕ := if i < s then i else i + d

theorem shiftAfter_strictMono (s d : ℕ) : StrictMono (shiftAfter s d) := by
  intro i j hij
  unfold shiftAfter
  split_ifs <;> omega

theorem shiftFrom_strictMono (s d : ℕ) : StrictMono (shiftFrom s d) := by
  intro i j hij
  unfold shiftFrom
  split_ifs <;> omega

theorem shiftFrom_eq_shiftAfter {s d i : ℕ} (hi : i ≠ s) : shiftFrom s d i = shiftAfter s d i := by
  unfold shiftFrom shiftAfter
  split_ifs <;> omega

/-! ### Column positions in a marked word grid -/

section Positions

variable {m k : ℕ} (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ) (hL : 0 < v.length)
  (p : Fin v.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
  (hO : H.O (Fin.last k) = 0)

theorem markedGrid_cols :
    (markedGrid v κ hL p H hX hO).cols =
      ((sCols v).take (finProdFinEquiv p + 1)).map (sfCol 0 v) ++
        (markBlock v H hX hO).cols ++
        ((sCols v).drop (finProdFinEquiv p + 1)).map (sfCol 0 v) := rfl

theorem sCols_getElem (v : SignedAdjacentWord m) (i : ℕ) (hi : i < (sCols v).length) :
    (sCols v)[i] = finProdFinEquiv.symm ⟨i, by rw [sCols_length] at hi; exact hi⟩ := by
  simp [sCols]

/-- The label at an index of a list without duplicates has that index as position. -/
theorem cpos_of_getElem {n : ℕ} {C R : Type*} [DecidableEq C] (G : LabeledGrid n C R) {c : C}
    {j : ℕ} (hj : j < G.cols.length) (h : G.cols[j] = c) : G.cpos c = j := by
  rw [← h]; exact G.cols_nodup.idxOf_getElem j hj

theorem sCols_map_getElem (v : SignedAdjacentWord m) (q : Fin v.length × Fin 3)
    (hq : (finProdFinEquiv q).val < ((sCols v).map (sfCol 0 v)).length) :
    ((sCols v).map (sfCol 0 v))[(finProdFinEquiv q).val] = Sum.inr (q.1.val, q.2) := by
  rw [List.getElem_map, sCols_getElem]
  simp only [Fin.eta, Equiv.symm_apply_apply, sfCol_zero]

/-- The position of a word column: shifted by the block after the column of `p`. -/
theorem markedGrid_cpos_word (q : Fin v.length × Fin 3) :
    (markedGrid v κ hL p H hX hO).cpos (Sum.inr (q.1.val, q.2)) =
      shiftAfter (finProdFinEquiv p) (k + 1) (finProdFinEquiv q) := by
  set L := (sCols v).map (sfCol 0 v) with hLdef
  have hlen : L.length = v.length * 3 := by simp [hLdef, sCols_length]
  have hpl := (finProdFinEquiv p).isLt
  have hql := (finProdFinEquiv q).isLt
  set s := (finProdFinEquiv p).val + 1 with hs
  have hPl : (markBlock v H hX hO).cols.length = k + 1 := ProtBlock.cols_length _
  have hcols : (markedGrid v κ hL p H hX hO).cols =
      L.take s ++ (markBlock v H hX hO).cols ++ L.drop s := by
    rw [markedGrid_cols, ← List.map_take, ← List.map_drop]
  have htake : (L.take s).length = s := by rw [List.length_take]; omega
  have hcl : (markedGrid v κ hL p H hX hO).cols.length = v.length * 3 + k + 1 := by
    rw [hcols]; simp only [List.length_append, htake, hPl, List.length_drop, hlen]; omega
  unfold shiftAfter
  split_ifs with hqs
  · refine cpos_of_getElem _ (by rw [hcl]; omega) ?_
    simp only [hcols]
    rw [List.getElem_append_left (by simp only [List.length_append, htake, hPl]; omega),
      List.getElem_append_left (by rw [htake]; omega), List.getElem_take]
    exact sCols_map_getElem v q (by rw [hlen]; exact hql)
  · refine cpos_of_getElem _ (by rw [hcl]; omega) ?_
    simp only [hcols]
    rw [List.getElem_append_right (by simp only [List.length_append, htake, hPl]; omega),
      List.getElem_drop]
    have he : s + ((finProdFinEquiv q).val + (k + 1) - ((L.take s) ++
        (markBlock v H hX hO).cols).length) = (finProdFinEquiv q).val := by
      simp only [List.length_append, htake, hPl]; omega
    simp only [he]
    exact sCols_map_getElem v q (by rw [hlen]; exact hql)

/-- The position of a block column: right after the column of `p`. -/
theorem markedGrid_cpos_block (j : Fin (k + 1)) :
    (markedGrid v κ hL p H hX hO).cpos ((markBlock v H hX hO).hc j) =
      (finProdFinEquiv p).val + 1 + j.val := by
  set L := (sCols v).map (sfCol 0 v) with hLdef
  have hlen : L.length = v.length * 3 := by simp [hLdef, sCols_length]
  have hpl := (finProdFinEquiv p).isLt
  set s := (finProdFinEquiv p).val + 1 with hs
  have hPl : (markBlock v H hX hO).cols.length = k + 1 := ProtBlock.cols_length _
  have hcols : (markedGrid v κ hL p H hX hO).cols =
      L.take s ++ (markBlock v H hX hO).cols ++ L.drop s := by
    rw [markedGrid_cols, ← List.map_take, ← List.map_drop]
  have htake : (L.take s).length = s := by rw [List.length_take]; omega
  have hcl : (markedGrid v κ hL p H hX hO).cols.length = v.length * 3 + k + 1 := by
    rw [hcols]; simp only [List.length_append, htake, hPl, List.length_drop, hlen]; omega
  have hj := j.isLt
  refine cpos_of_getElem _ (by rw [hcl]; omega) ?_
  simp only [hcols]
  rw [List.getElem_append_left (by simp only [List.length_append, htake, hPl]; omega),
    List.getElem_append_right (by rw [htake]; omega)]
  simp only [ProtBlock.cols, List.getElem_ofFn, htake]
  congr 1
  exact Fin.ext (by simp only; omega)

end Positions

/-! ### Markings of a marked word grid -/

section Marks

variable {m k : ℕ} (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ) (hL : 0 < v.length)
  (p : Fin v.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
  (hO : H.O (Fin.last k) = 0)

theorem inr_corner_inj {a b : Fin v.length × Fin 3}
    (h : (Sum.inr (a.1.val, a.2) : BCol) = Sum.inr (b.1.val, b.2)) : a = b := by
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem word_mem_plain (q : Fin v.length × Fin 3) :
    (Sum.inr (q.1.val, q.2) : BCol) ∈ (plainGrid v κ hL).cols :=
  mem_plainGrid_cols.mpr ⟨q, rfl⟩

theorem markedGrid_word_mem (q : Fin v.length × Fin 3) :
    (Sum.inr (q.1.val, q.2) : BCol) ∈ (markedGrid v κ hL p H hX hO).cols :=
  (markData v κ hL p H hX hO).mem_newCols.mpr (Or.inl (word_mem_plain v κ hL q))

theorem markedGrid_block_mem (j : Fin (k + 1)) :
    (markBlock v H hX hO).hc j ∈ (markedGrid v κ hL p H hX hO).cols :=
  (markData v κ hL p H hX hO).mem_newCols.mpr (Or.inr ((markBlock v H hX hO).hc_mem j))

/-- Every word column other than the column of `p` keeps its `O` label. -/
theorem markedGrid_O_word (q : Fin v.length × Fin 3) (hq : q ≠ p) :
    (markedGrid v κ hL p H hX hO).O (Sum.inr (q.1.val, q.2)) = Sum.inr (q.1.val, q.2) := by
  change blockO (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO) _ = _
  rw [(markData v κ hL p H hX hO).blockO_old (word_mem_plain v κ hL q), plainGrid_O,
    if_neg (fun h => hq (inr_corner_inj v h))]

/-- The column of `p` carries the input row of the block. -/
theorem markedGrid_O_p :
    (markedGrid v κ hL p H hX hO).O (Sum.inr (p.1.val, p.2)) = (markBlock v H hX hO).hr 0 := by
  change blockO (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO) _ = _
  rw [(markData v κ hL p H hX hO).blockO_old (word_mem_plain v κ hL p), plainGrid_O, if_pos rfl]

theorem markedGrid_X_word (q : Fin v.length × Fin 3) (hq : q ≠ sM v p) :
    (markedGrid v κ hL p H hX hO).X (Sum.inr (q.1.val, q.2)) =
      Sum.inr (((sM v).symm q).1.val, ((sM v).symm q).2) := by
  change blockX (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO) _ = _
  rw [(markData v κ hL p H hX hO).blockX_old (word_mem_plain v κ hL q), plainGrid_X,
    if_neg]
  intro h
  apply hq
  rw [← inr_corner_inj v h, Equiv.apply_symm_apply]

/-- The column where the marked arc ends carries the output row. -/
theorem markedGrid_X_sMp :
    (markedGrid v κ hL p H hX hO).X (Sum.inr ((sM v p).1.val, (sM v p).2)) =
      (markBlock v H hX hO).hr (Fin.last (k + 1)) := by
  change blockX (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO) _ = _
  rw [(markData v κ hL p H hX hO).blockX_old (word_mem_plain v κ hL _), plainGrid_X,
    Equiv.symm_apply_apply, if_pos rfl]

theorem markedGrid_O_block (j : Fin (k + 1)) :
    (markedGrid v κ hL p H hX hO).O ((markBlock v H hX hO).hc j) =
      (markBlock v H hX hO).oRow j := blockO_hc j

theorem markedGrid_X_block (j : Fin (k + 1)) :
    (markedGrid v κ hL p H hX hO).X ((markBlock v H hX hO).hc j) =
      (markBlock v H hX hO).xRow j := blockX_hc j

theorem markedGrid_rows :
    (markedGrid v κ hL p H hX hO).rows = (markData v κ hL p H hX hO).m₁ ++
      (markBlock v H hX hO).rows ++ (markData v κ hL p H hX hO).m₂ := rfl

/-- The columns of a marked word grid are word columns or block columns. -/
theorem markedGrid_mem_cols {c : BCol} (hc : c ∈ (markedGrid v κ hL p H hX hO).cols) :
    (∃ q : Fin v.length × Fin 3, c = Sum.inr (q.1.val, q.2)) ∨
      ∃ j, c = (markBlock v H hX hO).hc j := by
  rcases (markData v κ hL p H hX hO).mem_newCols.mp hc with h | h
  · exact Or.inl (mem_plainGrid_cols.mp h)
  · obtain ⟨j, rfl⟩ := (markBlock v H hX hO).mem_cols.mp h; exact Or.inr ⟨j, rfl⟩

/-- The rows of a marked word grid are the rows of the other arcs and the block rows. -/
theorem markedGrid_mem_rows {x : BRow} (hx : x ∈ (markedGrid v κ hL p H hX hO).rows) :
    (∃ q : Fin v.length × Fin 3, q ≠ p ∧ x = Sum.inr (q.1.val, q.2)) ∨
      x ∈ (markBlock v H hX hO).rows := by
  have hD := (markData v κ hL p H hX hO).rows_eq
  rw [markedGrid_rows] at hx
  simp only [List.mem_append] at hx
  rcases hx with (h | h) | h
  · left
    have hm : x ∈ (plainGrid v κ hL).rows := by rw [hD]; simp [h]
    obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hm
    refine ⟨q, fun hqp => ?_, rfl⟩
    rw [hqp] at h
    exact (markData v κ hL p H hX hO).not_mem_m₁ h
  · exact Or.inr h
  · left
    have hm : x ∈ (plainGrid v κ hL).rows := by rw [hD]; simp [h]
    obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hm
    refine ⟨q, fun hqp => ?_, rfl⟩
    rw [hqp] at h
    exact (markData v κ hL p H hX hO).not_mem_m₂ h

/-! ### Heights of the rows -/

/-- The height of a row of a marked word grid: the outgoing height of its arc, and the height of
the marked arc for the block rows. -/
def htRow : BRow → ℕ
  | Sum.inr a => if a.1 < v.length then v.oHeight2 (sCornerOf v hL a) else v.oHeight2 p
  | Sum.inl _ => 0

theorem htRow_word (q : Fin v.length × Fin 3) :
    htRow v hL p (Sum.inr (q.1.val, q.2)) = v.oHeight2 q := by
  simp only [htRow, if_pos q.1.isLt]
  rw [sCornerOf_self]

theorem htRow_block (x : BRow) (hx : x ∈ (markBlock v H hX hO).rows) :
    htRow v hL p x = v.oHeight2 p := by
  obtain ⟨i, rfl⟩ := (markBlock v H hX hO).mem_rows.mp hx
  rw [stdBlock_hr]
  simp only [htRow]
  rw [if_neg (by omega)]

variable {κ} in
/-- The rows of a marked word grid are ordered by height when the key refines the heights. -/
theorem markedGrid_rows_pairwise (hκ : ∀ a b, v.oHeight2 a < v.oHeight2 b → κ a < κ b) :
    (markedGrid v κ hL p H hX hO).rows.Pairwise
      (fun x y => htRow v hL p x ≤ htRow v hL p y) := by
  have hplain : (plainGrid v κ hL).rows.Pairwise
      (fun x y => htRow v hL p x ≤ htRow v hL p y) := by
    rw [plainGrid_rows, List.pairwise_map]
    refine (sRows_sorted v κ).imp fun {a b} h => ?_
    rw [sfCol_zero, sfCol_zero, htRow_word, htRow_word]
    by_contra hlt
    have := hκ b a (by omega)
    omega
  have hD := (markData v κ hL p H hX hO).rows_eq
  rw [hD, List.pairwise_append, List.pairwise_cons] at hplain
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hplain
  have hα : htRow v hL p (markRow v p) = v.oHeight2 p := htRow_word v hL p p
  have hB : ∀ b ∈ (markBlock v H hX hO).rows, htRow v hL p b = htRow v hL p (markRow v p) :=
    fun b hb => (htRow_block v hL p H hX hO b hb).trans hα.symm
  rw [markedGrid_rows, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨h1, ?_, fun x hx y hy => ?_⟩, h3, fun x hx y hy => ?_⟩
  · exact (List.pairwise_of_forall (R := fun _ _ => True) (fun _ _ => trivial)).imp_of_mem
      (fun ha hb _ => by rw [hB _ ha, hB _ hb])
  · rw [hB y hy]; exact h4 x hx _ List.mem_cons_self
  · rcases List.mem_append.mp hx with hx | hx
    · exact h4 x hx y (List.mem_cons_of_mem _ hy)
    · rw [hB x hx]; exact h2 y hy

end Marks

/-! ### Generic facts used for tie changes -/

section Generic

theorem rel_of_idxOf_lt {α : Type*} [DecidableEq α] {R : α → α → Prop} {l : List α}
    (h : l.Pairwise R) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hlt : l.idxOf x < l.idxOf y) :
    R x y := by
  have hx' := List.idxOf_lt_length_iff.mpr hx
  have hy' := List.idxOf_lt_length_iff.mpr hy
  have := List.pairwise_iff_getElem.mp h _ _ hx' hy' hlt
  rwa [List.getElem_idxOf, List.getElem_idxOf] at this

theorem rowsNonint_of_ends {n : ℕ} {C R : Type*} [DecidableEq C] (G : LabeledGrid n C R)
    {x z : R} {cx cx' cz cz' : C} (h1 : cx ∈ G.cols) (h2 : cx' ∈ G.cols) (h3 : cz ∈ G.cols)
    (h4 : cz' ∈ G.cols) (hOx : G.O cx = x) (hXx : G.X cx' = x) (hOz : G.O cz = z)
    (hXz : G.X cz' = z) (h : NonintN (G.cpos cx) (G.cpos cx') (G.cpos cz) (G.cpos cz')) :
    G.RowsNonint x z := by
  intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
  rw [G.O_inj a ha cx h1 (hOa.trans hOx.symm), G.X_inj a' ha' cx' h2 (hXa.trans hXx.symm),
    G.O_inj b hb cz h3 (hOb.trans hOz.symm), G.X_inj b' hb' cz' h4 (hXb.trans hXz.symm)]
  exact h

theorem nonintN_of_inside {lo hi a₀ a₁ b₀ b₁ : ℕ} (ha₀ : lo ≤ a₀ ∧ a₀ ≤ hi)
    (ha₁ : lo ≤ a₁ ∧ a₁ ≤ hi) (hb₀ : b₀ < lo ∨ hi < b₀) (hb₁ : b₁ < lo ∨ hi < b₁) :
    NonintN a₀ a₁ b₀ b₁ := by
  unfold NonintN CIooN
  constructor <;> constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

theorem idxOf_middle {α : Type*} [DecidableEq α] {m₁ B m₂ : List α} {x : α} (hx : x ∈ B)
    (hx1 : x ∉ m₁) : (m₁ ++ B ++ m₂).idxOf x = m₁.length + B.idxOf x := by
  rw [List.append_assoc, List.idxOf_append_of_notMem hx1, List.idxOf_append_of_mem hx]

end Generic

/-! ### Tie changes -/

section Ties

variable {m k : ℕ} (v : SignedAdjacentWord m) (hL : 0 < v.length)
  (p : Fin v.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
  (hO : H.O (Fin.last k) = 0)

theorem markBlock_hr_ne_word (i : Fin (k + 2)) (q : Fin v.length × Fin 3) :
    (markBlock v H hX hO).hr i ≠ Sum.inr (q.1.val, q.2) := by
  rw [stdBlock_hr]
  simp only [ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
  intro h; have := q.1.isLt; omega

theorem sM_ne_self (q : Fin v.length × Fin 3) : sM v q ≠ q := fun h =>
  oHeight2_ne_xHeight2 v q (by have := sM_height v q; rw [h] at this; exact this.symm)

theorem sM_ne_of_height {q q' : Fin v.length × Fin 3} (hh : v.oHeight2 q = v.oHeight2 q') :
    sM v q ≠ q' := fun h =>
  oHeight2_ne_xHeight2 v q' (by have := sM_height v q; rw [h, hh] at this; exact this.symm)

theorem plain_rows_perm (κ κ' : Fin v.length × Fin 3 → ℕ) :
    (plainGrid v κ' hL).rows.Perm (plainGrid v κ hL).rows := by
  rw [plainGrid_rows, plainGrid_rows]
  exact (((List.mergeSort_perm _ _).trans (List.mergeSort_perm _ _).symm)).map _

theorem markedGrid_rows_perm (κ κ' : Fin v.length × Fin 3 → ℕ) :
    (markedGrid v κ' hL p H hX hO).rows.Perm (markedGrid v κ hL p H hX hO).rows := by
  set D := markData v κ hL p H hX hO
  set D' := markData v κ' hL p H hX hO
  set B := (markBlock v H hX hO).rows
  have h0 := plain_rows_perm v hL κ κ'
  rw [D'.rows_eq, D.rows_eq] at h0
  have h1 : (D'.m₁ ++ D'.m₂).Perm (D.m₁ ++ D.m₂) :=
    ((List.perm_middle.symm.trans h0).trans List.perm_middle).cons_inv
  rw [markedGrid_rows, markedGrid_rows]
  have e : ∀ a b : List BRow, (a ++ B ++ b).Perm (B ++ (a ++ b)) := fun a b =>
    (List.perm_append_comm.append_right b).trans (List.Perm.of_eq (List.append_assoc B a b))
  exact (e _ _).trans (((h1.append_left B)).trans (e _ _).symm)

end Ties

section TieMain

variable {m k : ℕ} (v : SignedAdjacentWord m) (hL : 0 < v.length)
  (p : Fin v.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
  (hO : H.O (Fin.last k) = 0)

/-- The row of a word corner other than `p` does not interleave any other row of the same height
of a marked word grid. -/
theorem markedGrid_rowsNonint_word (κ : Fin v.length × Fin 3 → ℕ) (q : Fin v.length × Fin 3)
    (hq : q ≠ p) {y : BRow} (hy : y ∈ (markedGrid v κ hL p H hX hO).rows)
    (hyq : y ≠ Sum.inr (q.1.val, q.2)) (hh : htRow v hL p y = v.oHeight2 q) :
    (markedGrid v κ hL p H hX hO).RowsNonint (Sum.inr (q.1.val, q.2)) y := by
  set G := markedGrid v κ hL p H hX hO with hG
  set P := markBlock v H hX hO with hP
  have hsq : sM v q ≠ sM v p := (sM v).injective.ne hq
  have hXq : G.X (Sum.inr ((sM v q).1.val, (sM v q).2)) = Sum.inr (q.1.val, q.2) := by
    rw [markedGrid_X_word v κ hL p H hX hO _ hsq, Equiv.symm_apply_apply]
  have hcq := markedGrid_cpos_word v κ hL p H hX hO q
  have hcsq := markedGrid_cpos_word v κ hL p H hX hO (sM v q)
  have hqp : (finProdFinEquiv q).val ≠ (finProdFinEquiv p).val := fun h =>
    hq (finProdFinEquiv.injective (Fin.ext h))
  rcases markedGrid_mem_rows v κ hL p H hX hO hy with ⟨q', hq', rfl⟩ | hyB
  · -- another word row
    have hne : q ≠ q' := fun h => hyq (by rw [h])
    rw [htRow_word] at hh
    have hsq' : sM v q' ≠ sM v p := (sM v).injective.ne hq'
    have hXq' : G.X (Sum.inr ((sM v q').1.val, (sM v q').2)) = Sum.inr (q'.1.val, q'.2) := by
      rw [markedGrid_X_word v κ hL p H hX hO _ hsq', Equiv.symm_apply_apply]
    refine rowsNonint_of_ends G (markedGrid_word_mem v κ hL p H hX hO q)
      (markedGrid_word_mem v κ hL p H hX hO _) (markedGrid_word_mem v κ hL p H hX hO q')
      (markedGrid_word_mem v κ hL p H hX hO _) (markedGrid_O_word v κ hL p H hX hO q hq) hXq
      (markedGrid_O_word v κ hL p H hX hO q' hq') hXq' ?_
    rw [hcq, hcsq, markedGrid_cpos_word v κ hL p H hX hO q',
      markedGrid_cpos_word v κ hL p H hX hO (sM v q'),
      nonintN_map_strictMono (shiftAfter_strictMono _ _)]
    exact nonint_of_height_eq v hne hh.symm
  · obtain ⟨i, rfl⟩ := P.mem_rows.mp hyB
    have hhp : v.oHeight2 p = v.oHeight2 q := by
      rw [← hh, htRow_block v hL p H hX hO _ hyB]
    by_cases hi0 : i.val = 0
    · -- the input row: a short row
      have hi : i = 0 := Fin.ext hi0
      subst hi
      apply (G.rowsNonint_comm).mp
      have hXb : G.X (P.hc 0) = P.hr 0 := by
        rw [markedGrid_X_block, ProtBlock.xRow_zero]
      have hsp : p ≠ sM v p := fun h => sM_ne_self v p h.symm
      refine G.rowsNonint_of_short (markedGrid_word_mem v κ hL p H hX hO p)
        (markedGrid_block_mem v κ hL p H hX hO 0) (markedGrid_O_p v κ hL p H hX hO) hXb
        ?_ (markBlock_hr_ne_word v H hX hO 0 q).symm ?_ ?_
      · rw [markedGrid_cpos_block, markedGrid_cpos_word]
        left; simp [shiftAfter]
      · rw [markedGrid_O_block]
        unfold ProtBlock.oRow
        split_ifs
        · exact (markBlock_hr_ne_word v H hX hO _ q).symm
        · exact (markBlock_hr_ne_word v H hX hO _ q).symm
      · rw [markedGrid_X_word v κ hL p H hX hO p hsp]
        intro h
        have h' := inr_corner_inj v h
        exact sM_ne_of_height v hhp.symm (by rw [h', Equiv.apply_symm_apply])
    by_cases hil : i = Fin.last (k + 1)
    · -- the output row
      subst hil
      have hOl : G.O (P.hc (Fin.last k)) = P.hr (Fin.last (k + 1)) := by
        rw [markedGrid_O_block, ProtBlock.oRow_last]
      have hsp : (finProdFinEquiv (sM v p)).val ≠ (finProdFinEquiv p).val := fun h =>
        sM_ne_self v p (finProdFinEquiv.injective (Fin.ext h))
      have hsqp : (finProdFinEquiv (sM v q)).val ≠ (finProdFinEquiv p).val := fun h =>
        sM_ne_of_height v hhp.symm (finProdFinEquiv.injective (Fin.ext h))
      refine rowsNonint_of_ends G (markedGrid_word_mem v κ hL p H hX hO q)
        (markedGrid_word_mem v κ hL p H hX hO _) (markedGrid_block_mem v κ hL p H hX hO _)
        (markedGrid_word_mem v κ hL p H hX hO _) (markedGrid_O_word v κ hL p H hX hO q hq) hXq
        hOl
        (markedGrid_X_sMp v κ hL p H hX hO) ?_
      rw [hcq, hcsq, markedGrid_cpos_block, markedGrid_cpos_word,
        ← shiftFrom_eq_shiftAfter hqp, ← shiftFrom_eq_shiftAfter hsqp,
        ← shiftFrom_eq_shiftAfter hsp,
        show (finProdFinEquiv p).val + 1 + (Fin.last k).val =
          shiftFrom (finProdFinEquiv p) (k + 1) (finProdFinEquiv p) by
            simp [shiftFrom]; omega,
        nonintN_map_strictMono (shiftFrom_strictMono _ _)]
      exact nonint_of_height_eq v hq hhp.symm
    · -- an internal block row
      have hiw : ∀ q'' : Fin v.length × Fin 3, P.hr i ≠ Sum.inr (q''.1.val, q''.2) :=
        markBlock_hr_ne_word v H hX hO i
      obtain ⟨c, hc, hOc⟩ := G.exists_O_eq hy
      obtain ⟨c', hc', hXc'⟩ := G.exists_X_eq hy
      have hblock : ∀ d ∈ G.cols, (G.O d = P.hr i ∨ G.X d = P.hr i) →
          ∃ j : Fin (k + 1), d = P.hc j := by
        intro d hd hdi
        rcases markedGrid_mem_cols v κ hL p H hX hO hd with ⟨q'', rfl⟩ | hj
        · exfalso
          rcases hdi with h | h
          · by_cases hqp' : q'' = p
            · rw [hqp', markedGrid_O_p] at h
              exact hi0 (congrArg Fin.val (P.hr_inj h)).symm
            · rw [markedGrid_O_word v κ hL p H hX hO q'' hqp'] at h; exact hiw q'' h.symm
          · by_cases hs : q'' = sM v p
            · subst hs
              rw [markedGrid_X_sMp] at h
              exact hil (P.hr_inj h).symm
            · rw [markedGrid_X_word v κ hL p H hX hO _ hs] at h
              exact hiw _ h.symm
        · exact hj
      obtain ⟨j, rfl⟩ := hblock c hc (Or.inl hOc)
      obtain ⟨j', rfl⟩ := hblock c' hc' (Or.inr hXc')
      refine rowsNonint_of_ends G (markedGrid_word_mem v κ hL p H hX hO q)
        (markedGrid_word_mem v κ hL p H hX hO _) hc hc'
        (markedGrid_O_word v κ hL p H hX hO q hq) hXq hOc hXc' ?_
      rw [hcq, hcsq, markedGrid_cpos_block, markedGrid_cpos_block]
      apply nonintN_comm.mp
      have hj := j.isLt
      have hj' := j'.isLt
      refine nonintN_of_inside (lo := (finProdFinEquiv p).val + 1)
        (hi := (finProdFinEquiv p).val + 1 + k) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_ ?_
      · unfold shiftAfter; split_ifs <;> omega
      · unfold shiftAfter; split_ifs <;> omega

/-- **Tie changes of marked word grids.** Two marked word grids of the same word, marked arc and
protected grid, with keys refining the heights, are related by grid moves. -/
theorem markedGrid_movesTo_of_keys {κ κ' : Fin v.length × Fin 3 → ℕ}
    (hκ : ∀ a b, v.oHeight2 a < v.oHeight2 b → κ a < κ b)
    (hκ' : ∀ a b, v.oHeight2 a < v.oHeight2 b → κ' a < κ' b) :
    (markedGrid v κ hL p H hX hO).toGrid.MovesTo (markedGrid v κ' hL p H hX hO).toGrid := by
  set G := markedGrid v κ hL p H hX hO with hG
  set G' := markedGrid v κ' hL p H hX hO with hG'
  have hperm := markedGrid_rows_perm v hL p H hX hO κ κ'
  have heq : G'.toGrid = (G.withRows G'.rows hperm).toGrid :=
    LabeledGrid.toGrid_eq_of_data _ _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
  rw [heq]
  refine LabeledGrid.movesTo_withRows_of_inverted G G'.rows hperm ?_
  intro x hx y hy hxy hyx
  have hx' : x ∈ G'.rows := hperm.mem_iff.mpr hx
  have hy' : y ∈ G'.rows := hperm.mem_iff.mpr hy
  have h1 := rel_of_idxOf_lt (markedGrid_rows_pairwise v hL p H hX hO hκ) hx hy hxy
  have h2 := rel_of_idxOf_lt (markedGrid_rows_pairwise v hL p H hX hO hκ') hy' hx' hyx
  have hh : htRow v hL p x = htRow v hL p y := le_antisymm h1 h2
  have hne : x ≠ y := fun h => by rw [h] at hxy; exact lt_irrefl _ hxy
  rcases markedGrid_mem_rows v κ hL p H hX hO hx with ⟨q, hq, rfl⟩ | hxB
  · rw [htRow_word] at hh
    exact markedGrid_rowsNonint_word v hL p H hX hO κ q hq hy (Ne.symm hne) hh.symm
  · rcases markedGrid_mem_rows v κ hL p H hX hO hy with ⟨q, hq, rfl⟩ | hyB
    · rw [htRow_word] at hh
      exact (G.rowsNonint_comm).mp (markedGrid_rowsNonint_word v hL p H hX hO κ q hq hx hne hh)
    · exfalso
      have hdisj : ∀ (a b c : List BRow), (a ++ (markBlock v H hX hO).rows ++ c).Nodup →
          ∀ z ∈ (markBlock v H hX hO).rows, z ∉ a := by
        intro a b c hnd z hz hza
        have := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 z hza z hz
        exact this rfl
      have hGn := G.rows_nodup
      have hG'n := G'.rows_nodup
      rw [markedGrid_rows] at hGn hxy
      rw [markedGrid_rows] at hG'n hyx
      rw [idxOf_middle hxB (hdisj _ [] _ hGn x hxB), idxOf_middle hyB (hdisj _ [] _ hGn y hyB)]
        at hxy
      rw [idxOf_middle hxB (hdisj _ [] _ hG'n x hxB), idxOf_middle hyB (hdisj _ [] _ hG'n y hyB)]
        at hyx
      omega

end TieMain

end OnLeConjecture.KnotTheory.MarkedCancel
