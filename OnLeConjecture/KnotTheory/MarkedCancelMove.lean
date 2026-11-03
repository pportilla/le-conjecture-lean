/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelShared
public import OnLeConjecture.KnotTheory.MarkedCancelInsert

/-!
# The protected block passes every column of the base grid

This file proves the first framing fact of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 8, "The frame and its elementary exchanges"): after
the insertion of a protected block into a row `α` of a labeled grid `G` (`insertBlock`), the
block can be moved to any gap of the column order of `G` by grid moves
(`movesTo_insertBlock`).

A column `c` of `G` passes the block in one of three ways (`movesTo_insertBlock_pass`).

* If `c` has no marking in `α`, its row positions lie outside the rows of the block, while the
  markings of every block column lie inside them, so `c` commutes with every block column
  (`nonintN_of_outside`).
* If `X c = α`, then `c` carries the output row of the block, and `c` is exchanged with the last
  block column by the shared-endpoint rule (`movesTo_swapCols_shared_down`).
* If `O c = α`, then `c` carries the input row, and `c` is exchanged with the first block column
  by the shared-endpoint rule. When the `X` marking of `c` lies above the block, the rows are
  first rotated cyclically (`movesTo_withRows_rotate`).
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory LabeledGrid

/-- Two pairs of positions, the second inside an interval and the first outside it, do not
interleave. -/
theorem nonintN_of_outside {a₀ a₁ b₀ b₁ lo hi : ℕ} (ha₀ : a₀ < lo ∨ hi < a₀)
    (ha₁ : a₁ < lo ∨ hi < a₁) (hb₀ : lo ≤ b₀ ∧ b₀ ≤ hi) (hb₁ : lo ≤ b₁ ∧ b₁ ≤ hi) :
    NonintN a₀ a₁ b₀ b₁ := by
  unfold NonintN CIooN
  constructor <;> constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

/-! ### Cyclic rotation of the rows of a labeled grid -/

section Rotate

variable {n : ℕ} {C R : Type*} [DecidableEq R]

/-- **Cyclic permutation of rows.** Moving the first row to the end is a grid move. -/
theorem movesTo_rotateRows (G : LabeledGrid n C R) {x : R} {l : List R} (h : G.rows = x :: l) :
    G.toGrid.MovesTo
      (G.withRows (l ++ [x]) (by rw [h]; exact List.perm_append_singleton x l)).toGrid := by
  set G' := G.withRows (l ++ [x]) (by rw [h]; exact List.perm_append_singleton x l)
  have hl : l.length + 1 = n := by rw [← G.rows_length, h]; simp
  have hσ : ∀ i, G'.rowAt i = G.rowAt (finRotate n i) := by
    intro i
    rw [G'.rowAt_eq_of_rows (show G'.rows = l ++ [x] from rfl), G.rowAt_eq_of_rows h]
    by_cases hi : i.val + 1 < n
    · simp only [GridMoves.finRotate_val_of_lt i hi, List.getElem_cons_succ]
      rw [List.getElem_append_left (by omega)]
    · have hi' : i.val = l.length := by have := i.isLt; omega
      have h0 : (finRotate n i).val = 0 := by
        cases n with
        | zero => exact i.elim0
        | succ m =>
          have : i = Fin.last m := Fin.ext (by simp; omega)
          rw [this, finRotate_last]; rfl
      simp only [h0, List.getElem_cons_zero]
      rw [List.getElem_append_right (by omega)]
      simp [hi']
  have he : G'.toGrid = G.toGrid.relabelRows (finRotate n).symm :=
    G.toGrid_withRows _ _ _ hσ
  have hm := GridDiagram.cyclicRows_movesTo G'.toGrid
  have hb : G'.toGrid.relabelRows (finRotate n) = G.toGrid := by
    rw [he]
    ext i <;> simp
  rw [hb] at hm
  exact hm.symm

/-- **Cyclic rotation of rows.** If the rows of `G` are `l₁ ++ l₂`, the grid with the rows
`l₂ ++ l₁` is related to `G` by grid moves. -/
theorem movesTo_withRows_rotate (G : LabeledGrid n C R) {l₁ l₂ : List R}
    (h : G.rows = l₁ ++ l₂) :
    G.toGrid.MovesTo
      (G.withRows (l₂ ++ l₁) (by rw [h]; exact List.perm_append_comm)).toGrid := by
  induction l₁ generalizing G l₂ with
  | nil =>
    have he : (G.withRows (l₂ ++ []) (by rw [h]; exact List.perm_append_comm)).toGrid =
        G.toGrid := toGrid_eq_of_data _ _ rfl (by change l₂ ++ [] = G.rows; rw [h]; simp)
      (fun _ _ => rfl) (fun _ _ => rfl)
    rw [he]
  | cons x l₁ ih =>
    have h' : G.rows = x :: (l₁ ++ l₂) := by rw [h]; rfl
    have hm1 := movesTo_rotateRows G h'
    set G₁ := G.withRows ((l₁ ++ l₂) ++ [x])
      (by rw [h']; exact List.perm_append_singleton x _) with hG₁
    have hG₁r : G₁.rows = l₁ ++ (l₂ ++ [x]) := by simp [hG₁, withRows]
    have hm2 := ih G₁ hG₁r
    have he : (G₁.withRows ((l₂ ++ [x]) ++ l₁) (by rw [hG₁r]; exact
        List.perm_append_comm)).toGrid =
        (G.withRows (l₂ ++ x :: l₁) (by rw [h]; exact List.perm_append_comm)).toGrid :=
      toGrid_eq_of_data _ _ rfl (by simp [withRows]) (fun _ _ => rfl) (fun _ _ => rfl)
    rw [he] at hm2
    exact hm1.trans hm2

end Rotate

/-! ### Positions of the rows after an insertion -/

section Positions

variable {n m : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]
  {G : LabeledGrid n C R} {α : R} {P : ProtBlock m C R}

namespace InsertData

variable (D : InsertData G α P)

omit [DecidableEq C] [DecidableEq R] in
theorem m₁_eq (D' : InsertData G α P) : D.m₁ = D'.m₁ := by
  classical
  have h := D.rows_eq.symm.trans D'.rows_eq
  have h1 : (D.m₁ ++ α :: D.m₂).idxOf α = D.m₁.length := by
    rw [List.idxOf_append_of_notMem D.not_mem_m₁]; simp
  have h2 : (D'.m₁ ++ α :: D'.m₂).idxOf α = D'.m₁.length := by
    rw [List.idxOf_append_of_notMem D'.not_mem_m₁]; simp
  rw [h] at h1
  exact (List.append_inj h (h1.symm.trans h2)).1

omit [DecidableEq C] [DecidableEq R] in
theorem m₂_eq (D' : InsertData G α P) : D.m₂ = D'.m₂ := by
  have h := D.rows_eq.symm.trans D'.rows_eq
  rw [D.m₁_eq D'] at h
  have := List.append_cancel_left h
  simpa using this

omit [DecidableEq C] [DecidableEq R] in
theorem mem_m_of_mem {x : R} (hx : x ∈ G.rows) (hxα : x ≠ α) : x ∈ D.m₁ ∨ x ∈ D.m₂ := by
  rw [D.rows_eq] at hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with h | h | h
  · exact Or.inl h
  · exact absurd h hxα
  · exact Or.inr h

end InsertData

theorem insertBlock_rows (D : InsertData G α P) :
    (insertBlock G α P D).rows = D.m₁ ++ P.rows ++ D.m₂ := rfl

theorem insertBlock_cols (D : InsertData G α P) :
    (insertBlock G α P D).cols = D.l₁ ++ P.cols ++ D.l₂ := rfl

theorem insertBlock_O (D : InsertData G α P) : (insertBlock G α P D).O = blockO G α P := rfl

theorem insertBlock_X (D : InsertData G α P) : (insertBlock G α P D).X = blockX G α P := rfl

theorem ofFn_split {k : ℕ} {β : Type*} (f : Fin (k + 1) → β) (i : Fin (k + 1)) :
    List.ofFn f = (List.ofFn f).take i.val ++ f i :: (List.ofFn f).drop (i.val + 1) := by
  conv_lhs => rw [← List.take_append_drop i.val (List.ofFn f)]
  congr 1
  rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]

theorem rpos_hr (D : InsertData G α P) (i : Fin (m + 2)) :
    (insertBlock G α P D).rpos (P.hr i) = D.m₁.length + i.val := by
  have hsplit := ofFn_split P.hr i
  rw [(insertBlock G α P D).rpos_of_rows_eq (m₁ := D.m₁ ++ (List.ofFn P.hr).take i.val)
    (m₂ := (List.ofFn P.hr).drop (i.val + 1) ++ D.m₂)]
  · simp only [List.length_append, List.length_take, List.length_ofFn]
    omega
  · rw [insertBlock_rows]
    change D.m₁ ++ List.ofFn P.hr ++ D.m₂ = _
    conv_lhs => rw [hsplit]
    simp only [List.append_assoc, List.cons_append]

theorem rpos_lt_of_mem_m₁ (D : InsertData G α P) {x : R} (hx : x ∈ D.m₁) :
    (insertBlock G α P D).rpos x < D.m₁.length := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem hx
  rw [(insertBlock G α P D).rpos_of_rows_eq (m₁ := a) (m₂ := b ++ P.rows ++ D.m₂)]
  · rw [hab]; simp
  · rw [insertBlock_rows, hab]; simp

theorem le_rpos_of_mem_m₂ (D : InsertData G α P) {x : R} (hx : x ∈ D.m₂) :
    D.m₁.length + (m + 2) ≤ (insertBlock G α P D).rpos x := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem hx
  rw [(insertBlock G α P D).rpos_of_rows_eq (m₁ := D.m₁ ++ P.rows ++ a) (m₂ := b)]
  · simp [P.rows_length]
  · rw [insertBlock_rows, hab]; simp

/-- An old row other than `α` lies outside the block rows. -/
theorem rpos_outside (D : InsertData G α P) {x : R} (hx : x ∈ G.rows) (hxα : x ≠ α) :
    (insertBlock G α P D).rpos x < D.m₁.length ∨
      D.m₁.length + (m + 1) < (insertBlock G α P D).rpos x := by
  rcases D.mem_m_of_mem hx hxα with h | h
  · exact Or.inl (rpos_lt_of_mem_m₁ D h)
  · have := le_rpos_of_mem_m₂ D h; right; omega

theorem rpos_oRow (D : InsertData G α P) (j : Fin (m + 1)) :
    D.m₁.length + 1 ≤ (insertBlock G α P D).rpos (P.oRow j) ∧
      (insertBlock G α P D).rpos (P.oRow j) ≤ D.m₁.length + (m + 1) ∧
      (j ≠ Fin.last m → (insertBlock G α P D).rpos (P.oRow j) ≤ D.m₁.length + m) := by
  unfold ProtBlock.oRow
  split_ifs with h
  · rw [rpos_hr]
    refine ⟨by simp, by simp, fun hj => ?_⟩
    exact absurd (P.H.O.toPerm.injective (h.trans P.O_last.symm)) hj
  · rw [rpos_hr]
    have h1 := (P.H.O j).isLt
    have h2 : (P.H.O j).val ≠ 0 := fun e => h (Fin.ext e)
    simp only [Fin.val_castSucc]
    omega

theorem rpos_xRow (D : InsertData G α P) (j : Fin (m + 1)) :
    D.m₁.length ≤ (insertBlock G α P D).rpos (P.xRow j) ∧
      (insertBlock G α P D).rpos (P.xRow j) ≤ D.m₁.length + m ∧
      (j ≠ 0 → D.m₁.length + 1 ≤ (insertBlock G α P D).rpos (P.xRow j)) := by
  unfold ProtBlock.xRow
  rw [rpos_hr]
  have h1 := (P.H.X j).isLt
  simp only [Fin.val_castSucc]
  refine ⟨by omega, by omega, fun hj => ?_⟩
  have : (P.H.X j).val ≠ 0 := fun e =>
    hj (P.H.X.toPerm.injective ((Fin.ext e : P.H.X j = 0).trans P.X_zero.symm))
  omega

end Positions

/-! ### One column passes the block -/

section Pass

variable {n m : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]
  {G : LabeledGrid n C R} {α : R} {P : ProtBlock m C R}

theorem ofFn_succ_last {β : Type*} (f : Fin (m + 1) → β) :
    List.ofFn f = List.ofFn (fun j : Fin m => f j.castSucc) ++ [f (Fin.last m)] := by
  rw [List.ofFn_succ', List.concat_eq_append]

/-- **A column passes the block.** If the block follows the column `c`, the grid with the block
before `c` is related by grid moves. -/
theorem movesTo_insertBlock_pass (D D' : InsertData G α P) {L : List C} {c : C}
    (h₁ : D.l₁ = L ++ [c]) (h₁' : D'.l₁ = L) (h₂' : D'.l₂ = c :: D.l₂) :
    (insertBlock G α P D).toGrid.MovesTo (insertBlock G α P D').toGrid := by
  set M := insertBlock G α P D with hM
  set M' := insertBlock G α P D' with hM'
  have hcG : c ∈ G.cols := by rw [D.cols_eq, h₁]; simp
  have hMc : M.cols = L ++ c :: (P.cols ++ D.l₂) := by
    rw [hM, insertBlock_cols, h₁]; simp
  have hM'c : M'.cols = L ++ P.cols ++ c :: D.l₂ := by
    rw [hM', insertBlock_cols, h₁', h₂']
  have hrows : M'.rows = M.rows := by
    rw [hM, hM', insertBlock_rows, insertBlock_rows, D'.m₁_eq D, D'.m₂_eq D]
  have htarget : ∀ G' : LabeledGrid (n + m + 1) C R, G'.cols = M'.cols → G'.rows = M.rows →
      G'.O = M.O → G'.X = M.X → G'.toGrid = M'.toGrid := fun G' h1 h2 h3 h4 =>
    toGrid_eq_of_data _ _ h1 (h2.trans hrows.symm) (fun c _ => by rw [h3]; rfl)
      (fun c _ => by rw [h4]; rfl)
  set lo := D.m₁.length with hlo
  have hOc_ne : ∀ (hO : G.O c ≠ α), M.O c = G.O c := fun hO => by
    rw [hM, insertBlock_O, D.blockO_old hcG, if_neg hO]
  have hXc_ne : ∀ (hX : G.X c ≠ α), M.X c = G.X c := fun hX => by
    rw [hM, insertBlock_X, D.blockX_old hcG, if_neg hX]
  have hOB : ∀ j, M.O (P.hc j) = P.oRow j := fun j => by rw [hM, insertBlock_O, blockO_hc]
  have hXB : ∀ j, M.X (P.hc j) = P.xRow j := fun j => by rw [hM, insertBlock_X, blockX_hc]
  have hblock_ne : ∀ (i : Fin (m + 2)) {x : R}, x ∈ G.rows → x ≠ α → P.hr i ≠ x :=
    fun i x hx hxα => D.hr_not_mem_of_ne hx hxα
  by_cases hO : G.O c = α
  · -- `c` carries the input row
    have hX : G.X c ≠ α := fun h => G.O_ne_X c hcG (hO.trans h.symm)
    have hMOc : M.O c = P.hr 0 := by rw [hM, insertBlock_O, D.blockO_old hcG, if_pos hO]
    have hPc : P.cols = P.hc 0 :: List.ofFn (fun j : Fin m => P.hc j.succ) := by
      change List.ofFn P.hc = _; exact List.ofFn_succ
    have hPr : P.rows = P.hr 0 :: List.ofFn (fun j : Fin (m + 1) => P.hr j.succ) := by
      change List.ofFn P.hr = _; exact List.ofFn_succ
    set Pt := List.ofFn (fun j : Fin m => P.hc j.succ) with hPt
    have hmidB : ∀ x, x ∈ G.rows → x ≠ α → x ≠ M.O (P.hc 0) := fun x hx hxα he => by
      rw [hOB] at he
      unfold ProtBlock.oRow at he
      split_ifs at he <;> exact hblock_ne _ hx hxα he.symm
    have hOb : M.O (P.hc 0) ≠ M.X c := by
      rw [hXc_ne hX]
      exact Ne.symm (hmidB _ (G.X_mem c hcG) hX)
    -- the shared-endpoint exchange of `c` and the first block column
    obtain ⟨M₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ : ∃ M₁ : LabeledGrid (n + m + 1) C R,
        M₁.cols = L ++ P.hc 0 :: c :: (Pt ++ D.l₂) ∧ M₁.rows = M.rows ∧ M₁.O = M.O ∧
          M₁.X = M.X ∧ M.toGrid.MovesTo M₁.toGrid := by
      have hcols : M.cols = L ++ c :: P.hc 0 :: (Pt ++ D.l₂) := by rw [hMc, hPc]; simp
      rcases D.mem_m_of_mem (G.X_mem c hcG) hX with hp | hp
      · obtain ⟨a, b, hab⟩ := List.append_of_mem hp
        have hrows' : M.rows = a ++ M.X c :: (b ++ P.hr 0 ::
            (List.ofFn (fun j : Fin (m + 1) => P.hr j.succ) ++ D.m₂)) := by
          rw [hM, insertBlock_rows, hab, hPr, hXc_ne hX]; simp
        have hm := movesTo_swapCols_shared_down M hcols hrows' hMOc rfl
          (by rw [hXB, ProtBlock.xRow_zero]) hOb (fun x hx => hmidB x
            (by rw [D.rows_eq, hab]; simp [hx])
            (fun e => D.not_mem_m₁ (by rw [hab, ← e]; simp [hx])))
        exact ⟨M.withCols (L ++ P.hc 0 :: c :: (Pt ++ D.l₂))
          (hcols ▸ perm_swap_middle L (Pt ++ D.l₂) c (P.hc 0)), rfl, rfl, rfl, rfl, hm⟩
      · obtain ⟨a, b, hab⟩ := List.append_of_mem hp
        have hrot : M.rows = (D.m₁ ++ P.rows) ++ D.m₂ := by rw [hM, insertBlock_rows]
        have hm1 := movesTo_withRows_rotate M hrot
        set Mr := M.withRows (D.m₂ ++ (D.m₁ ++ P.rows))
          (by rw [hrot]; exact List.perm_append_comm) with hMr
        have hrows' : Mr.rows = a ++ Mr.X c :: ((b ++ D.m₁) ++ P.hr 0 ::
            List.ofFn (fun j : Fin (m + 1) => P.hr j.succ)) := by
          change D.m₂ ++ (D.m₁ ++ P.rows) = _
          rw [hab, hPr]
          change _ = a ++ M.X c :: _
          rw [hXc_ne hX]; simp
        have hm2 := movesTo_swapCols_shared_down Mr (l₁ := L) (l₂ := Pt ++ D.l₂) hcols hrows'
          hMOc rfl (by change M.X (P.hc 0) = _; rw [hXB, ProtBlock.xRow_zero]) hOb
          (fun x hx => by
            change x ≠ M.O (P.hc 0)
            simp only [List.mem_append] at hx
            rcases hx with hx | hx
            · exact hmidB x (by rw [D.rows_eq, hab]; simp [hx])
                (fun e => D.not_mem_m₂ (by rw [hab, ← e]; simp [hx]))
            · exact hmidB x (by rw [D.rows_eq]; simp [hx])
                (fun e => D.not_mem_m₁ (e ▸ hx)))
        set Mr₁ := Mr.withCols (L ++ P.hc 0 :: c :: (Pt ++ D.l₂))
          (hcols ▸ perm_swap_middle L (Pt ++ D.l₂) c (P.hc 0)) with hMr₁
        have hrot' : Mr₁.rows = D.m₂ ++ (D.m₁ ++ P.rows) := rfl
        have hm3 := movesTo_withRows_rotate Mr₁ hrot'
        exact ⟨Mr₁.withRows (D.m₁ ++ P.rows ++ D.m₂)
          (by change (D.m₁ ++ P.rows ++ D.m₂).Perm (D.m₂ ++ (D.m₁ ++ P.rows))
              exact List.perm_append_comm), rfl, rfl, rfl, rfl, hm1.trans (hm2.trans hm3)⟩
    -- `c` passes the remaining block columns
    have hrp₁ : ∀ x, M₁.rpos x = M.rpos x := fun x => by simp only [LabeledGrid.rpos, hr₁]
    obtain ⟨G₂, hc₂, hr₂, hO₂, hX₂, hm₂⟩ := M₁.exists_moveColRight (l₁ := L ++ [P.hc 0])
      (mid := Pt) (l₂ := D.l₂) (c := c) (by rw [hc₁]; simp) (fun d hd => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
        unfold ColsNonint
        rw [hO₁, hX₁, hMOc, hXB, hOB, hXc_ne hX, hrp₁, hrp₁, hrp₁, hrp₁, rpos_hr]
        have h1 := rpos_oRow D j.succ
        have h2 := rpos_xRow D j.succ
        have h3 := rpos_outside D (G.X_mem c hcG) hX
        rw [← hM] at h1 h2 h3
        have h0 : ((0 : Fin (m + 2)) : ℕ) = 0 := rfl
        exact nonintN_of_outside (lo := lo + 1) (hi := lo + (m + 1)) (by omega)
          (by omega) ⟨h1.1, h1.2.1⟩ ⟨h2.2.2 (Fin.succ_ne_zero j), by omega⟩)
    have he := htarget G₂ (by rw [hc₂, hM'c, hPc]; simp) (hr₂.trans hr₁) (hO₂.trans hO₁)
      (hX₂.trans hX₁)
    rw [he] at hm₂
    exact hm₁.trans hm₂
  · by_cases hX : G.X c = α
    · -- `c` carries the output row
      have hMXc : M.X c = P.hr (Fin.last (m + 1)) := by
        rw [hM, insertBlock_X, D.blockX_old hcG, if_pos hX]
      have hPc := ofFn_succ_last P.hc
      set Pi := List.ofFn (fun j : Fin m => P.hc j.castSucc) with hPi
      obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := M.exists_moveColRight (l₁ := L) (mid := Pi)
        (l₂ := P.hc (Fin.last m) :: D.l₂) (c := c)
        (by rw [hMc]; change L ++ c :: (List.ofFn P.hc ++ D.l₂) = _; rw [hPc]; simp)
        (fun d hd => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
          unfold ColsNonint
          rw [hOc_ne hO, hMXc, hOB, hXB, rpos_hr]
          have h1 := rpos_oRow D j.castSucc
          have h2 := rpos_xRow D j.castSucc
          have h3 := rpos_outside D (G.O_mem c hcG) hO
          rw [← hM] at h1 h2 h3
          have hl : (Fin.last (m + 1) : ℕ) = m + 1 := Fin.val_last _
          exact nonintN_of_outside (lo := lo) (hi := lo + m) (by omega) (by omega)
            ⟨by omega, h1.2.2 (Fin.castSucc_ne_last j)⟩ ⟨h2.1, h2.2.1⟩)
      -- the shared-endpoint exchange of the last block column and `c`, read in `M'`
      have hcolsM' : M'.cols = (L ++ Pi) ++ P.hc (Fin.last m) :: c :: D.l₂ := by
        rw [hM'c]; change L ++ List.ofFn P.hc ++ c :: D.l₂ = _; rw [hPc]; simp
      set i₀ := (P.H.X (Fin.last m)).castSucc with hi₀
      have hsplit := ofFn_split P.hr i₀
      have hdrop : (List.ofFn P.hr).drop (i₀.val + 1) =
          ((List.ofFn P.hr).drop (i₀.val + 1)).dropLast ++ [P.hr (Fin.last (m + 1))] := by
        have hne : (List.ofFn P.hr).drop (i₀.val + 1) ≠ [] := by
          rw [Ne, List.drop_eq_nil_iff]; simp only [List.length_ofFn, hi₀, Fin.val_castSucc]
          have := (P.H.X (Fin.last m)).isLt; omega
        have hlast : ((List.ofFn P.hr).drop (i₀.val + 1)).getLast hne =
            P.hr (Fin.last (m + 1)) := by
          rw [List.getLast_eq_getElem, List.getElem_drop, List.getElem_ofFn]
          congr 1
          apply Fin.ext
          have := (P.H.X (Fin.last m)).isLt
          simp only [List.length_drop, List.length_ofFn, Fin.val_last, hi₀, Fin.val_castSucc]
          omega
        conv_lhs => rw [← List.dropLast_append_getLast hne, hlast]
      have hrowsM' : M'.rows = (D.m₁ ++ (List.ofFn P.hr).take i₀.val) ++ P.xRow (Fin.last m) ::
          (((List.ofFn P.hr).drop (i₀.val + 1)).dropLast ++ P.hr (Fin.last (m + 1)) :: D.m₂) := by
        rw [hrows, hM, insertBlock_rows]
        change D.m₁ ++ List.ofFn P.hr ++ D.m₂ = _
        conv_lhs => rw [hsplit, hdrop]
        simp only [List.append_assoc, List.cons_append, ProtBlock.xRow,
          hi₀, List.nil_append]
      have hO'c : M'.O c = G.O c := by rw [hM', insertBlock_O, D'.blockO_old hcG, if_neg hO]
      have hm := movesTo_swapCols_shared_down M' hcolsM' hrowsM'
        (by rw [hM', insertBlock_O, blockO_hc, ProtBlock.oRow_last])
        (by rw [hM', insertBlock_X, blockX_hc])
        (by rw [hM', insertBlock_X, D'.blockX_old hcG, if_pos hX])
        (by
          rw [hO'c]
          exact fun he => hblock_ne _ (G.O_mem c hcG) hO he.symm)
        (fun x hx => by
          rw [hO'c]
          obtain ⟨k, hk⟩ : ∃ k, P.hr k = x := by
            have : x ∈ List.ofFn P.hr := List.mem_of_mem_drop (List.mem_of_mem_dropLast hx)
            obtain ⟨k, hk⟩ := List.mem_ofFn.mp this
            exact ⟨k, hk⟩
          rw [← hk]
          exact hblock_ne k (G.O_mem c hcG) hO)
      have he : (M'.withCols ((L ++ Pi) ++ c :: P.hc (Fin.last m) :: D.l₂)
          (hcolsM' ▸ perm_swap_middle (L ++ Pi) D.l₂ (P.hc (Fin.last m)) c)).toGrid =
          G₁.toGrid :=
        toGrid_eq_of_data _ _ (by rw [hc₁]; simp [withCols]) (by
          change M'.rows = G₁.rows; rw [hr₁, hrows])
          (fun d _ => by change M'.O d = G₁.O d; rw [hO₁]; rfl)
          (fun d _ => by change M'.X d = G₁.X d; rw [hX₁]; rfl)
      rw [he] at hm
      exact hm₁.trans hm.symm
    · -- `c` has no marking in `α`
      obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := M.exists_moveColRight hMc (fun d hd => by
        obtain ⟨j, rfl⟩ := P.mem_cols.mp hd
        unfold ColsNonint
        rw [hOc_ne hO, hXc_ne hX, hOB, hXB]
        have h1 := rpos_oRow D j
        have h2 := rpos_xRow D j
        have h3 := rpos_outside D (G.O_mem c hcG) hO
        have h4 := rpos_outside D (G.X_mem c hcG) hX
        rw [← hM] at h1 h2 h3 h4
        exact nonintN_of_outside (lo := lo) (hi := lo + (m + 1)) h3 h4
          ⟨by omega, h1.2.1⟩ ⟨h2.1, by omega⟩)
      have he := htarget G₁ (by rw [hc₁, hM'c]) hr₁ hO₁ hX₁
      rw [he] at hm₁
      exact hm₁

end Pass

/-! ### The block at any gap -/

section AnyGap

variable {n m : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]
  {G : LabeledGrid n C R} {α : R} {P : ProtBlock m C R}

/-- The insertion data with the block after the first `j` columns. -/
def InsertData.atPos (D : InsertData G α P) (j : ℕ) : InsertData G α P where
  l₁ := G.cols.take j
  l₂ := G.cols.drop j
  m₁ := D.m₁
  m₂ := D.m₂
  cols_eq := (List.take_append_drop j G.cols).symm
  rows_eq := D.rows_eq
  cols_fresh := D.cols_fresh
  rows_fresh := D.rows_fresh

theorem toGrid_insertBlock_atPos (D : InsertData G α P) :
    (insertBlock G α P D).toGrid = (insertBlock G α P (D.atPos D.l₁.length)).toGrid := by
  apply toGrid_eq_of_data
  · change D.l₁ ++ P.cols ++ D.l₂ = G.cols.take D.l₁.length ++ P.cols ++ G.cols.drop D.l₁.length
    rw [D.cols_eq, List.take_left', List.drop_left'] <;> rfl
  · rfl
  · intro _ _; rfl
  · intro _ _; rfl

theorem movesTo_insertBlock_atPos_succ (D : InsertData G α P) {j : ℕ} (hj : j < G.cols.length) :
    (insertBlock G α P (D.atPos (j + 1))).toGrid.MovesTo
      (insertBlock G α P (D.atPos j)).toGrid :=
  movesTo_insertBlock_pass (D.atPos (j + 1)) (D.atPos j) (L := G.cols.take j)
    (c := G.cols[j]) (List.take_succ_eq_append_getElem hj) rfl
    (List.drop_eq_getElem_cons hj)

theorem movesTo_insertBlock_atPos (D : InsertData G α P) {i j : ℕ} (hi : i ≤ G.cols.length)
    (hj : j ≤ G.cols.length) :
    (insertBlock G α P (D.atPos i)).toGrid.MovesTo (insertBlock G α P (D.atPos j)).toGrid := by
  have key : ∀ d i, i + d ≤ G.cols.length →
      (insertBlock G α P (D.atPos (i + d))).toGrid.MovesTo
        (insertBlock G α P (D.atPos i)).toGrid := by
    intro d
    induction d with
    | zero => intro i _; exact GridDiagram.MovesTo.refl _
    | succ d ih =>
      intro i hid
      exact (movesTo_insertBlock_atPos_succ D (j := i + d) (by omega)).trans (ih i (by omega))
  rcases Nat.le_total i j with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (key d i hj).symm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact key d j hi

/-- **The first framing fact.** Two insertions of the same protected block into the same row,
with the block at two gaps of the column order, are related by grid moves. -/
theorem movesTo_insertBlock (D D' : InsertData G α P) :
    (insertBlock G α P D).toGrid.MovesTo (insertBlock G α P D').toGrid := by
  rw [toGrid_insertBlock_atPos D, toGrid_insertBlock_atPos D']
  have h1 : D.l₁.length ≤ G.cols.length := by rw [D.cols_eq]; simp
  have h2 : D'.l₁.length ≤ G.cols.length := by rw [D'.cols_eq]; simp
  have he : D'.atPos D'.l₁.length = D.atPos D'.l₁.length := by
    unfold InsertData.atPos
    congr 1
    · exact D'.m₁_eq D
    · exact D'.m₂_eq D
  rw [he]
  exact movesTo_insertBlock_atPos D h1 h2

end AnyGap

end OnLeConjecture.KnotTheory.MarkedCancel
