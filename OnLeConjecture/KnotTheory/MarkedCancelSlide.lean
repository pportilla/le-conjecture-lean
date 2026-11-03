/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelMove
public import OnLeConjecture.KnotTheory.MarkedCancelImage

/-!
# Sliding the protected block to the next arc

Let a column `z` of a labeled grid `G` end the arc `α` (`X z = α`) and start the arc `β`
(`O z = β`). The insertion of a protected block with new row labels into `α` and its insertion
into `β` are related by grid moves (`movesTo_insertBlock_slide`). This is the passage of the
protected block through a corner of its strand in the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 8, "The frame and its elementary exchanges").

After a cyclic rotation of the rows that makes `α` the first row (`movesTo_insertBlock_rotate`),
both insertions destabilize to a common grid: in the first, the column `z` is absorbed into the
last block column (an `O` merge); in the second, `z` is absorbed into the first block column (an
`X` merge). In between, the internal rows of the block pass every row of `G` lying between `α`
and `β`, since such a row has no marking in a block column (`exists_moveRowsPast`, the second
framing fact).
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory LabeledGrid

/-! ### Column positions around a contiguous block -/

section Positions

variable {n : ℕ} {C R : Type*} [DecidableEq C] (G : LabeledGrid n C R)

theorem cpos_lt_of_mem_left {L B Rr : List C} (h : G.cols = L ++ B ++ Rr) {x : C} (hx : x ∈ L) :
    G.cpos x < L.length := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hx
  rw [G.cpos_of_cols_eq (l₁ := a) (l₂ := b ++ B ++ Rr) (by rw [h]; simp)]
  simp

theorem cpos_mem_mid {L B Rr : List C} (h : G.cols = L ++ B ++ Rr) {x : C} (hx : x ∈ B) :
    L.length ≤ G.cpos x ∧ G.cpos x < L.length + B.length := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hx
  rw [G.cpos_of_cols_eq (l₁ := L ++ a) (l₂ := b ++ Rr) (by rw [h]; simp)]
  simp

theorem le_cpos_of_mem_right {L B Rr : List C} (h : G.cols = L ++ B ++ Rr) {x : C}
    (hx : x ∈ Rr) : L.length + B.length ≤ G.cpos x := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hx
  rw [G.cpos_of_cols_eq (l₁ := L ++ B ++ a) (l₂ := b) (by rw [h]; simp)]
  simp

/-- A row whose markings lie in the columns of a contiguous block does not interleave a row whose
markings lie outside them. -/
theorem rowsNonint_of_block {L B Rr : List C} (h : G.cols = L ++ B ++ Rr) {x y : R}
    (hx : ∀ c ∈ G.cols, (G.O c = x ∨ G.X c = x) → c ∈ B)
    (hy : ∀ c ∈ G.cols, (G.O c = y ∨ G.X c = y) → c ∉ B) : G.RowsNonint x y := by
  intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
  have hmemB : ∀ c ∈ G.cols, c ∉ B → c ∈ L ∨ c ∈ Rr := by
    intro c hc hcB
    rw [h] at hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact Or.inl hc
    · exact absurd hc hcB
    · exact Or.inr hc
  have ha1 := cpos_mem_mid G h (hx a ha (Or.inl hOa))
  have ha2 := cpos_mem_mid G h (hx a' ha' (Or.inr hXa))
  have hout : ∀ c ∈ G.cols, c ∉ B → G.cpos c < L.length ∨ L.length + B.length - 1 < G.cpos c := by
    intro c hc hcB
    rcases hmemB c hc hcB with h' | h'
    · exact Or.inl (cpos_lt_of_mem_left G h h')
    · have := le_cpos_of_mem_right G h h'; right; omega
  apply nonintN_comm.mpr
  exact nonintN_of_outside (lo := L.length) (hi := L.length + B.length - 1)
    (hout b hb (hy b hb (Or.inl hOb))) (hout b' hb' (hy b' hb' (Or.inr hXb)))
    ⟨ha1.1, by omega⟩ ⟨ha2.1, by omega⟩

end Positions

/-! ### The second framing fact -/

section RowsPast

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

/-- **A list of rows passes a list of rows.** -/
theorem exists_moveRowsPast (G : LabeledGrid n C R) {m₁ Bl Cl m₂ : List R}
    (h : G.rows = m₁ ++ Bl ++ Cl ++ m₂) (hni : ∀ b ∈ Bl, ∀ c ∈ Cl, G.RowsNonint b c) :
    ∃ G' : LabeledGrid n C R, G'.cols = G.cols ∧ G'.rows = m₁ ++ Cl ++ Bl ++ m₂ ∧
      G'.O = G.O ∧ G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  induction Cl generalizing G m₁ with
  | nil => exact ⟨G, rfl, by simpa using h, rfl, rfl, GridDiagram.MovesTo.refl _⟩
  | cons c Cl ih =>
    have h' : G.rows = m₁ ++ Bl ++ c :: (Cl ++ m₂) := by rw [h]; simp
    obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveRowDown h'
      (fun b hb => hni b hb c (by simp))
    have hni₁ : ∀ b ∈ Bl, ∀ c' ∈ Cl, G₁.RowsNonint b c' := by
      intro b hb c' hc' a a' d d' ha ha' hd hd' e1 e2 e3 e4
      have hcp : ∀ x, G₁.cpos x = G.cpos x := fun x => by simp only [LabeledGrid.cpos, hc₁]
      rw [hcp, hcp, hcp, hcp]
      rw [hc₁] at ha ha' hd hd'
      rw [hO₁] at e1 e3
      rw [hX₁] at e2 e4
      exact hni b hb c' (by simp [hc']) a a' d d' ha ha' hd hd' e1 e2 e3 e4
    obtain ⟨G₂, hc₂, hr₂, hO₂, hX₂, hm₂⟩ := ih G₁ (m₁ := m₁ ++ [c])
      (by rw [hr₁]; simp) hni₁
    exact ⟨G₂, hc₂.trans hc₁, by rw [hr₂]; simp, hO₂.trans hO₁, hX₂.trans hX₁, hm₁.trans hm₂⟩

end RowsPast

/-! ### Rotation of the base rows -/

section RotateBase

variable {n m : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]
  {G : LabeledGrid n C R} {P : ProtBlock m C R}

omit [DecidableEq C] [DecidableEq R] in
theorem InsertData.m_of_split {γ : R} (D : InsertData G γ P) {a b : List R}
    (h : G.rows = a ++ γ :: b) : D.m₁ = a ∧ D.m₂ = b := by
  let D₂ : InsertData G γ P := { D with m₁ := a, m₂ := b, rows_eq := h }
  exact ⟨D.m₁_eq D₂, D.m₂_eq D₂⟩

/-- **Insertion into a rotated grid.** Rotating the rows of the base grid cyclically rotates the
rows of the inserted grid. -/
theorem movesTo_insertBlock_rotate {γ : R} (D : InsertData G γ P) {l₁ l₂ : List R}
    (h : G.rows = l₁ ++ l₂)
    (D' : InsertData (G.withRows (l₂ ++ l₁) (by rw [h]; exact List.perm_append_comm)) γ P) :
    (insertBlock G γ P D).toGrid.MovesTo (insertBlock _ γ P D').toGrid := by
  let D'' : InsertData (G.withRows (l₂ ++ l₁) (by rw [h]; exact List.perm_append_comm)) γ P :=
    { D' with l₁ := D.l₁, l₂ := D.l₂, cols_eq := D.cols_eq, cols_fresh := D.cols_fresh }
  suffices hs : (insertBlock G γ P D).toGrid.MovesTo (insertBlock _ γ P D'').toGrid from
    hs.trans (movesTo_insertBlock D'' D')
  have hγ : γ ∈ l₁ ++ l₂ := by rw [← h]; exact D.alpha_mem
  set M := insertBlock G γ P D with hM
  rcases List.mem_append.mp hγ with hγ | hγ
  · obtain ⟨a, b, rfl⟩ := List.append_of_mem hγ
    obtain ⟨e1, e2⟩ := D.m_of_split (a := a) (b := b ++ l₂) (by rw [h]; simp)
    obtain ⟨e1', e2'⟩ := D''.m_of_split (a := l₂ ++ a) (b := b) (by simp [withRows])
    have hMr : M.rows = (a ++ P.rows ++ b) ++ l₂ := by
      rw [hM, insertBlock_rows, e1, e2]; simp
    have hm := movesTo_withRows_rotate M hMr
    have he : (M.withRows (l₂ ++ (a ++ P.rows ++ b))
        (by rw [hMr]; exact List.perm_append_comm)).toGrid = (insertBlock _ γ P D'').toGrid :=
      toGrid_eq_of_data _ _ rfl
        (by change l₂ ++ (a ++ P.rows ++ b) = D''.m₁ ++ P.rows ++ D''.m₂
            rw [e1', e2']; simp)
        (fun _ _ => rfl) (fun _ _ => rfl)
    rw [he] at hm
    exact hm
  · obtain ⟨a, b, rfl⟩ := List.append_of_mem hγ
    obtain ⟨e1, e2⟩ := D.m_of_split (a := l₁ ++ a) (b := b) (by rw [h]; simp)
    obtain ⟨e1', e2'⟩ := D''.m_of_split (a := a) (b := b ++ l₁) (by simp [withRows])
    have hMr : M.rows = l₁ ++ (a ++ P.rows ++ b) := by
      rw [hM, insertBlock_rows, e1, e2]; simp
    have hm := movesTo_withRows_rotate M hMr
    have he : (M.withRows ((a ++ P.rows ++ b) ++ l₁)
        (by rw [hMr]; exact List.perm_append_comm)).toGrid = (insertBlock _ γ P D'').toGrid :=
      toGrid_eq_of_data _ _ rfl
        (by change (a ++ P.rows ++ b) ++ l₁ = D''.m₁ ++ P.rows ++ D''.m₂
            rw [e1', e2']; simp)
        (fun _ _ => rfl) (fun _ _ => rfl)
    rw [he] at hm
    exact hm

end RotateBase


/-! ### The slide -/

section SlideMain

variable {n m : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]
  {G : LabeledGrid n C R} {P : ProtBlock m C R}

/-- The internal rows of a protected block. -/
def ProtBlock.mid (P : ProtBlock m C R) : List R :=
  List.ofFn (fun i : Fin m => P.hr i.succ.castSucc)

omit [DecidableEq C] [DecidableEq R] in
theorem ProtBlock.rows_eq_mid (P : ProtBlock m C R) :
    P.rows = P.hr 0 :: (P.mid ++ [P.hr (Fin.last (m + 1))]) := by
  change List.ofFn P.hr = _
  rw [List.ofFn_succ, ofFn_succ_last]
  simp only [ProtBlock.mid, Fin.succ_last, Fin.succ_castSucc]

omit [DecidableEq C] [DecidableEq R] in
theorem ProtBlock.mem_mid {P : ProtBlock m C R} {x : R} (hx : x ∈ P.mid) :
    ∃ i : Fin m, x = P.hr i.succ.castSucc := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact ⟨i, rfl⟩

omit [DecidableEq C] [DecidableEq R] in
theorem ProtBlock.cols_eq_last (P : ProtBlock m C R) :
    P.cols = List.ofFn (fun j : Fin m => P.hc j.castSucc) ++ [P.hc (Fin.last m)] := by
  change List.ofFn P.hc = _; exact ofFn_succ_last _

omit [DecidableEq C] [DecidableEq R] in
theorem ProtBlock.cols_eq_first (P : ProtBlock m C R) :
    P.cols = P.hc 0 :: List.ofFn (fun j : Fin m => P.hc j.succ) := by
  change List.ofFn P.hc = _; exact List.ofFn_succ

/-- **Sliding the protected block to the next arc.** If the column `z` ends the arc `α` and
starts the arc `β`, the insertions of a block with new row labels into `α` and into `β` are
related by grid moves. -/
theorem movesTo_insertBlock_slide {z : C} (hz : z ∈ G.cols) {α β : R} (hXz : G.X z = α)
    (hOz : G.O z = β) (hfresh : ∀ i, P.hr i ∉ G.rows) (Dα : InsertData G α P)
    (Dβ : InsertData G β P) :
    (insertBlock G α P Dα).toGrid.MovesTo (insertBlock G β P Dβ).toGrid := by
  have : Nonempty C := ⟨z⟩
  have : Nonempty R := ⟨α⟩
  have hαβ : α ≠ β := fun e => G.O_ne_X z hz (by rw [hOz, hXz, e])
  -- rotate the rows so that `α` comes first
  have hsplit : G.rows = Dα.m₁ ++ (α :: Dα.m₂) := Dα.rows_eq
  have hβG₀ : β ∈ G.rows := by rw [← hOz]; exact G.O_mem z hz
  have hβmem : β ∈ Dα.m₂ ++ Dα.m₁ := by
    rcases Dα.mem_m_of_mem hβG₀ (Ne.symm hαβ) with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h
  obtain ⟨Cl, E, hCE⟩ := List.append_of_mem hβmem
  obtain ⟨L, R', hLR⟩ := List.append_of_mem hz
  have hperm : ((α :: Dα.m₂) ++ Dα.m₁).Perm G.rows := by
    rw [hsplit]; exact List.perm_append_comm
  set G' := G.withRows ((α :: Dα.m₂) ++ Dα.m₁) hperm with hG'
  have hG'rows : G'.rows = α :: (Cl ++ β :: E) := by
    change (α :: Dα.m₂) ++ Dα.m₁ = _; rw [List.cons_append, hCE]
  have hmemG' : ∀ x, x ∈ G'.rows ↔ x ∈ G.rows := fun x => hperm.mem_iff
  have hfresh' : ∀ i, P.hr i ∉ G'.rows := fun i h => hfresh i ((hmemG' _).mp h)
  let DA : InsertData G' α P :=
    { l₁ := L, l₂ := z :: R', m₁ := [], m₂ := Cl ++ β :: E, cols_eq := hLR,
      rows_eq := by rw [hG'rows]; rfl, cols_fresh := Dα.cols_fresh,
      rows_fresh := fun i h => absurd h (hfresh' i) }
  let DB : InsertData G' β P :=
    { l₁ := L ++ [z], l₂ := R', m₁ := α :: Cl, m₂ := E,
      cols_eq := by change G.cols = L ++ [z] ++ R'; rw [hLR]; simp,
      rows_eq := by rw [hG'rows]; rfl, cols_fresh := Dα.cols_fresh,
      rows_fresh := fun i h => absurd h (hfresh' i) }
  have hA := movesTo_insertBlock_rotate Dα hsplit DA
  have hB := movesTo_insertBlock_rotate Dβ hsplit DB
  refine hA.trans (GridDiagram.MovesTo.trans ?_ hB.symm)
  -- facts on the base grid
  have hGrows_nd := G'.rows_nodup
  rw [hG'rows] at hGrows_nd
  have hcolsnd := G.cols_nodup
  rw [hLR] at hcolsnd
  have hzL : z ∉ L := fun h => not_mem_of_nodup_middle hcolsnd (List.mem_append_left _ h)
  have hzR : z ∉ R' := fun h => not_mem_of_nodup_middle hcolsnd (List.mem_append_right _ h)
  have hβCl : β ∉ Cl := by
    intro h
    have := (List.nodup_cons.mp hGrows_nd).2
    exact (List.nodup_append.mp this).2.2 β h β (by simp) rfl
  have hClG : ∀ x ∈ Cl, x ∈ G.rows := fun x hx => (hmemG' x).mp (by rw [hG'rows]; simp [hx])
  have hEG : ∀ x ∈ E, x ∈ G.rows := fun x hx => (hmemG' x).mp (by rw [hG'rows]; simp [hx])
  have hαCl : α ∉ Cl := fun h => (List.nodup_cons.mp hGrows_nd).1 (by simp [h])
  have hαE : α ∉ E := fun h => (List.nodup_cons.mp hGrows_nd).1 (by simp [h])
  have hβE : β ∉ E := by
    intro h
    have := (List.nodup_cons.mp hGrows_nd).2
    have := (List.nodup_cons.mp (List.nodup_middle.mp this)).1
    exact this (List.mem_append_right _ h)
  have hblock_ne : ∀ (i : Fin (m + 2)) {x : R}, x ∈ G.rows → P.hr i ≠ x :=
    fun i x hx e => hfresh i (e ▸ hx)
  have hoRow_ne : ∀ (j : Fin (m + 1)) {x : R}, x ∈ G.rows → P.oRow j ≠ x := by
    intro j x hx
    unfold ProtBlock.oRow
    split_ifs <;> exact hblock_ne _ hx
  have hxRow_ne : ∀ (j : Fin (m + 1)) {x : R}, x ∈ G.rows → P.xRow j ≠ x :=
    fun j x hx => hblock_ne _ hx
  have hGO : ∀ c ∈ G.cols, c ≠ z → G.O c ≠ β := fun c hc hcz e =>
    hcz (G.O_inj c hc z hz (e.trans hOz.symm))
  have hGX : ∀ c ∈ G.cols, c ≠ z → G.X c ≠ α := fun c hc hcz e =>
    hcz (G.X_inj c hc z hz (e.trans hXz.symm))
  have hαG : α ∈ G.rows := by rw [hsplit]; simp
  have hβG : β ∈ G.rows := by rw [← hOz]; exact G.O_mem z hz
  -- the right absorption in the insertion into `α`
  set A := insertBlock G' α P DA with hAdef
  have hAO : ∀ c ∈ G.cols, A.O c = if G.O c = α then P.hr 0 else G.O c := fun c hc => by
    rw [hAdef, insertBlock_O]; exact DA.blockO_old hc
  have hAX : ∀ c ∈ G.cols, A.X c = if G.X c = α then P.hr (Fin.last (m + 1)) else G.X c :=
    fun c hc => by rw [hAdef, insertBlock_X]; exact DA.blockX_old hc
  have hAOB : ∀ j, A.O (P.hc j) = P.oRow j := fun j => by rw [hAdef, insertBlock_O, blockO_hc]
  have hAXB : ∀ j, A.X (P.hc j) = P.xRow j := fun j => by rw [hAdef, insertBlock_X, blockX_hc]
  obtain ⟨MA, hcA, hrA, hOA, hXA, hmA⟩ := A.exists_mergeO_up
    (l₁ := L ++ List.ofFn (fun j : Fin m => P.hc j.castSucc)) (l₂ := R') (c := z)
    (d := P.hc (Fin.last m)) (m₁ := P.hr 0 :: P.mid) (mid := Cl) (m₂ := E)
    (e := P.hr (Fin.last (m + 1))) (z := β)
    (Or.inr (by rw [hAdef, insertBlock_cols, P.cols_eq_last]; simp; rfl))
    (by rw [hAdef, insertBlock_rows, P.rows_eq_mid]
        simp only [List.append_assoc, List.cons_append]; rfl)
    (by rw [hAX z hz, if_pos hXz]) (by rw [hAO z hz, if_neg (by rw [hOz]; exact Ne.symm hαβ),
      hOz])
    (by rw [hAOB, ProtBlock.oRow_last])
    (by rw [hAXB]; exact hxRow_ne _ hβG)
    (fun r hr => by rw [hAXB]; exact (hxRow_ne _ (hClG r hr)).symm)
  have hcA' : MA.cols = L ++ P.cols ++ R' := by rw [hcA, P.cols_eq_last]; simp
  -- the left absorption in the insertion into `β`
  set B := insertBlock G' β P DB with hBdef
  have hBO : ∀ c ∈ G.cols, B.O c = if G.O c = β then P.hr 0 else G.O c := fun c hc => by
    rw [hBdef, insertBlock_O]; exact DB.blockO_old hc
  have hBX : ∀ c ∈ G.cols, B.X c = if G.X c = β then P.hr (Fin.last (m + 1)) else G.X c :=
    fun c hc => by rw [hBdef, insertBlock_X]; exact DB.blockX_old hc
  have hBOB : ∀ j, B.O (P.hc j) = P.oRow j := fun j => by rw [hBdef, insertBlock_O, blockO_hc]
  have hBXB : ∀ j, B.X (P.hc j) = P.xRow j := fun j => by rw [hBdef, insertBlock_X, blockX_hc]
  obtain ⟨MB, hcB, hrB, hOB, hXB, hmB⟩ := B.exists_mergeX_down
    (l₁ := L) (l₂ := List.ofFn (fun j : Fin m => P.hc j.succ) ++ R') (c := z) (d := P.hc 0)
    (m₁ := []) (mid := Cl) (m₂ := (P.mid ++ [P.hr (Fin.last (m + 1))]) ++ E)
    (e := P.hr 0) (z := α)
    (Or.inl (by
      rw [hBdef, insertBlock_cols, P.cols_eq_first]
      change (L ++ [z]) ++ (P.hc 0 :: List.ofFn (fun j : Fin m => P.hc j.succ)) ++ R' = _
      simp))
    (by rw [hBdef, insertBlock_rows, P.rows_eq_mid]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        rfl)
    (by rw [hBO z hz, if_pos hOz]) (by rw [hBX z hz, if_neg (by rw [hXz]; exact hαβ), hXz])
    (by rw [hBXB, ProtBlock.xRow_zero])
    (by rw [hBOB]; exact hoRow_ne _ hαG)
    (fun r hr => by rw [hBOB]; exact (hoRow_ne _ (hClG r hr)).symm)
  have hcB' : MB.cols = L ++ P.cols ++ R' := by rw [hcB, P.cols_eq_first]; simp
  -- the internal rows pass the rows between `α` and `β`
  have hMAcol : ∀ c ∈ MA.cols, c ∉ P.cols → c ∈ G.cols ∧ c ≠ z := by
    intro c hc hcP
    rw [hcA', List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ⟨by rw [hLR]; simp [hc], fun e => hzL (e ▸ hc)⟩
    · exact absurd hc hcP
    · exact ⟨by rw [hLR]; simp [hc], fun e => hzR (e ▸ hc)⟩
  have hMAO : ∀ c ∈ MA.cols, c ∉ P.cols → MA.O c = if G.O c = α then P.hr 0 else G.O c := by
    intro c hc hcP
    rw [hOA, Function.update_of_ne (fun e => hcP (by rw [e]; exact P.hc_mem _)),
      hAO c (hMAcol c hc hcP).1]
  have hMAX : ∀ c ∈ MA.cols, c ∉ P.cols → MA.X c = G.X c := by
    intro c hc hcP
    obtain ⟨hcG, hcz⟩ := hMAcol c hc hcP
    rw [hXA, hAX c hcG, if_neg (hGX c hcG hcz)]
  have hMAOB : ∀ j, MA.O (P.hc j) = if j = Fin.last m then β else P.oRow j := by
    intro j
    rw [hOA]
    by_cases hj : j = Fin.last m
    · rw [hj, Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne (fun e => hj (P.hc_inj e)), hAOB, if_neg hj]
  have hMAXB : ∀ j, MA.X (P.hc j) = P.xRow j := fun j => by rw [hXA, hAXB]
  have hmidne : ∀ b ∈ P.mid, b ≠ P.hr 0 ∧ b ≠ P.hr (Fin.last (m + 1)) ∧ b ∉ G.rows := by
    intro b hb
    obtain ⟨i, rfl⟩ := ProtBlock.mem_mid hb
    refine ⟨fun e => ?_, fun e => ?_, hfresh _⟩
    · have := congrArg Fin.val (P.hr_inj e); simp at this
    · have := congrArg Fin.val (P.hr_inj e); simp at this; omega
  obtain ⟨MA2, hc2, hr2, hO2, hX2, hm2⟩ := exists_moveRowsPast MA (m₁ := [P.hr 0])
    (Bl := P.mid) (Cl := Cl) (m₂ := β :: E) (by rw [hrA]; simp) (by
      intro b hb y hy
      refine rowsNonint_of_block MA hcA' (fun c hc hcb => ?_) (fun c hc hcy => ?_)
      · by_contra hcP
        obtain ⟨h1, h2, h3⟩ := hmidne b hb
        rcases hcb with e | e
        · rw [hMAO c hc hcP] at e
          split_ifs at e with h
          · exact h1 e.symm
          · exact h3 (e ▸ G.O_mem c (hMAcol c hc hcP).1)
        · rw [hMAX c hc hcP] at e
          exact h3 (e ▸ G.X_mem c (hMAcol c hc hcP).1)
      · intro hcP
        obtain ⟨j, rfl⟩ := P.mem_cols.mp hcP
        rcases hcy with e | e
        · rw [hMAOB] at e
          split_ifs at e
          · exact hβCl (e ▸ hy)
          · exact hoRow_ne j (hClG y hy) e
        · rw [hMAXB] at e
          exact hxRow_ne j (hClG y hy) e)
  -- the two absorbed grids agree after renaming the ports
  set gs : R → R := fun x => if x = P.hr 0 then α else if x = β then P.hr (Fin.last (m + 1))
    else x with hgs
  have hgs0 : gs (P.hr 0) = α := by simp [hgs]
  have hgsβ : gs β = P.hr (Fin.last (m + 1)) := by
    simp only [hgs, if_neg (hblock_ne 0 hβG).symm, if_true]
  have hgsfix : ∀ x, x ≠ P.hr 0 → x ≠ β → gs x = x := fun x h1 h2 => by
    simp only [hgs, if_neg h1, if_neg h2]
  have hrows2 : MA2.rows = P.hr 0 :: (Cl ++ P.mid ++ β :: E) := by rw [hr2]; simp
  have hMBrows : MB.rows = α :: (Cl ++ P.mid ++ P.hr (Fin.last (m + 1)) :: E) := by
    rw [hrB]; simp
  have hrec : MA2.toGrid = MB.toGrid := by
    symm
    apply toGrid_eq_of_image MA2 MB id gs
    · exact fun c _ c' _ h => h
    · intro x hx y hy h
      rw [hrows2] at hx hy
      have hcase : ∀ w, w ∈ P.hr 0 :: (Cl ++ P.mid ++ β :: E) →
          (w = P.hr 0 ∧ gs w = α) ∨ (w = β ∧ gs w = P.hr (Fin.last (m + 1))) ∨
          (gs w = w ∧ w ≠ α ∧ w ≠ P.hr (Fin.last (m + 1))) := by
        intro w hw
        simp only [List.mem_cons, List.mem_append] at hw
        rcases hw with rfl | ((hw | hw) | rfl | hw)
        · exact Or.inl ⟨rfl, hgs0⟩
        · exact Or.inr (Or.inr ⟨hgsfix w (fun e => hblock_ne 0 (hClG w hw) e.symm)
            (fun e => hβCl (e ▸ hw)), fun e => hαCl (e ▸ hw),
            fun e => hblock_ne _ (hClG w hw) e.symm⟩)
        · obtain ⟨h1, h2, h3⟩ := hmidne w hw
          exact Or.inr (Or.inr ⟨hgsfix w h1 (fun e => h3 (e ▸ hβG)),
            fun e => h3 (e ▸ hαG), h2⟩)
        · exact Or.inr (Or.inl ⟨rfl, hgsβ⟩)
        · exact Or.inr (Or.inr ⟨hgsfix w (fun e => hblock_ne 0 (hEG w hw) e.symm)
            (fun e => hβE (e ▸ hw)), fun e => hαE (e ▸ hw),
            fun e => hblock_ne _ (hEG w hw) e.symm⟩)
      rcases hcase x hx with ⟨rfl, hx'⟩ | ⟨rfl, hx'⟩ | ⟨hx', hxα, hxl⟩ <;>
        rcases hcase y hy with ⟨rfl, hy'⟩ | ⟨rfl, hy'⟩ | ⟨hy', hyα, hyl⟩
      · rfl
      · rw [hx', hy'] at h; exact absurd (h.symm ▸ hαG) (hfresh _)
      · rw [hx', hy'] at h; exact absurd h.symm hyα
      · rw [hx', hy'] at h; exact absurd (h ▸ hαG) (hfresh _)
      · rfl
      · rw [hx', hy'] at h; exact absurd h.symm hyl
      · rw [hx', hy'] at h; exact absurd h hxα
      · rw [hx', hy'] at h; exact absurd h hxl
      · rw [hx', hy'] at h; exact h
    · rw [hcB', hc2, hcA', List.map_id]
    · rw [hMBrows, hrows2, List.map_cons, hgs0, List.map_append, List.map_append, List.map_cons,
        hgsβ]
      have hCl : Cl.map gs = Cl := by
        conv_rhs => rw [← List.map_id Cl]
        exact List.map_congr_left (fun x hx => hgsfix x
          (fun e => hblock_ne 0 (hClG x hx) e.symm) (fun e => hβCl (e ▸ hx)))
      have hmid : P.mid.map gs = P.mid := by
        conv_rhs => rw [← List.map_id P.mid]
        exact List.map_congr_left (fun x hx => hgsfix x (hmidne x hx).1
          (fun e => (hmidne x hx).2.2 (e ▸ hβG)))
      have hE : E.map gs = E := by
        conv_rhs => rw [← List.map_id E]
        exact List.map_congr_left (fun x hx => hgsfix x
          (fun e => hblock_ne 0 (hEG x hx) e.symm) (fun e => hβE (e ▸ hx)))
      rw [hCl, hmid, hE]
    · intro c hc
      rw [hc2, hcA'] at hc
      rw [hO2, hOB]
      change B.O c = gs (MA.O c)
      by_cases hcP : c ∈ P.cols
      · obtain ⟨j, rfl⟩ := P.mem_cols.mp hcP
        rw [hBOB, hMAOB]
        split_ifs with hj
        · rw [hj, ProtBlock.oRow_last, hgsβ]
        · exact (hgsfix _ (P.oRow_ne_input j) (hoRow_ne j hβG)).symm
      · have hcM : c ∈ MA.cols := by rw [hcA']; exact hc
        obtain ⟨hcG, hcz⟩ := hMAcol c hcM hcP
        rw [hMAO c hcM hcP, hBO c hcG, if_neg (hGO c hcG hcz)]
        split_ifs with h
        · rw [hgs0, h]
        · exact (hgsfix _ (fun e => hblock_ne 0 (G.O_mem c hcG) e.symm) (hGO c hcG hcz)).symm
    · intro c hc
      rw [hc2, hcA'] at hc
      rw [hX2, hXB]
      change Function.update B.X (P.hc 0) α c = gs (MA.X c)
      by_cases hcP : c ∈ P.cols
      · obtain ⟨j, rfl⟩ := P.mem_cols.mp hcP
        rw [hMAXB]
        by_cases hj : j = 0
        · rw [hj, Function.update_self, ProtBlock.xRow_zero, hgs0]
        · rw [Function.update_of_ne (fun e => hj (P.hc_inj e)), hBXB]
          refine (hgsfix _ (fun e => hj ?_) (hxRow_ne j hβG)).symm
          exact P.xRow_inj (e.trans P.xRow_zero.symm)
      · have hcM : c ∈ MA.cols := by rw [hcA']; exact hc
        obtain ⟨hcG, hcz⟩ := hMAcol c hcM hcP
        rw [Function.update_of_ne (fun e => hcP (by rw [e]; exact P.hc_mem 0)), hMAX c hcM hcP,
          hBX c hcG]
        split_ifs with h
        · rw [h, hgsβ]
        · exact (hgsfix _ (fun e => hblock_ne 0 (G.X_mem c hcG) e.symm) h).symm
  exact hmA.trans (hm2.trans (by rw [hrec]; exact hmB.symm))

end SlideMain

end OnLeConjecture.KnotTheory.MarkedCancel
