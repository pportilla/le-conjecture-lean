/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelGrid
public import OnLeConjecture.KnotTheory.MarkedCancelMove
public import OnLeConjecture.KnotTheory.TorusWordGridHybrid

/-!
# Marked window grids

A labeled grid `M` whose lists and markings are the images of those of a labeled grid `L` under
maps of the labels that are injective on the labels of `L` has the grid diagram of `L`
(`toGrid_eq_of_image`).

For a word `B ++ t` with a block of `K` letters, a window state `S`, and a corner `p`, the
*marked window grid* (`winGrid`) is the insertion of a protected block into the row of the arc
leaving `p` of the initial grid `SignedGrid.sInitGrid S hB hS`, with the block columns after all
other columns. The output row of the block keeps the label of the marked arc, and the other block
rows are new outside labels (`winBlock`). Its grid diagram is that of the marked word grid with the
block at the end and the key `SignedGrid.skappa` (`toGrid_winGrid`). Hence, by the first framing
fact (`movesTo_insertBlock`), it is related by grid moves to the marked word grid of the written
proof of Statement E (`statement_E_complete_proof.tex`, Section 8), with the block after the
column of `p` (`markedGrid_movesTo_winGrid`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid

/-! ### Grids with the image data of another grid -/

section Image

variable {N : ℕ} {C R C' R' : Type*} [DecidableEq R] [DecidableEq R'] [Nonempty C] [Nonempty R]

/-- **Recognition by an image.** If the lists and markings of `M` are the images of those of `L`
under maps injective on the labels of `L`, then `M` and `L` have the same grid diagram. -/
theorem toGrid_eq_of_image (L : LabeledGrid N C R) (M : LabeledGrid N C' R') (f : C → C')
    (g : R → R') (hf : Set.InjOn f {c | c ∈ L.cols}) (hg : Set.InjOn g {r | r ∈ L.rows})
    (hc : M.cols = L.cols.map f) (hr : M.rows = L.rows.map g)
    (hO : ∀ c ∈ L.cols, M.O (f c) = g (L.O c)) (hX : ∀ c ∈ L.cols, M.X (f c) = g (L.X c)) :
    M.toGrid = L.toGrid := by
  have hfL : ∀ c ∈ L.cols, Function.invFunOn f {c | c ∈ L.cols} (f c) = c :=
    fun c hc => hf.leftInvOn_invFunOn hc
  have hgL : ∀ r ∈ L.rows, Function.invFunOn g {r | r ∈ L.rows} (g r) = r :=
    fun r hr => hg.leftInvOn_invFunOn hr
  rw [← L.toGrid_relabel f _ g _ hfL hgL]
  apply toGrid_eq_of_data
  · exact hc
  · exact hr
  · intro c' hc'
    rw [hc] at hc'
    obtain ⟨c, hcL, rfl⟩ := List.mem_map.mp hc'
    change M.O (f c) = g (L.O (Function.invFunOn f {c | c ∈ L.cols} (f c)))
    rw [hfL c hcL, hO c hcL]
  · intro c' hc'
    rw [hc] at hc'
    obtain ⟨c, hcL, rfl⟩ := List.mem_map.mp hc'
    change M.X (f c) = g (L.X (Function.invFunOn f {c | c ∈ L.cols} (f c)))
    rw [hfL c hcL, hX c hcL]

end Image

/-! ### The marked word grid with the block at the end -/

section EndData

variable {m k : ℕ} (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ) (hL : 0 < v.length)
  (p : Fin v.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
  (hO : H.O (Fin.last k) = 0)

/-- The insertion data of a marked word grid with the block after all columns. -/
def endData : InsertData (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO) where
  l₁ := (plainGrid v κ hL).cols
  l₂ := []
  m₁ := (markData v κ hL p H hX hO).m₁
  m₂ := (markData v κ hL p H hX hO).m₂
  cols_eq := by simp
  rows_eq := (markData v κ hL p H hX hO).rows_eq
  cols_fresh := (markData v κ hL p H hX hO).cols_fresh
  rows_fresh := (markData v κ hL p H hX hO).rows_fresh

/-- The marked word grid is related by grid moves to the marked word grid with the block at the
end. -/
theorem markedGrid_movesTo_end :
    (markedGrid v κ hL p H hX hO).toGrid.MovesTo
      (insertBlock (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO)
        (endData v κ hL p H hX hO)).toGrid :=
  movesTo_insertBlock _ _

end EndData

/-! ### The marked window grid -/

section Window

variable {m K E i k : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
  {B t : SignedAdjacentWord m} (S : WState) (hB : BlockS K E i offs sg B t (flagOf flags))
  (hS : InitOKS K S offs sg flags) (p : Fin (B ++ t).length × Fin 3)
  (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0)

theorem sgRow_ne_new (q : Fin (B ++ t).length × Fin 3) (j : ℕ) (c : Fin 3) :
    sgRow K S (B ++ t) q ≠ Sum.inr ((B ++ t).length + j, c) := by
  unfold sgRow
  split_ifs
  · simp
  · simp
  · simp only [ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
    intro h; have := q.1.isLt; omega

theorem sfCol_ne_new (q : Fin (B ++ t).length × Fin 3) (j : ℕ) (c : Fin 3) :
    sfCol K (B ++ t) q ≠ Sum.inr ((B ++ t).length + j, c) := by
  unfold sfCol
  split_ifs
  · simp
  · simp only [ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
    intro h; have := q.1.isLt; omega

variable (K) in
/-- The protected block of a marked window grid: the output row keeps the label of the marked
arc, and the other rows and the columns are new outside labels. -/
def winBlock : ProtBlock k BCol BRow where
  H := H
  hc j := Sum.inr ((B ++ t).length + j.val, 0)
  hr r := if r = Fin.last (k + 1) then sgRow K S (B ++ t) p
    else Sum.inr ((B ++ t).length + r.val, 1)
  hc_inj j j' h := by
    simp only [Sum.inr.injEq, Prod.mk.injEq, add_right_inj] at h
    exact Fin.ext h.1
  hr_inj r r' h := by
    simp only at h
    split_ifs at h with h1 h2 h2
    · rw [h1, h2]
    · exact absurd h (sgRow_ne_new S p _ _)
    · exact absurd h.symm (sgRow_ne_new S p _ _)
    · simp only [Sum.inr.injEq, Prod.mk.injEq, add_right_inj] at h
      exact Fin.ext h.1
  X_zero := hX
  O_last := hO

theorem winBlock_hr_last :
    (winBlock K S p H hX hO).hr (Fin.last (k + 1)) = sgRow K S (B ++ t) p := by
  simp [winBlock]

theorem winBlock_hr_of_ne {r : Fin (k + 2)} (hr : r ≠ Fin.last (k + 1)) :
    (winBlock K S p H hX hO).hr r = Sum.inr ((B ++ t).length + r.val, 1) := by
  simp [winBlock, hr]

theorem winBlock_hc (j : Fin (k + 1)) :
    (winBlock K S p H hX hO).hc j = Sum.inr ((B ++ t).length + j.val, 0) := rfl

theorem sgRow_mem_rows : sgRow K S (B ++ t) p ∈ (sInitGrid S hB hS).rows :=
  (mem_sInitGrid_rows S hB hS _).mpr ⟨p, rfl⟩

/-- The insertion data of a marked window grid: the block columns follow all other columns. -/
def winData : InsertData (sInitGrid S hB hS) (sgRow K S (B ++ t) p) (winBlock K S p H hX hO) where
  l₁ := (sInitGrid S hB hS).cols
  l₂ := []
  m₁ := (List.append_of_mem (sgRow_mem_rows S hB hS p)).choose
  m₂ := (List.append_of_mem (sgRow_mem_rows S hB hS p)).choose_spec.choose
  cols_eq := by simp
  rows_eq := (List.append_of_mem (sgRow_mem_rows S hB hS p)).choose_spec.choose_spec
  cols_fresh j hj := by
    change Sum.inr ((B ++ t).length + j.val, 0) ∈ (sCols (B ++ t)).map (sfCol K (B ++ t)) at hj
    obtain ⟨q, -, hq⟩ := List.mem_map.mp hj
    exact sfCol_ne_new q _ _ hq
  rows_fresh r hr := by
    by_cases h : r = Fin.last (k + 1)
    · rw [h]
      exact winBlock_hr_last S p H hX hO
    · exfalso
      rw [winBlock_hr_of_ne S p H hX hO h] at hr
      obtain ⟨q, hq⟩ := (mem_sInitGrid_rows S hB hS _).mp hr
      exact sgRow_ne_new S q _ _ hq

/-- **The marked window grid** of `B ++ t` for the window state `S`, marked arc leaving `p`, and
protected grid `H`: the block columns follow all other columns. -/
def winGrid : LabeledGrid ((B ++ t).length * 3 + k + 1) BCol BRow :=
  insertBlock (sInitGrid S hB hS) (sgRow K S (B ++ t) p) (winBlock K S p H hX hO)
    (winData S hB hS p H hX hO)

variable (K) in
/-- The map of column labels from the marked word grid to the marked window grid. -/
def winColMap (v : SignedAdjacentWord m) : BCol → BCol
  | Sum.inl x => Sum.inl x
  | Sum.inr q => if hq : q.1 < v.length then sfCol K v (⟨q.1, hq⟩, q.2) else Sum.inr q

variable (K k) in
/-- The map of row labels from the marked word grid to the marked window grid. -/
def winRowMap (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) : BRow → BRow
  | Sum.inl x => Sum.inl x
  | Sum.inr q => if hq : q.1 < v.length then sgRow K S v (⟨q.1, hq⟩, q.2)
      else if q.1 = v.length + (k + 1) then sgRow K S v p else Sum.inr q

theorem winColMap_corner (q : Fin (B ++ t).length × Fin 3) :
    winColMap K (B ++ t) (Sum.inr (q.1.val, q.2)) = sfCol K (B ++ t) q := by
  simp only [winColMap]; rw [dif_pos q.1.isLt]

theorem winRowMap_corner (q : Fin (B ++ t).length × Fin 3) :
    winRowMap K k S (B ++ t) p (Sum.inr (q.1.val, q.2)) = sgRow K S (B ++ t) q := by
  simp only [winRowMap]; rw [dif_pos q.1.isLt]

theorem winRowMap_hr (r : Fin (k + 2)) :
    winRowMap K k S (B ++ t) p ((markBlock (B ++ t) H hX hO).hr r) =
      (winBlock K S p H hX hO).hr r := by
  rw [stdBlock_hr]
  simp only [winRowMap]
  rw [dif_neg (by omega)]
  by_cases h : r = Fin.last (k + 1)
  · subst h
    rw [if_pos (by simp), winBlock_hr_last]
  · rw [if_neg (fun e => h (Fin.ext (by simp only [Fin.val_last]; omega))),
      winBlock_hr_of_ne S p H hX hO h]

theorem winColMap_hc (j : Fin (k + 1)) :
    winColMap K (B ++ t) ((markBlock (B ++ t) H hX hO).hc j) =
      (winBlock K S p H hX hO).hc j := by
  rw [stdBlock_hc]
  simp only [winColMap]
  rw [dif_neg (by omega)]
  rfl

/-- **The marked window grid has the grid diagram of a marked word grid**, with the block at the
end and the key `SignedGrid.skappa`. -/
theorem toGrid_winGrid :
    (winGrid S hB hS p H hX hO).toGrid =
      (insertBlock (plainGrid (B ++ t) (skappa K S (B ++ t)) hB.len_pos) (markRow (B ++ t) p)
        (markBlock (B ++ t) H hX hO)
        (endData (B ++ t) (skappa K S (B ++ t)) hB.len_pos p H hX hO)).toGrid := by
  set κ := skappa K S (B ++ t) with hκ
  set hL := hB.len_pos
  set L := insertBlock (plainGrid (B ++ t) κ hL) (markRow (B ++ t) p) (markBlock (B ++ t) H hX hO)
    (endData (B ++ t) κ hL p H hX hO) with hLdef
  set f := winColMap K (B ++ t) with hf
  set g := winRowMap K k S (B ++ t) p with hg
  have hD := endData (B ++ t) κ hL p H hX hO
  have hLc :
      L.cols = (sCols (B ++ t)).map (sfCol 0 (B ++ t)) ++ (markBlock (B ++ t) H hX hO).cols := by
    rw [hLdef, insertBlock_cols]; simp [endData, plainGrid_cols]
  have hgw : ∀ q : Fin (B ++ t).length × Fin 3, g (Sum.inr (q.1.val, q.2)) = sgRow K S (B ++ t) q :=
    winRowMap_corner S p
  have hfw : ∀ q : Fin (B ++ t).length × Fin 3, f (Sum.inr (q.1.val, q.2)) = sfCol K (B ++ t) q :=
    winColMap_corner
  -- the plain rows and their images
  have hrows_map : (plainGrid (B ++ t) κ hL).rows.map g = (sInitGrid S hB hS).rows := by
    rw [plainGrid_rows, sInitGrid_rows, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp, sfCol_zero]
    exact hgw q
  have hm₁ : (endData (B ++ t) κ hL p H hX hO).m₁.map g = (winData S hB hS p H hX hO).m₁ := by
    have hrw : (sInitGrid S hB hS).rows = (endData (B ++ t) κ hL p H hX hO).m₁.map g ++
        sgRow K S (B ++ t) p :: (endData (B ++ t) κ hL p H hX hO).m₂.map g := by
      rw [← hrows_map, (endData (B ++ t) κ hL p H hX hO).rows_eq, List.map_append, List.map_cons]
      congr 2
      exact hgw p
    let D₂ : InsertData (sInitGrid S hB hS) (sgRow K S (B ++ t) p) (winBlock K S p H hX hO) :=
      { winData S hB hS p H hX hO with
        m₁ := (endData (B ++ t) κ hL p H hX hO).m₁.map g
        m₂ := (endData (B ++ t) κ hL p H hX hO).m₂.map g
        rows_eq := hrw }
    exact D₂.m₁_eq (winData S hB hS p H hX hO)
  have hm₂ : (endData (B ++ t) κ hL p H hX hO).m₂.map g = (winData S hB hS p H hX hO).m₂ := by
    have hrw : (sInitGrid S hB hS).rows = (endData (B ++ t) κ hL p H hX hO).m₁.map g ++
        sgRow K S (B ++ t) p :: (endData (B ++ t) κ hL p H hX hO).m₂.map g := by
      rw [← hrows_map, (endData (B ++ t) κ hL p H hX hO).rows_eq, List.map_append, List.map_cons]
      congr 2
      exact hgw p
    let D₂ : InsertData (sInitGrid S hB hS) (sgRow K S (B ++ t) p) (winBlock K S p H hX hO) :=
      { winData S hB hS p H hX hO with
        m₁ := (endData (B ++ t) κ hL p H hX hO).m₁.map g
        m₂ := (endData (B ++ t) κ hL p H hX hO).m₂.map g
        rows_eq := hrw }
    exact D₂.m₂_eq (winData S hB hS p H hX hO)
  have hblock_rows : (markBlock (B ++ t) H hX hO).rows.map g = (winBlock K S p H hX hO).rows := by
    change (List.ofFn _).map g = List.ofFn _
    rw [List.map_ofFn]
    congr 1
    funext r
    exact winRowMap_hr S p H hX hO r
  have hblock_cols : (markBlock (B ++ t) H hX hO).cols.map f = (winBlock K S p H hX hO).cols := by
    change (List.ofFn _).map f = List.ofFn _
    rw [List.map_ofFn]
    congr 1
    funext j
    exact winColMap_hc S p H hX hO j
  -- injectivity
  have hsg_inj : ∀ q q' : Fin (B ++ t).length × Fin 3,
      sgRow K S (B ++ t) q = sgRow K S (B ++ t) q' → q = q' :=
    fun q q' h => by rw [← sgRowInv_sgRow S hB hS q, h, sgRowInv_sgRow S hB hS q']
  have hsf_inj : ∀ q q' : Fin (B ++ t).length × Fin 3,
      sfCol K (B ++ t) q = sfCol K (B ++ t) q' → q = q' :=
    fun q q' h => by rw [← sfColInv_sfCol (B ++ t) hL q, h, sfColInv_sfCol (B ++ t) hL q']
  have hcolL : ∀ c ∈ L.cols, (∃ q : Fin (B ++ t).length × Fin 3, c = Sum.inr (q.1.val, q.2)) ∨
      ∃ j, c = (markBlock (B ++ t) H hX hO).hc j := by
    intro c hc
    rw [hLc, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hc
      exact Or.inl ⟨q, sfCol_zero (B ++ t) q⟩
    · obtain ⟨j, rfl⟩ := (markBlock (B ++ t) H hX hO).mem_cols.mp hc
      exact Or.inr ⟨j, rfl⟩
  have hrowL : ∀ r ∈ L.rows,
      (∃ q : Fin (B ++ t).length × Fin 3, q ≠ p ∧ r = Sum.inr (q.1.val, q.2)) ∨
      ∃ j, r = (markBlock (B ++ t) H hX hO).hr j := by
    intro r hr
    rw [hLdef, insertBlock_rows] at hr
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · have hmem : r ∈ (plainGrid (B ++ t) κ hL).rows := by
        rw [(endData (B ++ t) κ hL p H hX hO).rows_eq]; simp [hr]
      obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hmem
      refine Or.inl ⟨q, fun e => (endData (B ++ t) κ hL p H hX hO).not_mem_m₁ ?_, rfl⟩
      subst e; exact hr
    · obtain ⟨j, rfl⟩ := (markBlock (B ++ t) H hX hO).mem_rows.mp hr
      exact Or.inr ⟨j, rfl⟩
    · have hmem : r ∈ (plainGrid (B ++ t) κ hL).rows := by
        rw [(endData (B ++ t) κ hL p H hX hO).rows_eq]; simp [hr]
      obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hmem
      refine Or.inl ⟨q, fun e => (endData (B ++ t) κ hL p H hX hO).not_mem_m₂ ?_, rfl⟩
      subst e; exact hr
  have hfh : ∀ j, f ((markBlock (B ++ t) H hX hO).hc j) = (winBlock K S p H hX hO).hc j :=
    winColMap_hc S p H hX hO
  have hgh : ∀ r, g ((markBlock (B ++ t) H hX hO).hr r) = (winBlock K S p H hX hO).hr r :=
    winRowMap_hr S p H hX hO
  apply toGrid_eq_of_image L _ f g
  · rintro c hc c' hc' h
    rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩ <;> rcases hcolL c' hc' with ⟨q', rfl⟩ | ⟨j', rfl⟩
    · rw [hfw, hfw] at h; rw [hsf_inj q q' h]
    · rw [hfw, hfh] at h; exact absurd h (sfCol_ne_new q _ _)
    · rw [hfw, hfh] at h; exact absurd h.symm (sfCol_ne_new q' _ _)
    · rw [hfh, hfh] at h; rw [(winBlock K S p H hX hO).hc_inj h]
  · rintro r hr r' hr' h
    rcases hrowL r hr with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ <;>
      rcases hrowL r' hr' with ⟨q', hq', rfl⟩ | ⟨j', rfl⟩
    · rw [hgw, hgw] at h; rw [hsg_inj q q' h]
    · rw [hgw, hgh] at h
      by_cases hj : j' = Fin.last (k + 1)
      · rw [hj, winBlock_hr_last] at h; exact absurd (hsg_inj q p h) hq
      · rw [winBlock_hr_of_ne S p H hX hO hj] at h; exact absurd h (sgRow_ne_new S q _ _)
    · rw [hgw, hgh] at h
      by_cases hj : j = Fin.last (k + 1)
      · rw [hj, winBlock_hr_last] at h; exact absurd (hsg_inj q' p h.symm) hq'
      · rw [winBlock_hr_of_ne S p H hX hO hj] at h; exact absurd h.symm (sgRow_ne_new S q' _ _)
    · rw [hgh, hgh] at h; rw [(winBlock K S p H hX hO).hr_inj h]
  · change (sInitGrid S hB hS).cols ++ (winBlock K S p H hX hO).cols ++ [] = L.cols.map f
    rw [hLc, List.map_append, hblock_cols, List.append_nil, List.map_map]
    congr 1
    change (sCols (B ++ t)).map (sfCol K (B ++ t)) = _
    apply List.map_congr_left
    intro q _
    simp only [Function.comp, sfCol_zero]
    exact (hfw q).symm
  · change (winData S hB hS p H hX hO).m₁ ++ (winBlock K S p H hX hO).rows ++
      (winData S hB hS p H hX hO).m₂ = _
    rw [hLdef, insertBlock_rows, List.map_append, List.map_append, hm₁, hm₂, hblock_rows]
  · intro c hc
    rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
    · rw [hfw]
      change blockO _ _ _ (sfCol K (B ++ t) q) = g (blockO _ _ _ (Sum.inr (q.1.val, q.2)))
      rw [(winData S hB hS p H hX hO).blockO_old (by
          change sfCol K (B ++ t) q ∈ (sCols (B ++ t)).map (sfCol K (B ++ t))
          exact List.mem_map_of_mem (mem_sCols (B ++ t) q)),
        (endData (B ++ t) κ hL p H hX hO).blockO_old (by
          rw [plainGrid_cols]
          exact List.mem_map.mpr ⟨q, mem_sCols (B ++ t) q, sfCol_zero (B ++ t) q⟩),
        plainGrid_O, sInitGrid_O, sfColInv_sfCol]
      by_cases hqp : q = p
      · subst hqp
        rw [if_pos rfl, if_pos rfl, hgh]
      · rw [if_neg (fun e => hqp (hsg_inj q p e)),
          if_neg (fun e => hqp (by
            simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
            exact Prod.ext (Fin.ext e.1) e.2)), hgw]
    · rw [hfh]
      change blockO _ _ _ ((winBlock K S p H hX hO).hc j) =
        g (blockO _ _ _ ((markBlock (B ++ t) H hX hO).hc j))
      rw [blockO_hc, blockO_hc]
      unfold ProtBlock.oRow
      change _ = g (if H.O j = 0 then _ else _)
      change (if H.O j = 0 then _ else _) = _
      split_ifs <;> rw [hgh]; rfl
  · intro c hc
    rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
    · rw [hfw]
      change blockX _ _ _ (sfCol K (B ++ t) q) = g (blockX _ _ _ (Sum.inr (q.1.val, q.2)))
      rw [(winData S hB hS p H hX hO).blockX_old (by
          change sfCol K (B ++ t) q ∈ (sCols (B ++ t)).map (sfCol K (B ++ t))
          exact List.mem_map_of_mem (mem_sCols (B ++ t) q)),
        (endData (B ++ t) κ hL p H hX hO).blockX_old (by
          rw [plainGrid_cols]
          exact List.mem_map.mpr ⟨q, mem_sCols (B ++ t) q, sfCol_zero (B ++ t) q⟩),
        plainGrid_X, sInitGrid_X, sfColInv_sfCol]
      by_cases hqp : (sM (B ++ t)).symm q = p
      · rw [hqp, if_pos rfl, if_pos rfl, hgh, winBlock_hr_last]
      · rw [if_neg (fun e => hqp (hsg_inj _ p e)),
          if_neg (fun e => hqp (by
            simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
            exact Prod.ext (Fin.ext e.1) e.2)), hgw]
    · rw [hfh]
      change blockX _ _ _ ((winBlock K S p H hX hO).hc j) =
        g (blockX _ _ _ ((markBlock (B ++ t) H hX hO).hc j))
      rw [blockX_hc, blockX_hc]
      exact (hgh _).symm

/-- **The marked word grid is related to the marked window grid by grid moves.** -/
theorem markedGrid_movesTo_winGrid :
    (markedGrid (B ++ t) (skappa K S (B ++ t)) hB.len_pos p H hX hO).toGrid.MovesTo
      (winGrid S hB hS p H hX hO).toGrid := by
  rw [toGrid_winGrid]
  exact markedGrid_movesTo_end _ _ _ _ _ _ _

end Window

end OnLeConjecture.KnotTheory.MarkedCancel
