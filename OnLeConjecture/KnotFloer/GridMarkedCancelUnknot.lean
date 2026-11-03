/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupBlocks
public import OnLeConjecture.KnotFloer.GridMarkedCancelSeam
public import OnLeConjecture.KnotTheory.MarkedCancelSlide

/-!
# Absorbing a split unknot into the protected grid

A *split unknot* added to a labeled grid `L` (`addUnknot`) consists of two new columns `a, b` in
front of the columns of `L` and two new rows `x, y` before the rows of `L`, with the `O` markings
at `(a, x)` and `(b, y)` and the `X` markings at `(a, y)` and `(b, x)`.

For a marked word grid with the protected grid `H` (triply prepared) and the block at the end,
the grid with a split unknot added is related by grid moves to the marked word grid with the
protected grid `blockInsert H k k`, a frame tower over `H` with one block
(`addUnknot_movesTo_marked`). The columns are rotated cyclically, the last block column is moved
past the two new columns, and the two new rows are moved into the block rows. This is the step of
the written proof of Statement E (`statement_E_complete_proof.tex`, Section 8) in which the strand
of an inverse pair that is not used by the rest of the word becomes one of the four-mark blocks
of the frame tower.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid LabeledGrid OnLeConjecture.KnotFloer.GridFull
  BraidWindow

/-! ### A split unknot -/

section Unknot

variable {n : ℕ} {C R : Type*} [DecidableEq C]

/-- The `O` row of a column after a split unknot is added. -/
def unkO (L : LabeledGrid n C R) (a b : C) (x y : R) (c : C) : R :=
  if c = a then x else if c = b then y else L.O c

/-- The `X` row of a column after a split unknot is added. -/
def unkX (L : LabeledGrid n C R) (a b : C) (x y : R) (c : C) : R :=
  if c = a then y else if c = b then x else L.X c

section Values

variable (L : LabeledGrid n C R) {a b : C} (x y : R)

theorem unkO_a : unkO L a b x y a = x := by simp [unkO]

theorem unkX_a : unkX L a b x y a = y := by simp [unkX]

theorem unkO_b (hab : a ≠ b) : unkO L a b x y b = y := by simp [unkO, Ne.symm hab]

theorem unkX_b (hab : a ≠ b) : unkX L a b x y b = x := by simp [unkX, Ne.symm hab]

theorem unkO_old {c : C} (ha : a ∉ L.cols) (hb : b ∉ L.cols) (hc : c ∈ L.cols) :
    unkO L a b x y c = L.O c := by
  have h1 : c ≠ a := fun e => ha (e ▸ hc)
  have h2 : c ≠ b := fun e => hb (e ▸ hc)
  simp [unkO, h1, h2]

theorem unkX_old {c : C} (ha : a ∉ L.cols) (hb : b ∉ L.cols) (hc : c ∈ L.cols) :
    unkX L a b x y c = L.X c := by
  have h1 : c ≠ a := fun e => ha (e ▸ hc)
  have h2 : c ≠ b := fun e => hb (e ▸ hc)
  simp [unkX, h1, h2]

end Values

/-- **A split unknot added to a labeled grid**: the columns `a, b` and the rows `x, y` are put in
front, with `O` markings at `(a, x)`, `(b, y)` and `X` markings at `(a, y)`, `(b, x)`. -/
def addUnknot (L : LabeledGrid n C R) (a b : C) (x y : R) (hab : a ≠ b) (hxy : x ≠ y)
    (ha : a ∉ L.cols) (hb : b ∉ L.cols) (hx : x ∉ L.rows) (hy : y ∉ L.rows) :
    LabeledGrid (n + 2) C R where
  cols := a :: b :: L.cols
  rows := x :: y :: L.rows
  O := unkO L a b x y
  X := unkX L a b x y
  cols_length := by simp [L.cols_length]
  rows_length := by simp [L.rows_length]
  cols_nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hb, L.cols_nodup⟩⟩
    simp only [List.mem_cons, not_or]; exact ⟨hab, ha⟩
  rows_nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hy, L.rows_nodup⟩⟩
    simp only [List.mem_cons, not_or]; exact ⟨hxy, hx⟩
  O_mem c hc := by
    simp only [List.mem_cons] at hc ⊢
    rcases hc with rfl | rfl | hc
    · left; exact unkO_a L x y
    · right; left; exact unkO_b L x y hab
    · right; right; rw [unkO_old L x y ha hb hc]; exact L.O_mem c hc
  X_mem c hc := by
    simp only [List.mem_cons] at hc ⊢
    rcases hc with rfl | rfl | hc
    · right; left; exact unkX_a L x y
    · left; exact unkX_b L x y hab
    · right; right; rw [unkX_old L x y ha hb hc]; exact L.X_mem c hc
  O_inj c hc c' hc' h := by
    have hO : ∀ d ∈ L.cols, L.O d ≠ x ∧ L.O d ≠ y := fun d hd =>
      ⟨fun e => hx (e ▸ L.O_mem d hd), fun e => hy (e ▸ L.O_mem d hd)⟩
    simp only [List.mem_cons] at hc hc'
    rcases hc with rfl | rfl | hc <;> rcases hc' with rfl | rfl | hc'
    · rfl
    · rw [unkO_a, unkO_b L x y hab] at h; exact absurd h hxy
    · rw [unkO_a, unkO_old L x y ha hb hc'] at h; exact absurd h.symm (hO _ hc').1
    · rw [unkO_a, unkO_b L x y hab] at h; exact absurd h.symm hxy
    · rfl
    · rw [unkO_b L x y hab, unkO_old L x y ha hb hc'] at h; exact absurd h.symm (hO _ hc').2
    · rw [unkO_a, unkO_old L x y ha hb hc] at h; exact absurd h (hO _ hc).1
    · rw [unkO_b L x y hab, unkO_old L x y ha hb hc] at h; exact absurd h (hO _ hc).2
    · rw [unkO_old L x y ha hb hc, unkO_old L x y ha hb hc'] at h; exact L.O_inj _ hc _ hc' h
  X_inj c hc c' hc' h := by
    have hX : ∀ d ∈ L.cols, L.X d ≠ x ∧ L.X d ≠ y := fun d hd =>
      ⟨fun e => hx (e ▸ L.X_mem d hd), fun e => hy (e ▸ L.X_mem d hd)⟩
    simp only [List.mem_cons] at hc hc'
    rcases hc with rfl | rfl | hc <;> rcases hc' with rfl | rfl | hc'
    · rfl
    · rw [unkX_a, unkX_b L x y hab] at h; exact absurd h.symm hxy
    · rw [unkX_a, unkX_old L x y ha hb hc'] at h; exact absurd h.symm (hX _ hc').2
    · rw [unkX_a, unkX_b L x y hab] at h; exact absurd h hxy
    · rfl
    · rw [unkX_b L x y hab, unkX_old L x y ha hb hc'] at h; exact absurd h.symm (hX _ hc').1
    · rw [unkX_a, unkX_old L x y ha hb hc] at h; exact absurd h (hX _ hc).2
    · rw [unkX_b L x y hab, unkX_old L x y ha hb hc] at h; exact absurd h (hX _ hc).1
    · rw [unkX_old L x y ha hb hc, unkX_old L x y ha hb hc'] at h; exact L.X_inj _ hc _ hc' h
  O_ne_X c hc := by
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · rw [unkO_a, unkX_a]; exact hxy
    · rw [unkO_b L x y hab, unkX_b L x y hab]; exact Ne.symm hxy
    · rw [unkO_old L x y ha hb hc, unkX_old L x y ha hb hc]; exact L.O_ne_X c hc

end Unknot

/-! ### Positions in labeled grids -/

section Positions

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

omit [DecidableEq C] in
theorem rpos_of_rows_cons (G : LabeledGrid n C R) {x : R} {l : List R} (h : G.rows = x :: l) :
    G.rpos x = 0 := by
  simp only [LabeledGrid.rpos, h, List.idxOf_cons_self]

omit [DecidableEq C] in
theorem rpos_of_rows_cons_cons (G : LabeledGrid n C R) {x y : R} {l : List R} (hxy : x ≠ y)
    (h : G.rows = x :: y :: l) : G.rpos y = 1 := by
  simp only [LabeledGrid.rpos, h]
  rw [List.idxOf_cons_ne _ hxy, List.idxOf_cons_self]

omit [DecidableEq R] in
theorem cpos_of_cols_append (G : LabeledGrid n C R) {l rest : List C} {c : C}
    (h : G.cols = l ++ c :: rest) (hc : c ∉ l) : G.cpos c = l.length := by
  simp only [LabeledGrid.cpos, h]
  rw [List.idxOf_append_of_notMem hc, List.idxOf_cons_self]; simp

omit [DecidableEq R] in
theorem cpos_of_cols_append' (G : LabeledGrid n C R) {l rest : List C} {c d : C}
    (h : G.cols = l ++ c :: d :: rest) (hd : d ∉ l) (hcd : c ≠ d) : G.cpos d = l.length + 1 := by
  simp only [LabeledGrid.cpos, h]
  rw [List.idxOf_append_of_notMem hd, List.idxOf_cons_ne _ hcd, List.idxOf_cons_self]

end Positions

/-! ### The protected grid with one more block -/

section Tower

variable {k : ℕ} (H : GridDiagram (k + 1))

/-- The protected grid with one more block, at the frame position `(k, k)`. -/
abbrev unkH : GridDiagram (k + 2 + 1) := blockInsert H ⟨k, by omega⟩ ⟨k, by omega⟩

theorem unkH_tp (hH : TriplyPrepared H) : TriplyPrepared (unkH H) :=
  triplyPrepared_blockInsert hH (two_le_of_triplyPrepared hH) le_rfl
    (two_le_of_triplyPrepared hH) le_rfl

theorem unkH_tower (hH : TriplyPrepared H) : FrameTower H 1 (unkH H) :=
  FrameTower.base.insert k k (two_le_of_triplyPrepared hH) le_rfl
    (two_le_of_triplyPrepared hH) le_rfl

theorem unkH_O_val (j : Fin (k + 2 + 1)) :
    ((unkH H).O j).val = if j.val = k then k else if j.val = k + 1 then k + 1
      else blockShift k (gridRowVal H.O (blockBack k j.val)) := by
  rw [← gridRowVal_val, gridRowVal_blockInsert_O]
  simp only
  split_ifs <;> first | rfl | omega

theorem unkH_X_val (j : Fin (k + 2 + 1)) :
    ((unkH H).X j).val = if j.val = k then k + 1 else if j.val = k + 1 then k
      else blockShift k (gridRowVal H.X (blockBack k j.val)) := by
  rw [← gridRowVal_val, gridRowVal_blockInsert_X]
  simp only
  split_ifs <;> first | rfl | omega

end Tower

/-! ### The label maps of the absorption -/

/-- The column labels of the marked word grid with one more block, mapped to the columns of the
grid with a split unknot: the two new block columns go to `a` and `b`. -/
def absC (N k a b : ℕ) : BCol → BCol
  | Sum.inl z => Sum.inl z
  | Sum.inr q => if q.1 < N + k then Sum.inr q else if q.1 = N + k then Sum.inl a
      else if q.1 = N + k + 1 then Sum.inl b else Sum.inr (q.1 - 2, q.2)

/-- The row labels of the marked word grid with one more block, mapped to the rows of the grid
with a split unknot: the two new block rows go to `x` and `y`. -/
def absR (N k x y : ℕ) : BRow → BRow
  | Sum.inl z => Sum.inl z
  | Sum.inr q => if q.1 < N + k then Sum.inr q else if q.1 = N + k then Sum.inl x
      else if q.1 = N + k + 1 then Sum.inl y else Sum.inr (q.1 - 2, q.2)

theorem absC_inj (N k a b : ℕ) (hab : a ≠ b) (c₀ : Fin 3) {q q' : ℕ × Fin 3}
    (hq : N + k ≤ q.1 → q.2 = c₀) (hq' : N + k ≤ q'.1 → q'.2 = c₀)
    (h : absC N k a b (Sum.inr q) = absC N k a b (Sum.inr q')) : q = q' := by
  obtain ⟨h₁, c₁⟩ := q
  obtain ⟨h₂, c₂⟩ := q'
  simp only at hq hq'
  simp only [absC] at h
  split_ifs at h <;> simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
  all_goals first
    | exact Prod.ext h.1 h.2
    | (exfalso; omega)
    | exact absurd h hab
    | exact absurd h.symm hab
    | (rw [hq (by omega), hq' (by omega)]; congr 1; omega)

theorem absR_inj (N k x y : ℕ) (hxy : x ≠ y) (c₀ : Fin 3) {q q' : ℕ × Fin 3}
    (hq : N + k ≤ q.1 → q.2 = c₀) (hq' : N + k ≤ q'.1 → q'.2 = c₀)
    (h : absR N k x y (Sum.inr q) = absR N k x y (Sum.inr q')) : q = q' := by
  obtain ⟨h₁, c₁⟩ := q
  obtain ⟨h₂, c₂⟩ := q'
  simp only at hq hq'
  simp only [absR] at h
  split_ifs at h <;> simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
  all_goals first
    | exact Prod.ext h.1 h.2
    | (exfalso; omega)
    | exact absurd h hxy
    | exact absurd h.symm hxy
    | (rw [hq (by omega), hq' (by omega)]; congr 1; omega)

theorem absR_low (N k x y : ℕ) {h : ℕ} (c : Fin 3) (hh : h < N + k) :
    absR N k x y (Sum.inr (h, c)) = Sum.inr (h, c) := by
  simp [absR, hh]

theorem absC_low (N k a b : ℕ) {h : ℕ} (c : Fin 3) (hh : h < N + k) :
    absC N k a b (Sum.inr (h, c)) = Sum.inr (h, c) := by
  simp [absC, hh]

/-- A shifted block row goes back to the old block row. -/
theorem absR_shift (N k x y v : ℕ) :
    absR N k x y (Sum.inr (N + blockShift k v, 1)) = Sum.inr (N + v, 1) := by
  unfold blockShift
  split_ifs with hv
  · exact absR_low N k x y 1 (by omega)
  · simp only [absR]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 2

/-! ### Rows and columns of the protected block -/

section StdBlock

variable {k : ℕ} (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0) (N₀ : ℕ)

theorem stdBlock_oRow (j : Fin (k + 1)) :
    (stdBlock H hX hO N₀).oRow j =
      if H.O j = 0 then Sum.inr (N₀ + (k + 1), 1) else Sum.inr (N₀ + (H.O j).val, 1) := by
  unfold ProtBlock.oRow
  rfl

theorem stdBlock_xRow (j : Fin (k + 1)) :
    (stdBlock H hX hO N₀).xRow j = Sum.inr (N₀ + (H.X j).val, 1) := rfl

end StdBlock

/-! ### The marked word grid with the block at the end -/

section EndGrid

variable {m k : ℕ} (t : SignedAdjacentWord m) (κ : Fin t.length × Fin 3 → ℕ) (ht : 0 < t.length)
  (p' : Fin t.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
  (hO : H.O (Fin.last k) = 0)

/-- The marked word grid with the block after all columns. -/
abbrev endGrid : LabeledGrid (t.length * 3 + k + 1) BCol BRow :=
  insertBlock (plainGrid t κ ht) (markRow t p') (markBlock t H hX hO) (endData t κ ht p' H hX hO)

theorem endGrid_cols :
    (endGrid t κ ht p' H hX hO).cols = (plainGrid t κ ht).cols ++ (markBlock t H hX hO).cols := by
  rw [insertBlock_cols]; simp [endData]

theorem endGrid_rows : (endGrid t κ ht p' H hX hO).rows =
    (markData t κ ht p' H hX hO).m₁ ++ (markBlock t H hX hO).rows ++
      (markData t κ ht p' H hX hO).m₂ := rfl

theorem mem_plain_of_m₁ {z : BRow} (hz : z ∈ (markData t κ ht p' H hX hO).m₁) :
    z ∈ (plainGrid t κ ht).rows := by
  rw [(markData t κ ht p' H hX hO).rows_eq]; simp [hz]

theorem mem_plain_of_m₂ {z : BRow} (hz : z ∈ (markData t κ ht p' H hX hO).m₂) :
    z ∈ (plainGrid t κ ht).rows := by
  rw [(markData t κ ht p' H hX hO).rows_eq]; simp [hz]

theorem endGrid_cols_inr {c : BCol} (hc : c ∈ (endGrid t κ ht p' H hX hO).cols) :
    ∃ q, c = Sum.inr q := by
  rw [endGrid_cols, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨q, rfl⟩ := mem_plainGrid_cols.mp hc; exact ⟨_, rfl⟩
  · obtain ⟨j, rfl⟩ := (markBlock t H hX hO).mem_cols.mp hc; exact ⟨_, rfl⟩

theorem endGrid_rows_inr {z : BRow} (hz : z ∈ (endGrid t κ ht p' H hX hO).rows) :
    ∃ q, z = Sum.inr q := by
  rw [endGrid_rows] at hz
  simp only [List.mem_append] at hz
  rcases hz with (hz | hz) | hz
  · obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp (mem_plain_of_m₁ t κ ht p' H hX hO hz)
    exact ⟨_, rfl⟩
  · obtain ⟨i, rfl⟩ := (markBlock t H hX hO).mem_rows.mp hz; exact ⟨_, rfl⟩
  · obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp (mem_plain_of_m₂ t κ ht p' H hX hO hz)
    exact ⟨_, rfl⟩

theorem inl_not_mem_endGrid_cols (z : ℕ) : Sum.inl z ∉ (endGrid t κ ht p' H hX hO).cols :=
  fun h => by obtain ⟨q, hq⟩ := endGrid_cols_inr t κ ht p' H hX hO h; simp at hq

theorem inl_not_mem_endGrid_rows (z : ℕ) : Sum.inl z ∉ (endGrid t κ ht p' H hX hO).rows :=
  fun h => by obtain ⟨q, hq⟩ := endGrid_rows_inr t κ ht p' H hX hO h; simp at hq

theorem endGrid_cols_cases {c : BCol} (hc : c ∈ (endGrid t κ ht p' H hX hO).cols) :
    (∃ q : Fin t.length × Fin 3, c = Sum.inr (q.1.val, q.2)) ∨
      ∃ j : Fin (k + 1), c = Sum.inr (t.length + j.val, 0) := by
  rw [endGrid_cols, List.mem_append] at hc
  rcases hc with hc | hc
  · exact Or.inl (mem_plainGrid_cols.mp hc)
  · obtain ⟨j, rfl⟩ := (markBlock t H hX hO).mem_cols.mp hc; exact Or.inr ⟨j, rfl⟩

theorem endGrid_rows_cases {z : BRow} (hz : z ∈ (endGrid t κ ht p' H hX hO).rows) :
    (∃ q : Fin t.length × Fin 3, z = Sum.inr (q.1.val, q.2)) ∨
      ∃ i : Fin (k + 2), z = Sum.inr (t.length + i.val, 1) := by
  rw [endGrid_rows] at hz
  simp only [List.mem_append] at hz
  rcases hz with (hz | hz) | hz
  · exact Or.inl (mem_plainGrid_rows.mp (mem_plain_of_m₁ t κ ht p' H hX hO hz))
  · obtain ⟨i, rfl⟩ := (markBlock t H hX hO).mem_rows.mp hz; exact Or.inr ⟨i, rfl⟩
  · exact Or.inl (mem_plainGrid_rows.mp (mem_plain_of_m₂ t κ ht p' H hX hO hz))

end EndGrid

theorem ofFn_split_one {β : Type*} {k : ℕ} (f : Fin (k + 1) → β) :
    List.ofFn f = List.ofFn (fun j : Fin k => f ⟨j.val, by omega⟩) ++ [f ⟨k, by omega⟩] := by
  rw [ofFn_succ_last]; rfl

theorem ofFn_split_two {β : Type*} {k : ℕ} (f : Fin (k + 2) → β) :
    List.ofFn f = List.ofFn (fun j : Fin k => f ⟨j.val, by omega⟩) ++
      [f ⟨k, by omega⟩, f ⟨k + 1, by omega⟩] := by
  rw [ofFn_succ_last, ofFn_succ_last, List.append_assoc]; rfl

theorem ofFn_split_three {β : Type*} {k : ℕ} (f : Fin (k + 2 + 1) → β) :
    List.ofFn f = List.ofFn (fun j : Fin k => f ⟨j.val, by omega⟩) ++
      [f ⟨k, by omega⟩, f ⟨k + 1, by omega⟩, f ⟨k + 2, by omega⟩] := by
  rw [ofFn_succ_last, ofFn_split_two, List.append_assoc]; rfl

theorem ofFn_split_four {β : Type*} {k : ℕ} (f : Fin (k + 2 + 2) → β) :
    List.ofFn f = List.ofFn (fun j : Fin k => f ⟨j.val, by omega⟩) ++
      [f ⟨k, by omega⟩, f ⟨k + 1, by omega⟩, f ⟨k + 2, by omega⟩, f ⟨k + 3, by omega⟩] := by
  rw [ofFn_succ_last, ofFn_split_three, List.append_assoc]; rfl

/-! ### Absorption of the split unknot -/

section Absorb

variable {m k : ℕ} (t : SignedAdjacentWord m) (κ : Fin t.length × Fin 3 → ℕ) (ht : 0 < t.length)
  (p' : Fin t.length × Fin 3) (H : GridDiagram (k + 1)) (hH : TriplyPrepared H)

/-- The marked word grid with the block at the end and a split unknot with the column labels
`a, b` and the row labels `x, y`. -/
abbrev unkGrid (a b x y : ℕ) (hab : a ≠ b) (hxy : x ≠ y) :
    LabeledGrid (t.length * 3 + k + 1 + 2) BCol BRow :=
  addUnknot (endGrid t κ ht p' H hH.1 hH.2.1) (Sum.inl a) (Sum.inl b) (Sum.inl x) (Sum.inl y)
    (by simpa using hab) (by simpa using hxy) (inl_not_mem_endGrid_cols t κ ht p' H _ _ a)
    (inl_not_mem_endGrid_cols t κ ht p' H _ _ b) (inl_not_mem_endGrid_rows t κ ht p' H _ _ x)
    (inl_not_mem_endGrid_rows t κ ht p' H _ _ y)

/-- **Absorption of a split unknot.** A marked word grid with the block at the end and a split
unknot added is related by grid moves to the marked word grid with the protected grid
`blockInsert H k k`. -/
theorem unkGrid_movesTo_marked (a b x y : ℕ) (hab : a ≠ b) (hxy : x ≠ y) :
    (unkGrid t κ ht p' H hH a b x y hab hxy).toGrid.MovesTo
      (markedGrid t κ ht p' (unkH H) (unkH_tp H hH).1 (unkH_tp H hH).2.1).toGrid := by
  have hk := two_le_of_triplyPrepared hH
  set L := endGrid t κ ht p' H hH.1 hH.2.1 with hLdef
  set U := unkGrid t κ ht p' H hH a b x y hab hxy with hUdef
  set P := markBlock t H hH.1 hH.2.1 with hPdef
  set D := markData t κ ht p' H hH.1 hH.2.1 with hDdef
  set plainC := (plainGrid t κ ht).cols with hplainC
  have hLc : L.cols = plainC ++ P.cols := endGrid_cols t κ ht p' H _ _
  have hPc : P.cols = List.ofFn (fun j : Fin k => P.hc ⟨j.val, by omega⟩) ++
      [P.hc ⟨k, by omega⟩] := ofFn_split_one P.hc
  have hPr : P.rows = List.ofFn (fun j : Fin k => P.hr ⟨j.val, by omega⟩) ++
      [P.hr ⟨k, by omega⟩, P.hr ⟨k + 1, by omega⟩] := ofFn_split_two P.hr
  have hLr : L.rows = D.m₁ ++ P.rows ++ D.m₂ := rfl
  have hUr : U.rows = Sum.inl x :: Sum.inl y :: L.rows := rfl
  have hUO : ∀ c, U.O c = unkO L (Sum.inl a) (Sum.inl b) (Sum.inl x) (Sum.inl y) c :=
    fun _ => rfl
  have hUX : ∀ c, U.X c = unkX L (Sum.inl a) (Sum.inl b) (Sum.inl x) (Sum.inl y) c :=
    fun _ => rfl
  have hna : Sum.inl a ∉ L.cols := inl_not_mem_endGrid_cols t κ ht p' H _ _ a
  have hnb : Sum.inl b ∉ L.cols := inl_not_mem_endGrid_cols t κ ht p' H _ _ b
  have hab' : (Sum.inl a : BCol) ≠ Sum.inl b := by simpa using hab
  have hUOa : U.O (Sum.inl a) = Sum.inl x := unkO_a L _ _
  have hUXa : U.X (Sum.inl a) = Sum.inl y := unkX_a L _ _
  have hUOb : U.O (Sum.inl b) = Sum.inl y := unkO_b L _ _ hab'
  have hUXb : U.X (Sum.inl b) = Sum.inl x := unkX_b L _ _ hab'
  have hUOold : ∀ c ∈ L.cols, U.O c = L.O c := fun c hc => unkO_old L _ _ hna hnb hc
  have hUXold : ∀ c ∈ L.cols, U.X c = L.X c := fun c hc => unkX_old L _ _ hna hnb hc
  have hLinr : ∀ z ∈ L.rows, ∀ w : ℕ, z ≠ Sum.inl w := fun z hz w e => by
    obtain ⟨q, rfl⟩ := endGrid_rows_inr t κ ht p' H _ _ hz; simp at e
  have hLcinr : ∀ c ∈ L.cols, ∀ w : ℕ, c ≠ Sum.inl w := fun c hc w e => by
    obtain ⟨q, rfl⟩ := endGrid_cols_inr t κ ht p' H _ _ hc; simp at e
  have hPcL : ∀ j, P.hc j ∈ L.cols := fun j => by
    rw [hLc]; exact List.mem_append_right _ (P.hc_mem j)
  -- the columns are rotated
  obtain ⟨U₁, hU₁c, hU₁r, hU₁O, hU₁X, m1⟩ : ∃ U₁ : LabeledGrid (t.length * 3 + k + 1 + 2) BCol BRow,
      U₁.cols = L.cols ++ [Sum.inl a, Sum.inl b] ∧ U₁.rows = U.rows ∧ U₁.O = U.O ∧ U₁.X = U.X ∧
        U.toGrid.MovesTo U₁.toGrid :=
    ⟨U.withCols (L.cols ++ [Sum.inl a, Sum.inl b]) (List.perm_append_comm (l₁ := L.cols)),
      rfl, rfl, rfl, rfl, movesTo_withCols_rotate U (l₁ := [Sum.inl a, Sum.inl b]) rfl⟩
  have hrx : U₁.rpos (Sum.inl x) = 0 := rpos_of_rows_cons U₁ (hU₁r.trans hUr)
  have hry : U₁.rpos (Sum.inl y) = 1 :=
    rpos_of_rows_cons_cons U₁ (by simpa using hxy) (hU₁r.trans hUr)
  -- the last block column passes the two new columns
  have hU₁c' : U₁.cols = (plainC ++ List.ofFn (fun j : Fin k => P.hc ⟨j.val, by omega⟩)) ++
      P.hc ⟨k, by omega⟩ :: ([Sum.inl a, Sum.inl b] ++ []) := by
    rw [hU₁c, hLc, hPc]; simp
  obtain ⟨U₂, hU₂c, hU₂r, hU₂O, hU₂X, m2⟩ := U₁.exists_moveColRight hU₁c' (fun d hd => by
    rw [U₁.colsNonint_comm]
    have hlast := hPcL ⟨k, by omega⟩
    have hmemd : d ∈ U₁.cols := by rw [hU₁c]; exact List.mem_append_right _ (by simpa using hd)
    have hmeml : P.hc ⟨k, by omega⟩ ∈ U₁.cols := by rw [hU₁c]; exact List.mem_append_left _ hlast
    have hOl : U₁.O (P.hc ⟨k, by omega⟩) = L.O (P.hc ⟨k, by omega⟩) := by
      rw [hU₁O]; exact hUOold _ hlast
    have hXl : U₁.X (P.hc ⟨k, by omega⟩) = L.X (P.hc ⟨k, by omega⟩) := by
      rw [hU₁X]; exact hUXold _ hlast
    have hOm := hLinr _ (L.O_mem _ hlast)
    have hXm := hLinr _ (L.X_mem _ hlast)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl
    · refine U₁.colsNonint_of_short hmemd hmeml ?_ ?_ ?_ ?_ ?_
      · left; rw [hU₁O, hU₁X, hUOa, hUXa, hrx, hry]
      all_goals simp only [hOl, hXl, hU₁O, hU₁X, hUOa, hUXa]
      exacts [hOm _, hOm _, hXm _, hXm _]
    · refine U₁.colsNonint_of_short hmemd hmeml ?_ ?_ ?_ ?_ ?_
      · right; rw [hU₁O, hU₁X, hUOb, hUXb, hrx, hry]
      all_goals simp only [hOl, hXl, hU₁O, hU₁X, hUOb, hUXb]
      exacts [hOm _, hOm _, hXm _, hXm _])
  -- the two new rows pass the rows below the last two block rows
  set l₀ := plainC ++ List.ofFn (fun j : Fin k => P.hc ⟨j.val, by omega⟩) with hl₀
  have hU₂c' : U₂.cols = l₀ ++ Sum.inl a :: Sum.inl b :: [P.hc ⟨k, by omega⟩] := by
    rw [hU₂c]; simp
  have hl₀L : ∀ c ∈ l₀, c ∈ L.cols := fun c hc => by
    rw [hLc, hPc]; rw [hl₀] at hc; simp only [List.mem_append] at hc ⊢; tauto
  have hal₀ : Sum.inl a ∉ l₀ := fun h => hLcinr _ (hl₀L _ h) a rfl
  have hbl₀ : Sum.inl b ∉ l₀ := fun h => hLcinr _ (hl₀L _ h) b rfl
  have hca : U₂.cpos (Sum.inl a) = l₀.length := cpos_of_cols_append U₂ hU₂c' hal₀
  have hcb : U₂.cpos (Sum.inl b) = l₀.length + 1 := cpos_of_cols_append' U₂ hU₂c' hbl₀ hab'
  have hU₂rows : U₂.rows = [] ++ [Sum.inl x, Sum.inl y] ++
      (D.m₁ ++ List.ofFn (fun j : Fin k => P.hr ⟨j.val, by omega⟩)) ++
      ([P.hr ⟨k, by omega⟩, P.hr ⟨k + 1, by omega⟩] ++ D.m₂) := by
    rw [hU₂r, hU₁r, hUr, hLr, hPr]; simp
  have hamem : Sum.inl a ∈ U₂.cols := by rw [hU₂c']; simp
  have hbmem : Sum.inl b ∈ U₂.cols := by rw [hU₂c']; simp
  obtain ⟨U₃, hU₃c, hU₃r, hU₃O, hU₃X, m3⟩ := exists_moveRowsPast U₂ hU₂rows (by
    intro z₁ hz₁ z hz
    have hzL : z ∈ L.rows := by
      rw [hLr, hPr]; simp only [List.mem_append] at hz ⊢; tauto
    have hzx := hLinr z hzL x
    have hzy := hLinr z hzL y
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz₁
    rcases hz₁ with rfl | rfl
    · refine U₂.rowsNonint_of_short hamem hbmem (by rw [hU₂O, hU₁O, hUOa])
        (by rw [hU₂X, hU₁X, hUXb]) (Or.inl (by rw [hca, hcb])) hzx ?_ ?_
      · rw [hU₂O, hU₁O, hUOb]; exact hzy
      · rw [hU₂X, hU₁X, hUXa]; exact hzy
    · refine U₂.rowsNonint_of_short hbmem hamem (by rw [hU₂O, hU₁O, hUOb])
        (by rw [hU₂X, hU₁X, hUXa]) (Or.inr (by rw [hca, hcb])) hzy ?_ ?_
      · rw [hU₂O, hU₁O, hUOa]; exact hzx
      · rw [hU₂X, hU₁X, hUXb]; exact hzx)
  -- recognition as the marked word grid with one more block
  have hH' := unkH_tp H hH
  set H' := unkH H with hH'def
  set L' := endGrid t κ ht p' H' hH'.1 hH'.2.1 with hL'def
  set P' := markBlock t H' hH'.1 hH'.2.1 with hP'def
  set fC := absC t.length k a b with hfC
  set fR := absR t.length k x y with hfR
  have hU₃O' : ∀ c, U₃.O c = U.O c := fun c => by rw [hU₃O, hU₂O, hU₁O]
  have hU₃X' : ∀ c, U₃.X c = U.X c := fun c => by rw [hU₃X, hU₂X, hU₁X]
  have hfRlast : fR (Sum.inr (t.length + (k + 2 + 1), 1)) = Sum.inr (t.length + (k + 1), 1) := by
    simp only [hfR, absR]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 2
  have hfRk : fR (Sum.inr (t.length + k, 1)) = Sum.inl x := by
    simp [hfR, absR]
  have hfRk1 : fR (Sum.inr (t.length + (k + 1), 1)) = Sum.inl y := by
    simp only [hfR, absR]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have hfRk2 : fR (Sum.inr (t.length + (k + 2), 1)) = Sum.inr (t.length + k, 1) := by
    simp only [hfR, absR]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 2
  have hfRk3 : fR (Sum.inr (t.length + (k + 3), 1)) = Sum.inr (t.length + (k + 1), 1) := by
    simp only [hfR, absR]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 2
  have hfCk : fC (Sum.inr (t.length + k, 0)) = Sum.inl a := by
    simp [hfC, absC]
  have hfCk1 : fC (Sum.inr (t.length + (k + 1), 0)) = Sum.inl b := by
    simp only [hfC, absC]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have hfCk2 : fC (Sum.inr (t.length + (k + 2), 0)) = Sum.inr (t.length + k, 0) := by
    simp only [hfC, absC]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 2
  have hplainR : ∀ z ∈ (plainGrid t κ ht).rows, fR z = z := by
    intro z hz
    obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hz
    exact absR_low _ _ _ _ _ (by have := q.1.isLt; omega)
  have hplainC' : ∀ c ∈ (plainGrid t κ ht).cols, fC c = c := by
    intro c hc
    obtain ⟨q, rfl⟩ := mem_plainGrid_cols.mp hc
    exact absC_low _ _ _ _ _ (by have := q.1.isLt; omega)
  have hfClow : ∀ (h : ℕ) (c : Fin 3), h < t.length + k → fC (Sum.inr (h, c)) = Sum.inr (h, c) :=
    fun _ c hh => absC_low _ _ _ _ c hh
  have hfRshift : ∀ v : ℕ, fR (Sum.inr (t.length + blockShift k v, 1)) =
      Sum.inr (t.length + v, 1) := fun v => absR_shift _ _ _ _ v
  have hrec : U₃.toGrid = L'.toGrid := by
    apply toGrid_eq_of_image L' U₃ fC fR
    · intro c hc c' hc' h
      have key : ∀ c ∈ L'.cols, ∃ q : ℕ × Fin 3,
          c = Sum.inr q ∧ (t.length + k ≤ q.1 → q.2 = 0) := by
        intro c hc
        rcases endGrid_cols_cases t κ ht p' H' _ _ hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
        · exact ⟨_, rfl, fun h => by simp only at h; have := q.1.isLt; exfalso; omega⟩
        · exact ⟨_, rfl, fun _ => rfl⟩
      obtain ⟨q, rfl, hq⟩ := key c hc
      obtain ⟨q', rfl, hq'⟩ := key c' hc'
      rw [absC_inj t.length k a b hab 0 hq hq' h]
    · intro z hz z' hz' h
      have key : ∀ z ∈ L'.rows, ∃ q : ℕ × Fin 3,
          z = Sum.inr q ∧ (t.length + k ≤ q.1 → q.2 = 1) := by
        intro z hz
        rcases endGrid_rows_cases t κ ht p' H' _ _ hz with ⟨q, rfl⟩ | ⟨i, rfl⟩
        · exact ⟨_, rfl, fun h => by simp only at h; have := q.1.isLt; exfalso; omega⟩
        · exact ⟨_, rfl, fun _ => rfl⟩
      obtain ⟨q, rfl, hq⟩ := key z hz
      obtain ⟨q', rfl, hq'⟩ := key z' hz'
      rw [absR_inj t.length k x y hxy 1 hq hq' h]
    · have e1 : (plainGrid t κ ht).cols.map fC = plainC := by
        conv_rhs => rw [← List.map_id plainC]
        exact List.map_congr_left hplainC'
      have e2 : P'.cols.map fC = List.ofFn (fun j : Fin k => P.hc ⟨j.val, by omega⟩) ++
          [Sum.inl a, Sum.inl b, P.hc ⟨k, by omega⟩] := by
        change (List.ofFn P'.hc).map fC = _
        rw [List.map_ofFn, ofFn_split_three]
        congr 1
        · congr 1; funext j
          have := j.isLt
          change absC t.length k a b (Sum.inr (t.length + j.val, 0)) = Sum.inr (t.length + j.val, 0)
          exact absC_low _ _ _ _ _ (by omega)
        · change [fC (Sum.inr (t.length + k, 0)), fC (Sum.inr (t.length + (k + 1), 0)),
            fC (Sum.inr (t.length + (k + 2), 0))] = _
          rw [hfCk, hfCk1, hfCk2]; rfl
      rw [hU₃c, hU₂c', endGrid_cols, List.map_append, e1, e2, hl₀]; simp
    · have e1 : (markData t κ ht p' H' hH'.1 hH'.2.1).m₁.map fR = D.m₁ := by
        conv_rhs => rw [← List.map_id D.m₁]
        exact List.map_congr_left fun z hz =>
          hplainR z (mem_plain_of_m₁ t κ ht p' H hH.1 hH.2.1 hz)
      have e3 : (markData t κ ht p' H' hH'.1 hH'.2.1).m₂.map fR = D.m₂ := by
        conv_rhs => rw [← List.map_id D.m₂]
        exact List.map_congr_left fun z hz =>
          hplainR z (mem_plain_of_m₂ t κ ht p' H hH.1 hH.2.1 hz)
      have e2 : P'.rows.map fR = List.ofFn (fun j : Fin k => P.hr ⟨j.val, by omega⟩) ++
          [Sum.inl x, Sum.inl y, P.hr ⟨k, by omega⟩, P.hr ⟨k + 1, by omega⟩] := by
        change (List.ofFn P'.hr).map fR = _
        rw [List.map_ofFn, ofFn_split_four]
        congr 1
        · congr 1; funext j
          have := j.isLt
          change absR t.length k x y (Sum.inr (t.length + j.val, 1)) = Sum.inr (t.length + j.val, 1)
          exact absR_low _ _ _ _ _ (by omega)
        · change [fR (Sum.inr (t.length + k, 1)), fR (Sum.inr (t.length + (k + 1), 1)),
            fR (Sum.inr (t.length + (k + 2), 1)), fR (Sum.inr (t.length + (k + 3), 1))] = _
          rw [hfRk, hfRk1, hfRk2, hfRk3]; rfl
      rw [hU₃r, endGrid_rows, List.map_append, List.map_append, e1, e2, e3]; simp
    · intro c hc
      rcases endGrid_cols_cases t κ ht p' H' _ _ hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · have hcp : (Sum.inr (q.1.val, q.2) : BCol) ∈ (plainGrid t κ ht).cols :=
          mem_plainGrid_cols.mpr ⟨q, rfl⟩
        have hcL : (Sum.inr (q.1.val, q.2) : BCol) ∈ L.cols := by
          rw [hLc]; exact List.mem_append_left _ hcp
        rw [hplainC' _ hcp, hU₃O', hUOold _ hcL]
        change blockO _ _ _ _ = fR (blockO _ _ _ _)
        rw [(endData t κ ht p' H hH.1 hH.2.1).blockO_old hcp,
          (endData t κ ht p' H' hH'.1 hH'.2.1).blockO_old hcp]
        split_ifs
        · rw [stdBlock_hr, stdBlock_hr, Fin.val_zero, Fin.val_zero]
          exact (absR_low _ _ _ _ _ (by omega)).symm
        · exact (hplainR _ ((plainGrid t κ ht).O_mem _ hcp)).symm
      · have hj := j.isLt
        have hcj : (Sum.inr (t.length + j.val, 0) : BCol) = P'.hc j := rfl
        rw [hcj]
        change _ = fR (blockO _ _ _ (P'.hc j))
        rw [blockO_hc, stdBlock_oRow, hU₃O']
        have hOv := unkH_O_val H j
        by_cases h1 : j.val < k
        · rw [if_neg (by omega), if_neg (by omega), blockBack, if_pos h1,
            gridRowVal_mk _ _ (by omega)] at hOv
          rw [← hcj, hfClow _ _ (by omega),
            show (Sum.inr (t.length + j.val, 0) : BCol) = P.hc ⟨j.val, by omega⟩ from rfl,
            hUOold _ (hPcL _)]
          change blockO _ _ _ (P.hc _) = _
          rw [blockO_hc, stdBlock_oRow]
          by_cases h0 : H.O ⟨j.val, by omega⟩ = 0
          · have hv : (H'.O j).val = 0 := by
              rw [hOv, h0, show ((0 : Fin (k + 1)) : ℕ) = 0 from rfl]; unfold blockShift
              rw [if_pos (show 0 < k by omega)]
            have h0' : H'.O j = 0 := by rw [Fin.ext_iff, hv]; rfl
            rw [if_pos h0, if_pos h0', hfRlast]
          · have h0' : H'.O j ≠ 0 := fun e => h0 (Fin.ext (by
              have := congrArg Fin.val e
              rw [hOv, show ((0 : Fin (k + 2 + 1)) : ℕ) = 0 from rfl] at this
              rw [show ((0 : Fin (k + 1)) : ℕ) = 0 from rfl]
              unfold blockShift at this
              split_ifs at this; omega))
            rw [if_neg h0, if_neg h0', hOv, hfRshift]
        by_cases h2 : j.val = k
        · rw [if_pos h2] at hOv
          have h0' : H'.O j ≠ 0 := fun e => by
            have := congrArg Fin.val e; rw [hOv] at this; simp at this; omega
          rw [← hcj, h2, hfCk, hUOa, if_neg h0', hOv, hfRk]
        by_cases h3 : j.val = k + 1
        · rw [if_neg h2, if_pos h3] at hOv
          have h0' : H'.O j ≠ 0 := fun e => by
            have := congrArg Fin.val e; rw [hOv] at this; simp at this
          rw [← hcj, h3, hfCk1, hUOb, if_neg h0', hOv, hfRk1]
        have h4 : j.val = k + 2 := by omega
        rw [if_neg h2, if_neg h3, blockBack, if_neg (by omega),
          show j.val - 2 = k by omega, gridRowVal_mk _ _ (by omega)] at hOv
        have hOk : H.O ⟨k, by omega⟩ = 0 := hH.2.1
        have hv : (H'.O j).val = 0 := by
          rw [hOv, hOk, show ((0 : Fin (k + 1)) : ℕ) = 0 from rfl]; unfold blockShift
          rw [if_pos (show 0 < k by omega)]
        have h0' : H'.O j = 0 := by rw [Fin.ext_iff, hv]; rfl
        rw [← hcj, h4, hfCk2,
          show (Sum.inr (t.length + k, 0) : BCol) = P.hc ⟨k, by omega⟩ from rfl,
          hUOold _ (hPcL _)]
        change blockO _ _ _ (P.hc _) = _
        rw [blockO_hc, stdBlock_oRow, if_pos hOk, if_pos h0', hfRlast]
    · intro c hc
      rcases endGrid_cols_cases t κ ht p' H' _ _ hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · have hcp : (Sum.inr (q.1.val, q.2) : BCol) ∈ (plainGrid t κ ht).cols :=
          mem_plainGrid_cols.mpr ⟨q, rfl⟩
        have hcL : (Sum.inr (q.1.val, q.2) : BCol) ∈ L.cols := by
          rw [hLc]; exact List.mem_append_left _ hcp
        rw [hplainC' _ hcp, hU₃X', hUXold _ hcL]
        change blockX _ _ _ _ = fR (blockX _ _ _ _)
        rw [(endData t κ ht p' H hH.1 hH.2.1).blockX_old hcp,
          (endData t κ ht p' H' hH'.1 hH'.2.1).blockX_old hcp]
        split_ifs
        · exact hfRlast.symm
        · exact (hplainR _ ((plainGrid t κ ht).X_mem _ hcp)).symm
      · have hj := j.isLt
        have hcj : (Sum.inr (t.length + j.val, 0) : BCol) = P'.hc j := rfl
        rw [hcj]
        change _ = fR (blockX _ _ _ (P'.hc j))
        rw [blockX_hc, stdBlock_xRow, hU₃X']
        have hXv := unkH_X_val H j
        by_cases h1 : j.val < k
        · rw [if_neg (by omega), if_neg (by omega), blockBack, if_pos h1,
            gridRowVal_mk _ _ (by omega)] at hXv
          rw [← hcj, hfClow _ _ (by omega),
            show (Sum.inr (t.length + j.val, 0) : BCol) = P.hc ⟨j.val, by omega⟩ from rfl,
            hUXold _ (hPcL _)]
          change blockX _ _ _ (P.hc _) = _
          rw [blockX_hc, stdBlock_xRow, hXv, hfRshift]
        by_cases h2 : j.val = k
        · rw [if_pos h2] at hXv
          rw [← hcj, h2, hfCk, hUXa, hXv, hfRk1]
        by_cases h3 : j.val = k + 1
        · rw [if_neg h2, if_pos h3] at hXv
          rw [← hcj, h3, hfCk1, hUXb, hXv, hfRk]
        have h4 : j.val = k + 2 := by omega
        rw [if_neg h2, if_neg h3, blockBack, if_neg (by omega),
          show j.val - 2 = k by omega, gridRowVal_mk _ _ (by omega)] at hXv
        have hXk : (H.X ⟨k, by omega⟩).val = k := congrArg Fin.val hH.2.2
        rw [← hcj, h4, hfCk2,
          show (Sum.inr (t.length + k, 0) : BCol) = P.hc ⟨k, by omega⟩ from rfl,
          hUXold _ (hPcL _)]
        change blockX _ _ _ (P.hc _) = _
        rw [blockX_hc, stdBlock_xRow, hXv, hXk]
        simp only [blockShift, lt_irrefl, if_false]
        exact hfRk2.symm
  have hfin := movesTo_insertBlock (endData t κ ht p' H' hH'.1 hH'.2.1)
    (markData t κ ht p' H' hH'.1 hH'.2.1)
  refine ((m1.trans m2).trans m3).trans ?_
  rw [hrec]; exact hfin

end Absorb

end OnLeConjecture.KnotTheory.MarkedCancel
