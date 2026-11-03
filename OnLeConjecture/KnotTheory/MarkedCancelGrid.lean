/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelInsert
public import OnLeConjecture.KnotTheory.SignedWordGridMovesInit

/-!
# Marked word grids

A *marked word grid* of a signed word `v` with marked integer arc leaving the corner `p` is the
signed word grid of `v` with a protected block inserted into the row of that arc, the block
columns placed immediately after the column of `p` (`markedGrid`). The column of `p` has its `O`
marking in the input row of the block, so that the input row is short, and the column where the
arc ends has its `X` marking in the output row. This is the framed insertion of the written
proof of Statement E (`statement_E_complete_proof.tex`, Section 8, "The frame and its elementary
exchanges"), with the block next to the outgoing end of the arc.

The underlying signed word grid is the corner grid `SignedGrid.sCornerGrid v κ` of a key `κ`
refining the outgoing heights, relabelled by `Sum.inr` (`plainGrid`). The protected block has the
columns `Sum.inr (N₀ + j, 0)` and the rows `Sum.inr (N₀ + i, 1)` (input row `i = 0`, output row
`i = k + 1`), where `N₀` is the length of `v` (`stdBlock`). `IsMarkedGrid v p H M` says that `M`
is the grid of a marked word grid for some
admissible key.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow

variable {m : ℕ}

/-! ### The plain corner grid -/

theorem sfCol_zero (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    sfCol 0 v p = Sum.inr (p.1.val, p.2) := by
  simp [sfCol]

/-- The corner grid of a signed word with all labels `Sum.inr (h, c)`. -/
def plainGrid (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ) (hL : 0 < v.length) :
    LabeledGrid (v.length * 3) BCol BRow :=
  (sCornerGrid v κ).relabel (sfCol 0 v) (sfColInv v hL) (sfCol 0 v) (sfColInv v hL)
    (fun c _ => sfColInv_sfCol v hL c) (fun r _ => sfColInv_sfCol v hL r)

theorem plainGrid_toGrid (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ)
    (hL : 0 < v.length) : (plainGrid v κ hL).toGrid = (sCornerGrid v κ).toGrid :=
  LabeledGrid.toGrid_relabel _ _ _ _ _ _ _

theorem plainGrid_cols (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ)
    (hL : 0 < v.length) : (plainGrid v κ hL).cols = (sCols v).map (sfCol 0 v) := rfl

theorem plainGrid_rows (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ)
    (hL : 0 < v.length) : (plainGrid v κ hL).rows = (sRows v κ).map (sfCol 0 v) := rfl

theorem mem_plainGrid_cols {v : SignedAdjacentWord m} {κ : Fin v.length × Fin 3 → ℕ}
    {hL : 0 < v.length} {c : BCol} :
    c ∈ (plainGrid v κ hL).cols ↔ ∃ p : Fin v.length × Fin 3, c = Sum.inr (p.1.val, p.2) := by
  rw [plainGrid_cols, List.mem_map]
  constructor
  · rintro ⟨p, -, rfl⟩; exact ⟨p, sfCol_zero v p⟩
  · rintro ⟨p, rfl⟩; exact ⟨p, mem_sCols v p, sfCol_zero v p⟩

theorem mem_plainGrid_rows {v : SignedAdjacentWord m} {κ : Fin v.length × Fin 3 → ℕ}
    {hL : 0 < v.length} {x : BRow} :
    x ∈ (plainGrid v κ hL).rows ↔ ∃ p : Fin v.length × Fin 3, x = Sum.inr (p.1.val, p.2) := by
  rw [plainGrid_rows, List.mem_map]
  constructor
  · rintro ⟨p, -, rfl⟩; exact ⟨p, sfCol_zero v p⟩
  · rintro ⟨p, rfl⟩; exact ⟨p, mem_sRows v κ p, sfCol_zero v p⟩

theorem plainGrid_O (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ) (hL : 0 < v.length)
    (p : Fin v.length × Fin 3) :
    (plainGrid v κ hL).O (Sum.inr (p.1.val, p.2)) = Sum.inr (p.1.val, p.2) := by
  change sfCol 0 v (sfColInv v hL (Sum.inr (p.1.val, p.2))) = _
  rw [show (Sum.inr (p.1.val, p.2) : BCol) = sfCol 0 v p from (sfCol_zero v p).symm,
    sfColInv_sfCol]

theorem plainGrid_X (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ) (hL : 0 < v.length)
    (q : Fin v.length × Fin 3) :
    (plainGrid v κ hL).X (Sum.inr (q.1.val, q.2)) =
      Sum.inr (((sM v).symm q).1.val, ((sM v).symm q).2) := by
  change sfCol 0 v ((sM v).symm (sfColInv v hL (Sum.inr (q.1.val, q.2)))) = _
  rw [show (Sum.inr (q.1.val, q.2) : BCol) = sfCol 0 v q from (sfCol_zero v q).symm,
    sfColInv_sfCol, sfCol_zero]

/-! ### The standard protected block -/

section Block

variable {k : ℕ}

/-- The standard labels of a protected block: columns `Sum.inr (N₀ + j, 0)` and rows
`Sum.inr (N₀ + i, 1)`. -/
def stdBlock (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0) (N₀ : ℕ) :
    ProtBlock k BCol BRow where
  H := H
  hc j := Sum.inr (N₀ + j.val, 0)
  hr i := Sum.inr (N₀ + i.val, 1)
  hc_inj j j' h := by
    simp only [Sum.inr.injEq, Prod.mk.injEq, add_right_inj] at h
    exact Fin.ext h.1
  hr_inj i i' h := by
    simp only [Sum.inr.injEq, Prod.mk.injEq, add_right_inj] at h
    exact Fin.ext h.1
  X_zero := hX
  O_last := hO

theorem stdBlock_hr (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0)
    (N₀ : ℕ) (i : Fin (k + 2)) : (stdBlock H hX hO N₀).hr i = Sum.inr (N₀ + i.val, 1) := rfl

theorem stdBlock_hc (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0)
    (N₀ : ℕ) (j : Fin (k + 1)) : (stdBlock H hX hO N₀).hc j = Sum.inr (N₀ + j.val, 0) := rfl

end Block

/-! ### The marked word grid -/

section Marked

variable {k : ℕ} (v : SignedAdjacentWord m) (κ : Fin v.length × Fin 3 → ℕ) (hL : 0 < v.length)
  (p : Fin v.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
  (hO : H.O (Fin.last k) = 0)

/-- The row of the marked arc. -/
abbrev markRow : BRow := Sum.inr (p.1.val, p.2)

theorem markRow_mem : markRow v p ∈ (plainGrid v κ hL).rows :=
  mem_plainGrid_rows.mpr ⟨p, rfl⟩

/-- The standard block of a marked word grid. -/
abbrev markBlock : ProtBlock k BCol BRow := stdBlock H hX hO v.length

/-- The insertion data of a marked word grid: the block columns follow the column of `p`. -/
def markData : InsertData (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO) where
  l₁ := ((sCols v).take (finProdFinEquiv p + 1)).map (sfCol 0 v)
  l₂ := ((sCols v).drop (finProdFinEquiv p + 1)).map (sfCol 0 v)
  m₁ := (List.append_of_mem (markRow_mem v κ hL p)).choose
  m₂ := (List.append_of_mem (markRow_mem v κ hL p)).choose_spec.choose
  cols_eq := by
    rw [plainGrid_cols, ← List.map_append, List.take_append_drop]
  rows_eq := (List.append_of_mem (markRow_mem v κ hL p)).choose_spec.choose_spec
  cols_fresh j hj := by
    obtain ⟨q, hq⟩ := mem_plainGrid_cols.mp hj
    simp only [markBlock, stdBlock, Sum.inr.injEq, Prod.mk.injEq] at hq
    have := q.1.isLt
    omega
  rows_fresh i hi := by
    exfalso
    obtain ⟨q, hq⟩ := mem_plainGrid_rows.mp hi
    rw [stdBlock_hr] at hq
    simp only [Sum.inr.injEq, Prod.mk.injEq] at hq
    have := q.1.isLt
    omega

/-- **The marked word grid** of `v` with key `κ`, marked arc leaving `p`, and protected grid `H`. -/
def markedGrid : LabeledGrid (v.length * 3 + k + 1) BCol BRow :=
  insertBlock (plainGrid v κ hL) (markRow v p) (markBlock v H hX hO) (markData v κ hL p H hX hO)

end Marked

/-- `M` is the grid of a marked word grid of `v` with marked arc leaving `p` and protected grid
`H`, for some key refining the outgoing heights. -/
def IsMarkedGrid {k : ℕ} (v : SignedAdjacentWord m) (hL : 0 < v.length) (p : Fin v.length × Fin 3)
    (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0)
    (M : GridDiagram (v.length * 3 + k + 1)) : Prop :=
  ∃ κ : Fin v.length × Fin 3 → ℕ, (∀ a b, v.oHeight2 a < v.oHeight2 b → κ a < κ b) ∧
    M = (markedGrid v κ hL p H hX hO).toGrid

end OnLeConjecture.KnotTheory.MarkedCancel
