/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.GridMoveRecognition

/-! # Grid diagrams presented by ordered labels

A labeled grid (`LabeledGrid n C R`) consists of a list of `n` distinct column labels, a list of
`n` distinct row labels, and two maps `O X : C → R` which restrict to bijections from the column
labels onto the row labels, with `O c ≠ X c`. Its grid diagram (`LabeledGrid.toGrid`) has the
`O`-marking of the column in position `i` in the position of the row label `O c`.

This presentation lets one describe grid moves in an arbitrary context: the other columns and rows
are just other entries of the two lists. This module proves the elementary move lemmas in this
language.

* `LabeledGrid.movesTo_swapCols`, `LabeledGrid.movesTo_swapRows`: exchanging two consecutive
  columns or rows with non-interleaving segments.
* `LabeledGrid.movesTo_destabX`, `LabeledGrid.movesTo_destabO`: destabilizations given by a
  pattern of three markings in two consecutive columns and two consecutive rows.
* `LabeledGrid.movesTo_rotateCols`: moving the first column to the end.
* `LabeledGrid.toGrid_eq_of_incidence`: two labeled grids with the same incidence pattern have
  the same grid diagram.

Segments are compared with `NonintN`, the non-interleaving relation of TauCeti written on natural
numbers. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-! ### Non-interleaving on natural numbers -/

/-- Membership of `x` in the open cyclic interval from `a` to `b`, on natural numbers. -/
def CIooN (a b x : ℕ) : Prop :=
  a ≠ b ∧ if a < b then a < x ∧ x < b else (a < x ∨ x < b)

instance (a b x : ℕ) : Decidable (CIooN a b x) := by
  unfold CIooN; infer_instance

/-- Non-interleaving of two pairs of natural numbers, with the cyclic intervals of `CIooN`. -/
def NonintN (a₀ a₁ b₀ b₁ : ℕ) : Prop :=
  (CIooN b₀ b₁ a₀ ↔ CIooN b₀ b₁ a₁) ∧ (CIooN a₀ a₁ b₀ ↔ CIooN a₀ a₁ b₁)

instance (a₀ a₁ b₀ b₁ : ℕ) : Decidable (NonintN a₀ a₁ b₀ b₁) := by
  unfold NonintN; infer_instance

theorem mem_cIoo_iff_cIooN {n : ℕ} (a b x : Fin n) :
    x ∈ Grid.cIoo a b ↔ CIooN a.val b.val x.val := by
  rw [Grid.mem_cIoo, CIooN, Fin.val_ne_iff]

/-- TauCeti's non-interleaving is `NonintN` on the values. -/
theorem noninterleaving_iff_nonintN {n : ℕ} (a₀ a₁ b₀ b₁ : Fin n) :
    Grid.Noninterleaving a₀ a₁ b₀ b₁ ↔ NonintN a₀.val a₁.val b₀.val b₁.val := by
  simp only [Grid.Noninterleaving, NonintN, mem_cIoo_iff_cIooN]

/-- Two pairs whose linear intervals are disjoint do not interleave. -/
theorem nonintN_of_lt {a₀ a₁ b₀ b₁ : ℕ} (h : max a₀ a₁ < min b₀ b₁ ∨ max b₀ b₁ < min a₀ a₁) :
    NonintN a₀ a₁ b₀ b₁ := by
  unfold NonintN CIooN
  rcases h with h | h <;> constructor <;> constructor <;> intro hh <;>
    simp only [max_lt_iff, lt_min_iff] at h <;> split_ifs at hh ⊢ <;> omega

/-- Two pairs whose linear intervals are strictly nested do not interleave. -/
theorem nonintN_of_nested {a₀ a₁ b₀ b₁ : ℕ}
    (h : (min b₀ b₁ < min a₀ a₁ ∧ max a₀ a₁ < max b₀ b₁) ∨
      (min a₀ a₁ < min b₀ b₁ ∧ max b₀ b₁ < max a₀ a₁)) :
    NonintN a₀ a₁ b₀ b₁ := by
  unfold NonintN CIooN
  rcases h with h | h <;> constructor <;> constructor <;> intro hh <;>
    simp only [min_lt_iff, lt_max_iff, max_lt_iff, lt_min_iff] at h <;> split_ifs at hh ⊢ <;>
    omega

/-- A pair of consecutive numbers does not interleave with a pair avoiding both. -/
theorem nonintN_of_adjacent {a₀ a₁ b₀ b₁ : ℕ} (ha : a₁ = a₀ + 1 ∨ a₀ = a₁ + 1)
    (h0 : b₀ ≠ a₀ ∧ b₀ ≠ a₁) (h1 : b₁ ≠ a₀ ∧ b₁ ≠ a₁) : NonintN a₀ a₁ b₀ b₁ := by
  unfold NonintN CIooN
  constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega

theorem nonintN_comm {a₀ a₁ b₀ b₁ : ℕ} : NonintN a₀ a₁ b₀ b₁ ↔ NonintN b₀ b₁ a₀ a₁ := by
  unfold NonintN; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ### Labeled grids -/

/-- A grid diagram presented by a list of distinct column labels, a list of distinct row labels of
the same length `n`, and the two marking maps. -/
structure LabeledGrid (n : ℕ) (C R : Type*) where
  /-- The column labels, from left to right. -/
  cols : List C
  /-- The row labels, from bottom to top. -/
  rows : List R
  /-- The row label of the `O`-marking of a column label. -/
  O : C → R
  /-- The row label of the `X`-marking of a column label. -/
  X : C → R
  cols_length : cols.length = n
  rows_length : rows.length = n
  cols_nodup : cols.Nodup
  rows_nodup : rows.Nodup
  O_mem : ∀ c ∈ cols, O c ∈ rows
  X_mem : ∀ c ∈ cols, X c ∈ rows
  O_inj : ∀ c ∈ cols, ∀ c' ∈ cols, O c = O c' → c = c'
  X_inj : ∀ c ∈ cols, ∀ c' ∈ cols, X c = X c' → c = c'
  O_ne_X : ∀ c ∈ cols, O c ≠ X c

namespace LabeledGrid

variable {n : ℕ} {C R : Type*}

section Positions

variable (G : LabeledGrid n C R)

/-- The column label in a position. -/
def colAt (i : Fin n) : C := G.cols[i.val]'(by rw [G.cols_length]; exact i.isLt)

/-- The row label in a position. -/
def rowAt (i : Fin n) : R := G.rows[i.val]'(by rw [G.rows_length]; exact i.isLt)

theorem colAt_mem (i : Fin n) : G.colAt i ∈ G.cols := List.getElem_mem _

theorem rowAt_mem (i : Fin n) : G.rowAt i ∈ G.rows := List.getElem_mem _

theorem colAt_injective : Function.Injective G.colAt := by
  intro i j h
  exact Fin.ext ((G.cols_nodup.getElem_inj_iff).mp h)

/-- The position of a column label. -/
def cpos [DecidableEq C] (c : C) : ℕ := G.cols.idxOf c

/-- The position of a row label. -/
def rpos [DecidableEq R] (r : R) : ℕ := G.rows.idxOf r

theorem cpos_lt [DecidableEq C] {c : C} (hc : c ∈ G.cols) : G.cpos c < n :=
  lt_of_lt_of_eq (List.idxOf_lt_length_iff.mpr hc) G.cols_length

theorem rpos_lt [DecidableEq R] {r : R} (hr : r ∈ G.rows) : G.rpos r < n :=
  lt_of_lt_of_eq (List.idxOf_lt_length_iff.mpr hr) G.rows_length

@[simp] theorem cpos_colAt [DecidableEq C] (i : Fin n) : G.cpos (G.colAt i) = i.val :=
  G.cols_nodup.idxOf_getElem _ _

@[simp] theorem rpos_rowAt [DecidableEq R] (i : Fin n) : G.rpos (G.rowAt i) = i.val :=
  G.rows_nodup.idxOf_getElem _ _

theorem colAt_cpos [DecidableEq C] {c : C} (hc : c ∈ G.cols) :
    G.colAt ⟨G.cpos c, G.cpos_lt hc⟩ = c :=
  List.getElem_idxOf _

theorem rowAt_rpos [DecidableEq R] {r : R} (hr : r ∈ G.rows) :
    G.rowAt ⟨G.rpos r, G.rpos_lt hr⟩ = r :=
  List.getElem_idxOf _

theorem rpos_inj [DecidableEq R] {r r' : R} (hr : r ∈ G.rows) (h : G.rpos r = G.rpos r') :
    r = r' :=
  (List.idxOf_inj hr).mp h

theorem cpos_inj [DecidableEq C] {c c' : C} (hc : c ∈ G.cols) (h : G.cpos c = G.cpos c') :
    c = c' :=
  (List.idxOf_inj hc).mp h

end Positions

section Grid

variable [DecidableEq R] (G : LabeledGrid n C R)

/-- The row position of the `O`-marking of the column in position `i`. -/
def oPos (i : Fin n) : Fin n := ⟨G.rpos (G.O (G.colAt i)), G.rpos_lt (G.O_mem _ (G.colAt_mem i))⟩

/-- The row position of the `X`-marking of the column in position `i`. -/
def xPos (i : Fin n) : Fin n := ⟨G.rpos (G.X (G.colAt i)), G.rpos_lt (G.X_mem _ (G.colAt_mem i))⟩

theorem oPos_injective : Function.Injective G.oPos := by
  intro i j h
  have h1 := G.rpos_inj (G.O_mem _ (G.colAt_mem i)) (congrArg Fin.val h)
  exact G.colAt_injective (G.O_inj _ (G.colAt_mem i) _ (G.colAt_mem j) h1)

theorem xPos_injective : Function.Injective G.xPos := by
  intro i j h
  have h1 := G.rpos_inj (G.X_mem _ (G.colAt_mem i)) (congrArg Fin.val h)
  exact G.colAt_injective (G.X_inj _ (G.colAt_mem i) _ (G.colAt_mem j) h1)

/-- The grid diagram of a labeled grid. -/
def toGrid : GridDiagram n where
  O := ⟨Equiv.ofBijective G.oPos (Finite.injective_iff_bijective.mp G.oPos_injective)⟩
  X := ⟨Equiv.ofBijective G.xPos (Finite.injective_iff_bijective.mp G.xPos_injective)⟩
  disjoint := by
    intro i h
    have h1 : G.oPos i = G.xPos i := h
    exact G.O_ne_X _ (G.colAt_mem i) (G.rpos_inj (G.O_mem _ (G.colAt_mem i))
      (congrArg Fin.val h1))

theorem toGrid_O_val (i : Fin n) : (G.toGrid.O i).val = G.rpos (G.O (G.colAt i)) := rfl

theorem toGrid_X_val (i : Fin n) : (G.toGrid.X i).val = G.rpos (G.X (G.colAt i)) := rfl

/-- The `O`-marking of the column labeled `c` lies in the position of the row label `O c`. -/
theorem toGrid_O_cpos [DecidableEq C] {c : C} (hc : c ∈ G.cols) :
    (G.toGrid.O ⟨G.cpos c, G.cpos_lt hc⟩).val = G.rpos (G.O c) := by
  rw [toGrid_O_val, colAt_cpos _ hc]

/-- The `X`-marking of the column labeled `c` lies in the position of the row label `X c`. -/
theorem toGrid_X_cpos [DecidableEq C] {c : C} (hc : c ∈ G.cols) :
    (G.toGrid.X ⟨G.cpos c, G.cpos_lt hc⟩).val = G.rpos (G.X c) := by
  rw [toGrid_X_val, colAt_cpos _ hc]

end Grid


/-! ### List lemmas -/

section ListLemmas

variable {α : Type*}

theorem getElem_append_cons_cons_of_ne (l₁ l₂ : List α) (a b : α) (k : ℕ)
    (hk1 : k ≠ l₁.length) (hk2 : k ≠ l₁.length + 1) (hk : k < (l₁ ++ b :: a :: l₂).length) :
    (l₁ ++ b :: a :: l₂)[k] = (l₁ ++ a :: b :: l₂)[k]'(by simpa using hk) := by
  rcases Nat.lt_or_ge k l₁.length with h | h
  · rw [List.getElem_append_left h, List.getElem_append_left h]
  · rw [List.getElem_append_right h, List.getElem_append_right h]
    obtain ⟨t, ht⟩ : ∃ t, k - l₁.length = t + 2 := ⟨k - l₁.length - 2, by omega⟩
    simp only [ht, List.getElem_cons_succ]

theorem getElem_append_cons_of_lt (l₁ l₂ : List α) (c : α) (k : ℕ) (h : k < l₁.length)
    (hk : k < (l₁ ++ l₂).length) :
    (l₁ ++ l₂)[k] = (l₁ ++ c :: l₂)[k]'(by simp at hk ⊢; omega) := by
  rw [List.getElem_append_left h, List.getElem_append_left h]

theorem getElem_append_cons_of_ge (l₁ l₂ : List α) (c : α) (k : ℕ) (h : l₁.length ≤ k)
    (hk : k < (l₁ ++ l₂).length) :
    (l₁ ++ l₂)[k] = (l₁ ++ c :: l₂)[k + 1]'(by simp at hk ⊢; omega) := by
  rw [List.getElem_append_right h, List.getElem_append_right (by omega)]
  simp only [show k + 1 - l₁.length = k - l₁.length + 1 by omega, List.getElem_cons_succ]

theorem idxOf_append_cons_of_ne [DecidableEq α] (m₁ m₂ : List α) (x r : α)
    (hrx : r ≠ x) :
    (m₁ ++ x :: m₂).idxOf r =
      if (m₁ ++ m₂).idxOf r < m₁.length then (m₁ ++ m₂).idxOf r
      else (m₁ ++ m₂).idxOf r + 1 := by
  by_cases h1 : r ∈ m₁
  · rw [List.idxOf_append_of_mem h1, List.idxOf_append_of_mem h1,
      if_pos (List.idxOf_lt_length_iff.mpr h1)]
  · rw [List.idxOf_append_of_notMem h1, List.idxOf_append_of_notMem h1,
      List.idxOf_cons_ne _ (Ne.symm hrx), if_neg (by omega)]
    rfl

theorem val_succAbove_eq {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

end ListLemmas

/-- Swapping two linearly adjacent columns with non-interleaving markings is a grid move. -/
theorem movesTo_swapColumns_of_val_eq_succ (G : GridDiagram n) {a b : Fin n}
    (hab : b.val = a.val + 1) (h : G.ColumnsNoninterleaving a b) :
    GridDiagram.MovesTo G (G.swapColumns a b) := by
  cases n with
  | zero => exact a.elim0
  | succ n =>
    have hb : finRotate (n + 1) a = b := GridMoves.finRotate_eq_of_val_eq_succ hab
    have h' := GridDiagram.movesTo_swapColumns G a (hb ▸ h)
    rw [hb] at h'
    exact h'

/-! ### Permuting the columns or the rows -/

section Permute

variable (G : LabeledGrid n C R)

/-- Replace the list of columns by a permutation of it. -/
def withCols (l : List C) (h : l.Perm G.cols) : LabeledGrid n C R where
  cols := l
  rows := G.rows
  O := G.O
  X := G.X
  cols_length := h.length_eq.trans G.cols_length
  rows_length := G.rows_length
  cols_nodup := h.nodup_iff.mpr G.cols_nodup
  rows_nodup := G.rows_nodup
  O_mem c hc := G.O_mem c (h.subset hc)
  X_mem c hc := G.X_mem c (h.subset hc)
  O_inj c hc c' hc' := G.O_inj c (h.subset hc) c' (h.subset hc')
  X_inj c hc c' hc' := G.X_inj c (h.subset hc) c' (h.subset hc')
  O_ne_X c hc := G.O_ne_X c (h.subset hc)

/-- Replace the list of rows by a permutation of it. -/
def withRows (l : List R) (h : l.Perm G.rows) : LabeledGrid n C R where
  cols := G.cols
  rows := l
  O := G.O
  X := G.X
  cols_length := G.cols_length
  rows_length := h.length_eq.trans G.rows_length
  cols_nodup := G.cols_nodup
  rows_nodup := h.nodup_iff.mpr G.rows_nodup
  O_mem c hc := h.symm.subset (G.O_mem c hc)
  X_mem c hc := h.symm.subset (G.X_mem c hc)
  O_inj := G.O_inj
  X_inj := G.X_inj
  O_ne_X := G.O_ne_X

/-- Exchange the two markings. -/
def swapMarks : LabeledGrid n C R where
  cols := G.cols
  rows := G.rows
  O := G.X
  X := G.O
  cols_length := G.cols_length
  rows_length := G.rows_length
  cols_nodup := G.cols_nodup
  rows_nodup := G.rows_nodup
  O_mem := G.X_mem
  X_mem := G.O_mem
  O_inj := G.X_inj
  X_inj := G.O_inj
  O_ne_X c hc := (G.O_ne_X c hc).symm

theorem colAt_eq_of_cols {L : List C} (h : G.cols = L) (i : Fin n) :
    G.colAt i = L[i.val]'(by rw [← h, G.cols_length]; exact i.isLt) :=
  List.getElem_of_eq h _

theorem rowAt_eq_of_rows {L : List R} (h : G.rows = L) (i : Fin n) :
    G.rowAt i = L[i.val]'(by rw [← h, G.rows_length]; exact i.isLt) :=
  List.getElem_of_eq h _

/-- Exchange two consecutive columns. -/
def swapCols {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂) :
    LabeledGrid n C R :=
  G.withCols (l₁ ++ b :: a :: l₂)
    (by rw [h]; exact List.Perm.append_left l₁ (List.Perm.swap a b l₂))

/-- Exchange two consecutive rows. -/
def swapRows {m₁ m₂ : List R} {x y : R} (h : G.rows = m₁ ++ x :: y :: m₂) :
    LabeledGrid n C R :=
  G.withRows (m₁ ++ y :: x :: m₂)
    (by rw [h]; exact List.Perm.append_left m₁ (List.Perm.swap x y m₂))

theorem swapCols_cols {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂) :
    (G.swapCols h).cols = l₁ ++ b :: a :: l₂ := rfl

theorem swapRows_rows {m₁ m₂ : List R} {x y : R} (h : G.rows = m₁ ++ x :: y :: m₂) :
    (G.swapRows h).rows = m₁ ++ y :: x :: m₂ := rfl

@[simp] theorem swapCols_rows {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂) :
    (G.swapCols h).rows = G.rows := rfl

@[simp] theorem swapCols_O {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂) :
    (G.swapCols h).O = G.O := rfl

@[simp] theorem swapCols_X {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂) :
    (G.swapCols h).X = G.X := rfl

@[simp] theorem swapRows_cols {m₁ m₂ : List R} {x y : R} (h : G.rows = m₁ ++ x :: y :: m₂) :
    (G.swapRows h).cols = G.cols := rfl

@[simp] theorem swapRows_O {m₁ m₂ : List R} {x y : R} (h : G.rows = m₁ ++ x :: y :: m₂) :
    (G.swapRows h).O = G.O := rfl

@[simp] theorem swapRows_X {m₁ m₂ : List R} {x y : R} (h : G.rows = m₁ ++ x :: y :: m₂) :
    (G.swapRows h).X = G.X := rfl

theorem length_of_cols_eq {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂) :
    l₁.length + 2 + l₂.length = n := by
  rw [← G.cols_length, h]; simp; omega

theorem length_of_rows_eq {m₁ m₂ : List R} {x y : R} (h : G.rows = m₁ ++ x :: y :: m₂) :
    m₁.length + 2 + m₂.length = n := by
  rw [← G.rows_length, h]; simp; omega

end Permute

section PermuteGrid

variable [DecidableEq R] (G : LabeledGrid n C R)

theorem toGrid_withCols (l : List C) (h : l.Perm G.cols) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, (G.withCols l h).colAt i = G.colAt (σ i)) :
    (G.withCols l h).toGrid = G.toGrid.relabelColumns σ.symm := by
  ext i
  · rw [GridDiagram.relabelColumns_O_apply, Equiv.symm_symm, toGrid_O_val, toGrid_O_val, hσ]
    rfl
  · rw [GridDiagram.relabelColumns_X_apply, Equiv.symm_symm, toGrid_X_val, toGrid_X_val, hσ]
    rfl

theorem toGrid_withRows (l : List R) (h : l.Perm G.rows) (ρ : Equiv.Perm (Fin n))
    (hρ : ∀ j, (G.withRows l h).rowAt j = G.rowAt (ρ j)) :
    (G.withRows l h).toGrid = G.toGrid.relabelRows ρ.symm := by
  have key : ∀ (r : R), r ∈ G.rows → ∀ j : Fin n, G.rowAt j = r →
      (G.withRows l h).rpos r = (ρ.symm j).val := by
    intro r _ j hj
    have h1 := (G.withRows l h).rpos_rowAt (ρ.symm j)
    rw [hρ, Equiv.apply_symm_apply, hj] at h1
    exact h1
  ext i
  · rw [GridDiagram.relabelRows_O_apply, toGrid_O_val]
    exact key _ (G.O_mem _ (G.colAt_mem i)) _ (G.rowAt_rpos (G.O_mem _ (G.colAt_mem i)))
  · rw [GridDiagram.relabelRows_X_apply, toGrid_X_val]
    exact key _ (G.X_mem _ (G.colAt_mem i)) _ (G.rowAt_rpos (G.X_mem _ (G.colAt_mem i)))

theorem toGrid_swapMarks : G.swapMarks.toGrid = G.toGrid.swapMarkings := by
  ext i <;> rfl

end PermuteGrid

section Swap

variable [DecidableEq R] (G : LabeledGrid n C R)

omit [DecidableEq R] in
/-- The positions of the two exchanged columns. -/
theorem colAt_swapCols {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂) (i : Fin n) :
    (G.swapCols h).colAt i = G.colAt (Equiv.swap ⟨l₁.length, by
        have := G.length_of_cols_eq h; omega⟩ ⟨l₁.length + 1, by
        have := G.length_of_cols_eq h; omega⟩ i) := by
  have hl := G.length_of_cols_eq h
  rw [(G.swapCols h).colAt_eq_of_cols (G.swapCols_cols h), G.colAt_eq_of_cols h]
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; simp
  · subst h2; simp
  · exact getElem_append_cons_cons_of_ne _ _ _ _ _ (fun he => h1 (Fin.ext he))
      (fun he => h2 (Fin.ext he)) _

omit [DecidableEq R] in
/-- The positions of the two exchanged rows. -/
theorem rowAt_swapRows {m₁ m₂ : List R} {x y : R} (h : G.rows = m₁ ++ x :: y :: m₂) (j : Fin n) :
    (G.swapRows h).rowAt j = G.rowAt (Equiv.swap ⟨m₁.length, by
        have := G.length_of_rows_eq h; omega⟩ ⟨m₁.length + 1, by
        have := G.length_of_rows_eq h; omega⟩ j) := by
  have hl := G.length_of_rows_eq h
  rw [(G.swapRows h).rowAt_eq_of_rows (G.swapRows_rows h), G.rowAt_eq_of_rows h]
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; simp
  · subst h2; simp
  · exact getElem_append_cons_cons_of_ne _ _ _ _ _ (fun he => h1 (Fin.ext he))
      (fun he => h2 (Fin.ext he)) _

/-- **Column exchange.** Two consecutive columns with non-interleaving segments can be
exchanged by a grid move. -/
theorem movesTo_swapCols {l₁ l₂ : List C} {a b : C} (h : G.cols = l₁ ++ a :: b :: l₂)
    (hni : NonintN (G.rpos (G.O a)) (G.rpos (G.X a)) (G.rpos (G.O b)) (G.rpos (G.X b))) :
    G.toGrid.MovesTo (G.swapCols h).toGrid := by
  have hl := G.length_of_cols_eq h
  rw [swapCols, G.toGrid_withCols _ _ _ (G.colAt_swapCols h), Equiv.symm_swap]
  apply movesTo_swapColumns_of_val_eq_succ _ rfl
  rw [GridDiagram.ColumnsNoninterleaving, noninterleaving_iff_nonintN, toGrid_O_val, toGrid_X_val,
    toGrid_O_val, toGrid_X_val, G.colAt_eq_of_cols h, G.colAt_eq_of_cols h]
  simpa using hni

/-- The column of the `O`-marking of a row. -/
theorem toGrid_O_transpose [DecidableEq C] {c : C} (hc : c ∈ G.cols) :
    G.toGrid.O.transpose ⟨G.rpos (G.O c), G.rpos_lt (G.O_mem c hc)⟩ =
      ⟨G.cpos c, G.cpos_lt hc⟩ := by
  rw [GridState.transpose_apply, Equiv.symm_apply_eq]
  exact (Fin.ext (G.toGrid_O_cpos hc)).symm

/-- The column of the `X`-marking of a row. -/
theorem toGrid_X_transpose [DecidableEq C] {c : C} (hc : c ∈ G.cols) :
    G.toGrid.X.transpose ⟨G.rpos (G.X c), G.rpos_lt (G.X_mem c hc)⟩ =
      ⟨G.cpos c, G.cpos_lt hc⟩ := by
  rw [GridState.transpose_apply, Equiv.symm_apply_eq]
  exact (Fin.ext (G.toGrid_X_cpos hc)).symm

/-- **Row exchange.** Two consecutive rows with non-interleaving segments can be exchanged by a
grid move. The columns `cx, cx'` carry the `O`- and `X`-markings of `x`, and `cy, cy'` those of
`y`. -/
theorem movesTo_swapRows [DecidableEq C] {m₁ m₂ : List R} {x y : R}
    (h : G.rows = m₁ ++ x :: y :: m₂) {cx cx' cy cy' : C} (hcx : cx ∈ G.cols)
    (hcx' : cx' ∈ G.cols) (hcy : cy ∈ G.cols) (hcy' : cy' ∈ G.cols) (hOx : G.O cx = x)
    (hXx : G.X cx' = x) (hOy : G.O cy = y) (hXy : G.X cy' = y)
    (hni : NonintN (G.cpos cx) (G.cpos cx') (G.cpos cy) (G.cpos cy')) :
    G.toGrid.MovesTo (G.swapRows h).toGrid := by
  have hl := G.length_of_rows_eq h
  rw [swapRows, G.toGrid_withRows _ _ _ (G.rowAt_swapRows h), Equiv.symm_swap]
  apply GridDiagram.movesTo_swapRows_of_val_eq_succ _ rfl
  have hx : G.rpos x = m₁.length := by
    rw [rpos, h, List.idxOf_append_of_notMem (fun hm => ?_)]
    · simp
    · have hnd := G.rows_nodup; rw [h] at hnd
      exact (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_cons_self) rfl
  have hy : G.rpos y = m₁.length + 1 := by
    have hnd := G.rows_nodup; rw [h] at hnd
    have hxy : x ≠ y := by
      have := (List.nodup_append.mp hnd).2.1
      intro he; subst he; simp at this
    rw [rpos, h, List.idxOf_append_of_notMem (fun hm => ?_), List.idxOf_cons_ne _ hxy]
    · simp
    · exact (List.nodup_append.mp hnd).2.2 _ hm _ (by simp) rfl
  rw [GridDiagram.RowsNoninterleaving, noninterleaving_iff_nonintN]
  have e1 := G.toGrid_O_transpose hcx
  have e2 := G.toGrid_X_transpose hcx'
  have e3 := G.toGrid_O_transpose hcy
  have e4 := G.toGrid_X_transpose hcy'
  simp only [hOx, hXx, hOy, hXy, hx, hy] at e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  exact hni

/-- **Cyclic permutation of columns.** Moving the first column to the end is a grid move. -/
theorem movesTo_rotateCols {c : C} {l : List C} (h : G.cols = c :: l) :
    G.toGrid.MovesTo
      (G.withCols (l ++ [c]) (by rw [h]; exact List.perm_append_singleton c l)).toGrid := by
  set G' := G.withCols (l ++ [c]) (by rw [h]; exact List.perm_append_singleton c l)
  have hl : l.length + 1 = n := by rw [← G.cols_length, h]; simp
  have hσ : ∀ i, G'.colAt i = G.colAt (finRotate n i) := by
    intro i
    rw [G'.colAt_eq_of_cols (show G'.cols = l ++ [c] from rfl), G.colAt_eq_of_cols h]
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
  have he : G'.toGrid = G.toGrid.relabelColumns (finRotate n).symm :=
    G.toGrid_withCols _ _ _ hσ
  have hm := GridDiagram.cyclicColumns_movesTo G'.toGrid
  have hb : G'.toGrid.relabelColumns (finRotate n) = G.toGrid := by
    rw [he]
    ext i <;> simp
  rw [hb] at hm
  exact hm.symm

end Swap


/-! ### Destabilizations -/

section Destab

variable [DecidableEq C]

theorem not_mem_of_nodup_middle {α : Type*} {l₁ l₂ : List α} {c : α}
    (h : (l₁ ++ c :: l₂).Nodup) : c ∉ l₁ ++ l₂ :=
  (List.nodup_cons.mp (List.nodup_middle.mp h)).1

theorem nodup_of_nodup_middle {α : Type*} {l₁ l₂ : List α} {c : α}
    (h : (l₁ ++ c :: l₂).Nodup) : (l₁ ++ l₂).Nodup :=
  (List.nodup_cons.mp (List.nodup_middle.mp h)).2

theorem mem_middle_of_mem {α : Type*} {l₁ l₂ : List α} {c a : α} (h : a ∈ l₁ ++ l₂) :
    a ∈ l₁ ++ c :: l₂ := by
  simp only [List.mem_append, List.mem_cons] at h ⊢; tauto

theorem mem_of_mem_middle_of_ne {α : Type*} {l₁ l₂ : List α} {c a : α} (h : a ∈ l₁ ++ c :: l₂)
    (hne : a ≠ c) : a ∈ l₁ ++ l₂ := by
  simp only [List.mem_append, List.mem_cons] at h ⊢; tauto

/-- The result of an `X`-destabilization: delete the column `c` and the row `x = O c`, and move
the `X`-marking of the column `d`, which lies in the row `x`, to the row `y = X c`. -/
def destabX (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C} {x y : R}
    (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hOc : G.O c = x)
    (hXc : G.X c = y) (hXd : G.X d = x) (hOd : G.O d ≠ y) (hd : d ∈ G.cols) :
    LabeledGrid n C R where
  cols := l₁ ++ l₂
  rows := m₁ ++ m₂
  O := G.O
  X := Function.update G.X d y
  cols_length := by have := G.cols_length; rw [hc] at this; simp at this ⊢; omega
  rows_length := by have := G.rows_length; rw [hx] at this; simp at this ⊢; omega
  cols_nodup := nodup_of_nodup_middle (hc ▸ G.cols_nodup)
  rows_nodup := nodup_of_nodup_middle (hx ▸ G.rows_nodup)
  O_mem c' hc' := by
    have hc'm : c' ∈ G.cols := hc ▸ mem_middle_of_mem hc'
    have hne : c' ≠ c := fun he => not_mem_of_nodup_middle (hc ▸ G.cols_nodup) (he ▸ hc')
    have h1 := G.O_mem c' hc'm
    rw [hx] at h1
    refine mem_of_mem_middle_of_ne h1 fun he => hne ?_
    exact G.O_inj c' hc'm c (hc ▸ List.mem_append_right _ List.mem_cons_self) (he.trans hOc.symm)
  X_mem c' hc' := by
    have hcm : c ∈ G.cols := hc ▸ List.mem_append_right _ List.mem_cons_self
    have hc'm : c' ∈ G.cols := hc ▸ mem_middle_of_mem hc'
    by_cases hcd : c' = d
    · subst hcd
      rw [Function.update_self]
      have h1 := G.X_mem c hcm
      rw [hXc, hx] at h1
      refine mem_of_mem_middle_of_ne h1 fun he => G.O_ne_X c hcm ?_
      rw [hOc, hXc, he]
    · rw [Function.update_of_ne hcd]
      have h1 := G.X_mem c' hc'm
      rw [hx] at h1
      exact mem_of_mem_middle_of_ne h1 fun he => hcd (G.X_inj c' hc'm d hd (he.trans hXd.symm))
  O_inj c₁ h₁ c₂ h₂ := G.O_inj c₁ (hc ▸ mem_middle_of_mem h₁) c₂ (hc ▸ mem_middle_of_mem h₂)
  X_inj c₁ h₁ c₂ h₂ := by
    have hcm : c ∈ G.cols := hc ▸ List.mem_append_right _ List.mem_cons_self
    have hn₁ : c₁ ≠ c := fun he => not_mem_of_nodup_middle (hc ▸ G.cols_nodup) (he ▸ h₁)
    have hn₂ : c₂ ≠ c := fun he => not_mem_of_nodup_middle (hc ▸ G.cols_nodup) (he ▸ h₂)
    have hm₁ : c₁ ∈ G.cols := hc ▸ mem_middle_of_mem h₁
    have hm₂ : c₂ ∈ G.cols := hc ▸ mem_middle_of_mem h₂
    intro he
    by_cases e1 : c₁ = d <;> by_cases e2 : c₂ = d
    · rw [e1, e2]
    · rw [e1, Function.update_self, Function.update_of_ne e2, ← hXc] at he
      exact absurd (G.X_inj c hcm c₂ hm₂ he).symm hn₂
    · rw [e2, Function.update_self, Function.update_of_ne e1, ← hXc] at he
      exact absurd (G.X_inj c₁ hm₁ c hcm he) hn₁
    · rw [Function.update_of_ne e1, Function.update_of_ne e2] at he
      exact G.X_inj c₁ hm₁ c₂ hm₂ he
  O_ne_X c' hc' := by
    by_cases hcd : c' = d
    · subst hcd; rw [Function.update_self]; exact hOd
    · rw [Function.update_of_ne hcd]; exact G.O_ne_X c' (hc ▸ mem_middle_of_mem hc')

theorem destabX_cols (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hOc : G.O c = x)
    (hXc : G.X c = y) (hXd : G.X d = x) (hOd : G.O d ≠ y) (hd : d ∈ G.cols) :
    (G.destabX hc hx hOc hXc hXd hOd hd).cols = l₁ ++ l₂ := rfl

theorem destabX_rows (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hOc : G.O c = x)
    (hXc : G.X c = y) (hXd : G.X d = x) (hOd : G.O d ≠ y) (hd : d ∈ G.cols) :
    (G.destabX hc hx hOc hXc hXd hOd hd).rows = m₁ ++ m₂ := rfl

theorem destabX_O (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hOc : G.O c = x)
    (hXc : G.X c = y) (hXd : G.X d = x) (hOd : G.O d ≠ y) (hd : d ∈ G.cols) :
    (G.destabX hc hx hOc hXc hXd hOd hd).O = G.O := rfl

theorem destabX_X (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hOc : G.O c = x)
    (hXc : G.X c = y) (hXd : G.X d = x) (hOd : G.O d ≠ y) (hd : d ∈ G.cols) :
    (G.destabX hc hx hOc hXc hXd hOd hd).X = Function.update G.X d y := rfl

theorem cpos_of_cols_eq (G : LabeledGrid n C R) {l₁ l₂ : List C} {c : C}
    (hc : G.cols = l₁ ++ c :: l₂) : G.cpos c = l₁.length := by
  rw [cpos, hc, List.idxOf_append_of_notMem (fun hm => ?_), List.idxOf_cons_self]
  · rfl
  · have hnd := G.cols_nodup; rw [hc] at hnd
    exact not_mem_of_nodup_middle hnd (List.mem_append_left _ hm)

omit [DecidableEq C] in
theorem rpos_of_rows_eq [DecidableEq R] (G : LabeledGrid n C R) {m₁ m₂ : List R} {x : R}
    (hx : G.rows = m₁ ++ x :: m₂) : G.rpos x = m₁.length := by
  rw [rpos, hx, List.idxOf_append_of_notMem (fun hm => ?_), List.idxOf_cons_self]
  · rfl
  · have hnd := G.rows_nodup; rw [hx] at hnd
    exact not_mem_of_nodup_middle hnd (List.mem_append_left _ hm)

/-- **`X`-destabilization.** If the columns `c, d` and the rows `x = O c`, `y = X c` are
consecutive, `X d = x` and `O d ≠ y`, then deleting `c` and `x` is a destabilization. -/
theorem isDestabilization_destabX [DecidableEq R] (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C}
    {m₁ m₂ : List R} {c d : C} {x y : R} (hc : G.cols = l₁ ++ c :: l₂)
    (hx : G.rows = m₁ ++ x :: m₂) (hOc : G.O c = x) (hXc : G.X c = y) (hXd : G.X d = x)
    (hOd : G.O d ≠ y) (hd : d ∈ G.cols)
    (hcol : G.cpos d = G.cpos c + 1 ∨ G.cpos c = G.cpos d + 1)
    (hrow : G.rpos y = G.rpos x + 1 ∨ G.rpos x = G.rpos y + 1) :
    GridDiagram.IsDestabilization G.toGrid (G.destabX hc hx hOc hXc hXd hOd hd).toGrid := by
  set D := G.destabX hc hx hOc hXc hXd hOd hd
  have hcm : c ∈ G.cols := hc ▸ List.mem_append_right _ List.mem_cons_self
  have hxm : x ∈ G.rows := hx ▸ List.mem_append_right _ List.mem_cons_self
  have hym : y ∈ G.rows := hXc ▸ G.X_mem c hcm
  have hxy : x ≠ y := fun he => G.O_ne_X c hcm (by rw [hOc, hXc, he])
  have hcpos := G.cpos_of_cols_eq hc
  have hrpos := G.rpos_of_rows_eq hx
  let cI : Fin (n + 1) := ⟨G.cpos c, G.cpos_lt hcm⟩
  let dI : Fin (n + 1) := ⟨G.cpos d, G.cpos_lt hd⟩
  have hOcI : (G.toGrid.O cI).val = G.rpos x := by rw [G.toGrid_O_cpos hcm, hOc]
  have hXcI : (G.toGrid.X cI).val = G.rpos y := by rw [G.toGrid_X_cpos hcm, hXc]
  have hd' : G.toGrid.X dI = G.toGrid.O cI := Fin.ext (by rw [G.toGrid_X_cpos hd, hXd, hOcI])
  have h4' : G.toGrid.O dI ≠ G.toGrid.X cI := by
    intro he
    have := congrArg Fin.val he
    rw [G.toGrid_O_cpos hd, hXcI] at this
    exact hOd (G.rpos_inj (G.O_mem d hd) this)
  have hcol' : finRotate (n + 1) cI = dI ∨ finRotate (n + 1) dI = cI := by
    rcases hcol with h | h
    · exact Or.inl (GridMoves.finRotate_eq_of_val_eq_succ h)
    · exact Or.inr (GridMoves.finRotate_eq_of_val_eq_succ h)
  have hrow' : finRotate (n + 1) (G.toGrid.O cI) = G.toGrid.X cI ∨
      finRotate (n + 1) (G.toGrid.X cI) = G.toGrid.O cI := by
    rcases hrow with h | h
    · exact Or.inl (GridMoves.finRotate_eq_of_val_eq_succ (by rw [hOcI, hXcI, h]))
    · exact Or.inr (GridMoves.finRotate_eq_of_val_eq_succ (by rw [hOcI, hXcI, h]))
  have hstab := G.toGrid.isXStabilization_eraseOCorner cI dI hd' h4' hcol' hrow'
  -- Columns of `D` are the columns of `G` other than `c`.
  have hcolD : ∀ k : Fin n, D.colAt k = G.colAt (cI.succAbove k) := by
    intro k
    rw [D.colAt_eq_of_cols (show D.cols = l₁ ++ l₂ from rfl), G.colAt_eq_of_cols hc]
    have hv := val_succAbove_eq cI k
    have hcI : cI.val = l₁.length := hcpos
    by_cases hk : k.val < l₁.length
    · rw [getElem_append_cons_of_lt l₁ l₂ c k.val hk]
      congr 1
      rw [hv, if_pos (by omega)]
    · rw [getElem_append_cons_of_ge l₁ l₂ c k.val (by omega)]
      congr 1
      rw [hv, if_neg (by omega)]
  -- Rows of `D` are the rows of `G` other than `x`.
  have hlift : ∀ r, r ∈ D.rows → ∀ k : Fin n, D.rpos r = k.val →
      ((G.toGrid.O cI).succAbove k).val = G.rpos r := by
    intro r hr k hk
    have hrx : r ≠ x := fun he => not_mem_of_nodup_middle (hx ▸ G.rows_nodup) (he ▸ hr)
    have e1 : G.rpos r = if D.rpos r < m₁.length then D.rpos r else D.rpos r + 1 := by
      rw [rpos, hx, idxOf_append_cons_of_ne m₁ m₂ x r hrx]; rfl
    rw [val_succAbove_eq, e1, hk, hOcI, hrpos]
  have hO' : ∀ k : Fin n, G.toGrid.O (cI.succAbove k) =
      (G.toGrid.O cI).succAbove (D.toGrid.O k) := by
    intro k
    apply Fin.ext
    have h1 : (G.toGrid.O (cI.succAbove k)).val = G.rpos (G.O (D.colAt k)) := by
      rw [G.toGrid_O_val, hcolD k]
    rw [h1, hlift _ (D.O_mem _ (D.colAt_mem k)) _ (D.toGrid_O_val k).symm]
    rfl
  have hX' : ∀ k : Fin n, G.toGrid.X (Equiv.swap cI dI (cI.succAbove k)) =
      (G.toGrid.O cI).succAbove (D.toGrid.X k) := by
    intro k
    apply Fin.ext
    rw [hlift _ (D.X_mem _ (D.colAt_mem k)) _ (D.toGrid_X_val k).symm]
    by_cases hk : D.colAt k = d
    · have hs : Equiv.swap cI dI (cI.succAbove k) = cI := by
        have : cI.succAbove k = dI := by
          apply Fin.ext
          have := congrArg G.cpos ((hcolD k).symm.trans hk)
          rw [G.cpos_colAt] at this
          exact this
        rw [this, Equiv.swap_apply_right]
      rw [hs, hXcI]
      change G.rpos y = G.rpos (Function.update G.X d y (D.colAt k))
      rw [hk, Function.update_self]
    · have hne1 : cI.succAbove k ≠ cI := Fin.succAbove_ne cI k
      have hne2 : cI.succAbove k ≠ dI := by
        intro he
        apply hk
        rw [hcolD k, he]
        exact G.colAt_cpos hd
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, G.toGrid_X_val, ← hcolD k]
      change G.rpos (G.X (D.colAt k)) = G.rpos (Function.update G.X d y (D.colAt k))
      rw [Function.update_of_ne hk]
  have hD : G.toGrid.eraseOCorner cI dI hd' h4' = D.toGrid := by
    ext1
    · refine GridState.ext fun k => ?_
      apply (G.toGrid.O cI).succAbove_right_injective
      rw [GridDiagram.succAbove_eraseOCorner_O]
      exact hO' k
    · refine GridState.ext fun k => ?_
      apply (G.toGrid.O cI).succAbove_right_injective
      rw [GridDiagram.succAbove_eraseOCorner_X]
      exact hX' k
  rw [← hD]
  exact (GridDiagram.isDestabilization_iff_isStabilization _ _).mpr
    ((GridDiagram.isStabilization_iff _ _).mpr (Or.inr hstab))

/-- The result of an `O`-destabilization: delete the column `c` and the row `x = X c`, and move
the `O`-marking of the column `d`, which lies in the row `x`, to the row `y = O c`. -/
def destabO (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C} {x y : R}
    (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hXc : G.X c = x)
    (hOc : G.O c = y) (hOd : G.O d = x) (hXd : G.X d ≠ y) (hd : d ∈ G.cols) :
    LabeledGrid n C R :=
  (G.swapMarks.destabX hc hx hXc hOc hOd hXd hd).swapMarks

theorem destabO_cols (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hXc : G.X c = x)
    (hOc : G.O c = y) (hOd : G.O d = x) (hXd : G.X d ≠ y) (hd : d ∈ G.cols) :
    (G.destabO hc hx hXc hOc hOd hXd hd).cols = l₁ ++ l₂ := rfl

theorem destabO_rows (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hXc : G.X c = x)
    (hOc : G.O c = y) (hOd : G.O d = x) (hXd : G.X d ≠ y) (hd : d ∈ G.cols) :
    (G.destabO hc hx hXc hOc hOd hXd hd).rows = m₁ ++ m₂ := rfl

theorem destabO_O (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hXc : G.X c = x)
    (hOc : G.O c = y) (hOd : G.O d = x) (hXd : G.X d ≠ y) (hd : d ∈ G.cols) :
    (G.destabO hc hx hXc hOc hOd hXd hd).O = Function.update G.O d y := rfl

theorem destabO_X (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {c d : C}
    {x y : R} (hc : G.cols = l₁ ++ c :: l₂) (hx : G.rows = m₁ ++ x :: m₂) (hXc : G.X c = x)
    (hOc : G.O c = y) (hOd : G.O d = x) (hXd : G.X d ≠ y) (hd : d ∈ G.cols) :
    (G.destabO hc hx hXc hOc hOd hXd hd).X = G.X := rfl

/-- **`O`-destabilization.** If the columns `c, d` and the rows `x = X c`, `y = O c` are
consecutive, `O d = x` and `X d ≠ y`, then deleting `c` and `x` is a destabilization. -/
theorem isDestabilization_destabO [DecidableEq R] (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C}
    {m₁ m₂ : List R} {c d : C} {x y : R} (hc : G.cols = l₁ ++ c :: l₂)
    (hx : G.rows = m₁ ++ x :: m₂) (hXc : G.X c = x) (hOc : G.O c = y) (hOd : G.O d = x)
    (hXd : G.X d ≠ y) (hd : d ∈ G.cols)
    (hcol : G.cpos d = G.cpos c + 1 ∨ G.cpos c = G.cpos d + 1)
    (hrow : G.rpos y = G.rpos x + 1 ∨ G.rpos x = G.rpos y + 1) :
    GridDiagram.IsDestabilization G.toGrid (G.destabO hc hx hXc hOc hOd hXd hd).toGrid := by
  have h := G.swapMarks.isDestabilization_destabX hc hx hXc hOc hOd hXd hd hcol hrow
  rw [toGrid_swapMarks] at h
  rw [destabO, toGrid_swapMarks, ← GridDiagram.isDestabilization_swapMarkings,
    GridDiagram.swapMarkings_swapMarkings]
  exact h

end Destab

/-! ### Labeled grids with the same incidence -/

/-- Two labeled grids of the same size whose markings occupy the same positions have the same
grid diagram. -/
theorem toGrid_eq_of_incidence [DecidableEq R] {C' R' : Type*} [DecidableEq R']
    (G : LabeledGrid n C R) (G' : LabeledGrid n C' R')
    (hO : ∀ i : Fin n, G.rpos (G.O (G.colAt i)) = G'.rpos (G'.O (G'.colAt i)))
    (hX : ∀ i : Fin n, G.rpos (G.X (G.colAt i)) = G'.rpos (G'.X (G'.colAt i))) :
    G.toGrid = G'.toGrid := by
  ext i
  · exact congrArg Fin.val (show G.toGrid.O i = G'.toGrid.O i from Fin.ext (hO i))
  · exact congrArg Fin.val (show G.toGrid.X i = G'.toGrid.X i from Fin.ext (hX i))

end LabeledGrid

end OnLeConjecture.KnotTheory
