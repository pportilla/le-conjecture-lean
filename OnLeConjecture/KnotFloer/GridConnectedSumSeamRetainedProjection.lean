/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamRetainedRectangles

/-!
# Projecting retained rectangles to the first factor

The final column of the first factor is placed at the unique southwest
column in the second block. This increasing column embedding identifies
all state points whose row belongs to the first block. Rectangles with a
side strictly before the seam project to first-factor rectangles, and
emptiness passes to the projection.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The first-factor columns, with its final column placed at the moving southwest point. -/
def seamFirstFactorColumn (z : GridState (m + 1)) (a : Fin (n + 1)) : Fin (n + m + 1) :=
  if a = Fin.last n then seamRight n m (z.toPerm.symm 0) else seamLeft n m a

@[simp] theorem seamFirstFactorColumn_last (z : GridState (m + 1)) :
    seamFirstFactorColumn (n := n) z (Fin.last n) = seamRight n m (z.toPerm.symm 0) := by
  simp only [seamFirstFactorColumn, ite_true]

@[simp] theorem seamFirstFactorColumn_castSucc (z : GridState (m + 1)) (a : Fin n) :
    seamFirstFactorColumn z a.castSucc = seamLeft n m a.castSucc := by
  simp only [seamFirstFactorColumn, Fin.castSucc_ne_last, if_false]

theorem seamFirstFactorColumn_strictMono (z : GridState (m + 1)) :
    StrictMono (seamFirstFactorColumn (n := n) z) := by
  intro a b hab
  have ha : a ≠ Fin.last n := by
    intro hh
    have := b.isLt
    rw [hh] at hab
    simp only [Fin.lt_def, Fin.val_last] at hab
    omega
  by_cases hb : b = Fin.last n
  · rw [hb, seamFirstFactorColumn_last, seamFirstFactorColumn, if_neg ha]
    change a.val < n + (z.toPerm.symm 0).val
    have := a.isLt
    have hh : a.val ≠ n := fun h => ha (Fin.ext h)
    omega
  · simpa only [seamFirstFactorColumn, if_neg ha, if_neg hb, Fin.lt_def,
      seamLeft_val] using hab

theorem seamFirstFactorColumn_injective (z : GridState (m + 1)) :
    Function.Injective (seamFirstFactorColumn (n := n) z) :=
  (seamFirstFactorColumn_strictMono z).injective

/-- State rows along the embedded first-factor columns are precisely the first-factor rows. -/
@[simp] theorem seamState_firstFactorColumn (x : GridState (n + 1))
    (z : GridState (m + 1)) (a : Fin (n + 1)) :
    seamState x z (seamFirstFactorColumn z a) = seamLeft n m (x a) := by
  induction a using Fin.lastCases with
  | last =>
    rw [seamFirstFactorColumn_last]
    exact seamState_right_of_zero x z _ (z.toPerm.apply_symm_apply 0)
  | cast a => rw [seamFirstFactorColumn_castSucc, seamState_left_castSucc]

/-- The inverse index on embedded first-factor columns. -/
def seamFirstFactorIndex (c : Fin (n + m + 1)) : Fin (n + 1) :=
  if h : c.val < n then ⟨c.val, by omega⟩ else Fin.last n

@[simp] theorem seamFirstFactorIndex_column (z : GridState (m + 1)) (a : Fin (n + 1)) :
    seamFirstFactorIndex (seamFirstFactorColumn z a) = a := by
  induction a using Fin.lastCases with
  | last =>
    simp only [seamFirstFactorColumn_last, seamFirstFactorIndex, seamRight_val]
    rw [dif_neg (by omega)]
  | cast a =>
    simp only [seamFirstFactorColumn_castSucc, seamFirstFactorIndex, seamLeft_val,
      Fin.val_castSucc, dif_pos a.isLt]
    exact Fin.ext rfl

/-- Columns whose state row is at most n are exactly the embedded first-factor columns. -/
theorem seamFirstFactorColumn_index_of_row_le (x : GridState (n + 1))
    (z : GridState (m + 1)) (c : Fin (n + m + 1))
    (hc : (seamState x z c).val ≤ n) :
    seamFirstFactorColumn z (seamFirstFactorIndex c) = c := by
  by_cases hcn : c.val < n
  · have he : (⟨c.val, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
      intro hh
      have := congrArg Fin.val hh
      simp only [Fin.val_last] at this
      omega
    simp only [seamFirstFactorIndex, dif_pos hcn, seamFirstFactorColumn, if_neg he]
    exact Fin.ext rfl
  · let d : Fin (m + 1) := ⟨c.val - n, by have := c.isLt; omega⟩
    have hd : seamRight n m d = c := by
      apply Fin.ext
      simp only [seamRight_val, d]
      omega
    have hz : z d = 0 := (seamState_right_row_le_iff x z d).mp (hd.symm ▸ hc)
    have hz' : z.toPerm.symm 0 = d := by
      exact z.toPerm.symm_apply_eq.mpr hz.symm
    simp only [seamFirstFactorIndex, dif_neg hcn, seamFirstFactorColumn_last, hz', hd]

theorem seamFirstFactorColumn_range_iff (x : GridState (n + 1))
    (z : GridState (m + 1)) (c : Fin (n + m + 1)) :
    c ∈ Set.range (seamFirstFactorColumn (n := n) z) ↔ (seamState x z c).val ≤ n := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [seamState_firstFactorColumn, seamLeft_val]
    exact Nat.le_of_lt_succ (x a).isLt
  · intro hc
    exact ⟨seamFirstFactorIndex c, seamFirstFactorColumn_index_of_row_le x z c hc⟩

private theorem strictMono_mem_cIoo_iff {k l : ℕ} (f : Fin k → Fin l) (hf : StrictMono f)
    (a b c : Fin k) : f c ∈ Grid.cIoo (f a) (f b) ↔ c ∈ Grid.cIoo a b := by
  simp only [Grid.mem_cIoo, ← Fin.lt_def, hf.lt_iff_lt, hf.injective.ne_iff]

@[simp] theorem seamFirstFactorColumn_mem_cIoo_iff (z : GridState (m + 1))
    (a b c : Fin (n + 1)) :
    seamFirstFactorColumn z c ∈ Grid.cIoo (seamFirstFactorColumn z a)
      (seamFirstFactorColumn z b) ↔ c ∈ Grid.cIoo a b :=
  strictMono_mem_cIoo_iff _ (seamFirstFactorColumn_strictMono z) a b c

/-- A retained rectangle with a side in the first block has both endpoint rows in that block. -/
theorem seamRetainedRectangle_endpoint_rows_le
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) :
    r.bottom.val ≤ n ∧ r.top.val ≤ n := by
  rcases hside with h | h
  · refine ⟨seamPairSector_row_le (seamState_mem_pairSector p.1 p.2) _ h, ?_⟩
    have hh := seamPairSector_row_le (seamState_mem_pairSector q.1 q.2) _ h
    simpa only [r.map_left, top_def] using hh
  · refine ⟨?_, seamPairSector_row_le (seamState_mem_pairSector p.1 p.2) _ h⟩
    have hh := seamPairSector_row_le (seamState_mem_pairSector q.1 q.2) _ h
    simpa only [r.map_right, bottom_def] using hh

theorem seamRetainedRectangle_left_recovery
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) :
    seamFirstFactorColumn p.2 (seamFirstFactorIndex r.left) = r.left :=
  seamFirstFactorColumn_index_of_row_le p.1 p.2 _
    (seamRetainedRectangle_endpoint_rows_le p q r hside).1

theorem seamRetainedRectangle_right_recovery
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) :
    seamFirstFactorColumn p.2 (seamFirstFactorIndex r.right) = r.right :=
  seamFirstFactorColumn_index_of_row_le p.1 p.2 _
    (seamRetainedRectangle_endpoint_rows_le p q r hside).2

/-- Project a retained rectangle with a first-block side to its first factor. -/
def seamRetainedFirstRectangle
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) : GridRectangleBetween p.1 q.1 where
  left := seamFirstFactorIndex r.left
  right := seamFirstFactorIndex r.right
  left_ne_right := by
    intro hh
    have hh := congrArg (seamFirstFactorColumn p.2) hh
    rw [seamRetainedRectangle_left_recovery p q r hside,
      seamRetainedRectangle_right_recovery p q r hside] at hh
    exact r.left_ne_right hh
  map_left := by
    apply seamLeft_injective (m := m)
    have hz := seamRetainedRectangle_second_eq_of_side_lt p q r hside
    have hvalue (a : Fin (n + 1)) :
        seamState q.1 q.2 (seamFirstFactorColumn p.2 a) = seamLeft n m (q.1 a) := by
      rw [← hz, seamState_firstFactorColumn]
    have hh := r.map_left
    rw [← seamRetainedRectangle_left_recovery p q r hside,
      ← seamRetainedRectangle_right_recovery p q r hside,
      hvalue, seamState_firstFactorColumn] at hh
    exact hh
  map_right := by
    apply seamLeft_injective (m := m)
    have hz := seamRetainedRectangle_second_eq_of_side_lt p q r hside
    have hvalue (a : Fin (n + 1)) :
        seamState q.1 q.2 (seamFirstFactorColumn p.2 a) = seamLeft n m (q.1 a) := by
      rw [← hz, seamState_firstFactorColumn]
    have hh := r.map_right
    rw [← seamRetainedRectangle_left_recovery p q r hside,
      ← seamRetainedRectangle_right_recovery p q r hside,
      hvalue, seamState_firstFactorColumn] at hh
    exact hh
  map_of_ne c hl hr := by
    apply seamLeft_injective (m := m)
    have hz := seamRetainedRectangle_second_eq_of_side_lt p q r hside
    have hcL : seamFirstFactorColumn p.2 c ≠ r.left := by
      rw [← seamRetainedRectangle_left_recovery p q r hside]
      exact fun hh => hl (seamFirstFactorColumn_injective _ hh)
    have hcR : seamFirstFactorColumn p.2 c ≠ r.right := by
      rw [← seamRetainedRectangle_right_recovery p q r hside]
      exact fun hh => hr (seamFirstFactorColumn_injective _ hh)
    have hh := r.map_of_ne (seamFirstFactorColumn p.2 c) hcL hcR
    rw [← hz, seamState_firstFactorColumn, seamState_firstFactorColumn] at hh
    exact hh

@[simp] theorem seamRetainedFirstRectangle_left
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) :
    (seamRetainedFirstRectangle p q r hside).left = seamFirstFactorIndex r.left := rfl

@[simp] theorem seamRetainedFirstRectangle_right
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) :
    (seamRetainedFirstRectangle p q r hside).right = seamFirstFactorIndex r.right := rfl

@[simp] theorem seamRetainedFirstRectangle_bottom_recovery
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) :
    seamLeft n m (seamRetainedFirstRectangle p q r hside).bottom = r.bottom := by
  rw [bottom_def, seamRetainedFirstRectangle_left, ← seamState_firstFactorColumn p.1 p.2,
    seamRetainedRectangle_left_recovery p q r hside, bottom_def]

@[simp] theorem seamRetainedFirstRectangle_top_recovery
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) :
    seamLeft n m (seamRetainedFirstRectangle p q r hside).top = r.top := by
  rw [top_def, seamRetainedFirstRectangle_right, ← seamState_firstFactorColumn p.1 p.2,
    seamRetainedRectangle_right_recovery p q r hside, top_def]

/-- Projecting a retained empty rectangle preserves emptiness, including wrapping intervals. -/
theorem seamRetainedFirstRectangle_isEmpty
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) (he : r.IsEmpty) :
    (seamRetainedFirstRectangle p q r hside).IsEmpty := by
  apply (isEmpty_iff_forall_notMem_cIoo _).mpr
  intro a ha hrow
  have hcol : seamFirstFactorColumn p.2 a ∈ Grid.cIoo r.left r.right := by
    rw [← seamRetainedRectangle_left_recovery p q r hside,
      ← seamRetainedRectangle_right_recovery p q r hside,
      seamFirstFactorColumn_mem_cIoo_iff]
    exact ha
  have hv : seamState p.1 p.2 (seamFirstFactorColumn p.2 a) ∈
      Grid.cIoo r.bottom r.top := by
    rw [seamState_firstFactorColumn,
      ← seamRetainedFirstRectangle_bottom_recovery p q r hside,
      ← seamRetainedFirstRectangle_top_recovery p q r hside,
      seamLeft_mem_cIoo_iff]
    exact hrow
  exact (isEmpty_iff_forall_notMem_cIoo r).mp he _ hcol hv

/-- The projection is injective on rectangles with a first-block side. -/
theorem seamRetainedFirstRectangle_injective
    (p q : GridState (n + 1) × GridState (m + 1))
    (r s : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hr : r.left.val < n ∨ r.right.val < n)
    (hs : s.left.val < n ∨ s.right.val < n)
    (h : seamRetainedFirstRectangle p q r hr = seamRetainedFirstRectangle p q s hs) : r = s := by
  apply GridRectangleBetween.ext
  · have hh := congrArg (fun t => seamFirstFactorColumn p.2 t.left) h
    simpa only [seamRetainedFirstRectangle_left,
      seamRetainedRectangle_left_recovery p q r hr,
      seamRetainedRectangle_left_recovery p q s hs] using hh
  · have hh := congrArg (fun t => seamFirstFactorColumn p.2 t.right) h
    simpa only [seamRetainedFirstRectangle_right,
      seamRetainedRectangle_right_recovery p q r hr,
      seamRetainedRectangle_right_recovery p q s hs] using hh

/-- If the first factor changes, every retained rectangle has a side strictly before the seam. -/
theorem seamRetainedRectangle_side_lt_of_first_ne
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hne : p.1 ≠ q.1) : r.left.val < n ∨ r.right.val < n := by
  by_contra h
  exact hne (seamRetainedRectangle_first_eq_of_sides_ge p q r (by omega) (by omega))

/-- An empty retained rectangle changing the first factor has an empty first-factor projection. -/
theorem seamRetainedFirstRectangle_isEmpty_of_first_ne
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hne : p.1 ≠ q.1) (he : r.IsEmpty) :
    (seamRetainedFirstRectangle p q r
      (seamRetainedRectangle_side_lt_of_first_ne p q r hne)).IsEmpty :=
  seamRetainedFirstRectangle_isEmpty p q r _ he

end OnLeConjecture.KnotFloer.GridFull
