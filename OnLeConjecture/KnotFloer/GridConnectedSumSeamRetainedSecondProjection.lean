/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamRetainedProjection

/-!
# Projecting retained rectangles to the second factor

The zero row of the second factor is placed at the last row value of the
first state. This increasing row embedding and the second-block column
embedding recover rectangles whose two side columns are at least n.
Emptiness passes to this projection, without a converse lifting claim.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The second-factor rows, placing its zero row at the last row value of the first state. -/
def seamSecondFactorRow (x : GridState (n + 1)) (b : Fin (m + 1)) : Fin (n + m + 1) :=
  if b = 0 then seamLeft n m (x (Fin.last n)) else seamRight n m b

@[simp] theorem seamSecondFactorRow_zero (x : GridState (n + 1)) :
    seamSecondFactorRow (m := m) x 0 = seamLeft n m (x (Fin.last n)) := by
  simp only [seamSecondFactorRow, ite_true]

@[simp] theorem seamSecondFactorRow_of_ne_zero (x : GridState (n + 1))
    (b : Fin (m + 1)) (hb : b ≠ 0) : seamSecondFactorRow x b = seamRight n m b := by
  simp only [seamSecondFactorRow, if_neg hb]

theorem seamSecondFactorRow_strictMono (x : GridState (n + 1)) :
    StrictMono (seamSecondFactorRow (m := m) x) := by
  intro a b hab
  have hb : b ≠ 0 := by
    intro hh
    rw [hh] at hab
    exact (not_lt_of_ge (Fin.zero_le a)) hab
  rw [seamSecondFactorRow_of_ne_zero x b hb]
  by_cases ha : a = 0
  · rw [ha, seamSecondFactorRow_zero]
    change (x (Fin.last n)).val < n + b.val
    have hx := (x (Fin.last n)).isLt
    have hbn : b.val ≠ 0 := fun h => hb (Fin.ext h)
    omega
  · rw [seamSecondFactorRow_of_ne_zero x a ha]
    change n + a.val < n + b.val
    exact Nat.add_lt_add_left hab n

theorem seamSecondFactorRow_injective (x : GridState (n + 1)) :
    Function.Injective (seamSecondFactorRow (m := m) x) :=
  (seamSecondFactorRow_strictMono x).injective

/-- Second-block state values are the increasing row embedding of the second factor. -/
@[simp] theorem seamState_secondFactorRow (x : GridState (n + 1))
    (z : GridState (m + 1)) (d : Fin (m + 1)) :
    seamState x z (seamRight n m d) = seamSecondFactorRow x (z d) := by
  by_cases hd : z d = 0
  · rw [seamState_right_of_zero x z d hd, hd, seamSecondFactorRow_zero]
  · rw [seamState_right_of_ne_zero x z d hd, seamSecondFactorRow_of_ne_zero x _ hd]

private theorem strictMono_mem_cIoo_iff {k l : ℕ} (f : Fin k → Fin l) (hf : StrictMono f)
    (a b c : Fin k) : f c ∈ Grid.cIoo (f a) (f b) ↔ c ∈ Grid.cIoo a b := by
  simp only [Grid.mem_cIoo, ← Fin.lt_def, hf.lt_iff_lt, hf.injective.ne_iff]

@[simp] theorem seamSecondFactorRow_mem_cIoo_iff (x : GridState (n + 1))
    (a b c : Fin (m + 1)) :
    seamSecondFactorRow x c ∈ Grid.cIoo (seamSecondFactorRow x a)
      (seamSecondFactorRow x b) ↔ c ∈ Grid.cIoo a b :=
  strictMono_mem_cIoo_iff _ (seamSecondFactorRow_strictMono x) a b c

@[simp] theorem seamRight_mem_cIoo_iff (a b c : Fin (m + 1)) :
    seamRight n m c ∈ Grid.cIoo (seamRight n m a) (seamRight n m b) ↔ c ∈ Grid.cIoo a b := by
  apply strictMono_mem_cIoo_iff
  intro d e hde
  exact Nat.add_lt_add_left hde n

/-- The index of a column in the second block. -/
def seamSecondFactorIndex (c : Fin (n + m + 1)) (hc : n ≤ c.val) : Fin (m + 1) :=
  ⟨c.val - n, by have := c.isLt; omega⟩

@[simp] theorem seamRight_secondFactorIndex (c : Fin (n + m + 1)) (hc : n ≤ c.val) :
    seamRight n m (seamSecondFactorIndex c hc) = c := by
  apply Fin.ext
  change n + (c.val - n) = c.val
  omega

@[simp] theorem seamSecondFactorIndex_right (d : Fin (m + 1)) :
    seamSecondFactorIndex (seamRight n m d) (by simp only [seamRight_val]; omega) = d := by
  apply Fin.ext
  change (n + d.val) - n = d.val
  omega

/-- Project a retained rectangle with both side columns in the second block. -/
def seamRetainedSecondRectangle
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val) : GridRectangleBetween p.2 q.2 where
  left := seamSecondFactorIndex r.left hl
  right := seamSecondFactorIndex r.right hr
  left_ne_right := by
    intro hh
    have hh := congrArg (seamRight n m) hh
    rw [seamRight_secondFactorIndex, seamRight_secondFactorIndex] at hh
    exact r.left_ne_right hh
  map_left := by
    apply seamSecondFactorRow_injective p.1
    have hx := seamRetainedRectangle_first_eq_of_sides_ge p q r hl hr
    have hvalue (a : Fin (m + 1)) :
        seamState q.1 q.2 (seamRight n m a) = seamSecondFactorRow p.1 (q.2 a) := by
      rw [← hx, seamState_secondFactorRow]
    have hh := r.map_left
    rw [← seamRight_secondFactorIndex r.left hl, ← seamRight_secondFactorIndex r.right hr,
      hvalue, seamState_secondFactorRow] at hh
    exact hh
  map_right := by
    apply seamSecondFactorRow_injective p.1
    have hx := seamRetainedRectangle_first_eq_of_sides_ge p q r hl hr
    have hvalue (a : Fin (m + 1)) :
        seamState q.1 q.2 (seamRight n m a) = seamSecondFactorRow p.1 (q.2 a) := by
      rw [← hx, seamState_secondFactorRow]
    have hh := r.map_right
    rw [← seamRight_secondFactorIndex r.left hl, ← seamRight_secondFactorIndex r.right hr,
      hvalue, seamState_secondFactorRow] at hh
    exact hh
  map_of_ne c hcL hcR := by
    apply seamSecondFactorRow_injective p.1
    have hx := seamRetainedRectangle_first_eq_of_sides_ge p q r hl hr
    have hcl : seamRight n m c ≠ r.left := by
      rw [← seamRight_secondFactorIndex r.left hl]
      exact fun hh => hcL (seamRight_injective hh)
    have hcr : seamRight n m c ≠ r.right := by
      rw [← seamRight_secondFactorIndex r.right hr]
      exact fun hh => hcR (seamRight_injective hh)
    have hh := r.map_of_ne (seamRight n m c) hcl hcr
    rw [← hx, seamState_secondFactorRow, seamState_secondFactorRow] at hh
    exact hh

@[simp] theorem seamRetainedSecondRectangle_left
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val) :
    (seamRetainedSecondRectangle p q r hl hr).left = seamSecondFactorIndex r.left hl := rfl

@[simp] theorem seamRetainedSecondRectangle_right
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val) :
    (seamRetainedSecondRectangle p q r hl hr).right = seamSecondFactorIndex r.right hr := rfl

@[simp] theorem seamRetainedSecondRectangle_bottom_recovery
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val) :
    seamSecondFactorRow p.1 (seamRetainedSecondRectangle p q r hl hr).bottom = r.bottom := by
  rw [bottom_def, seamRetainedSecondRectangle_left, ← seamState_secondFactorRow p.1 p.2,
    seamRight_secondFactorIndex, bottom_def]

@[simp] theorem seamRetainedSecondRectangle_top_recovery
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val) :
    seamSecondFactorRow p.1 (seamRetainedSecondRectangle p q r hl hr).top = r.top := by
  rw [top_def, seamRetainedSecondRectangle_right, ← seamState_secondFactorRow p.1 p.2,
    seamRight_secondFactorIndex, top_def]

/-- Emptiness passes from the full retained rectangle to its second-factor projection. -/
theorem seamRetainedSecondRectangle_isEmpty
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val) (he : r.IsEmpty) :
    (seamRetainedSecondRectangle p q r hl hr).IsEmpty := by
  apply (isEmpty_iff_forall_notMem_cIoo _).mpr
  intro a ha hrow
  have hcol : seamRight n m a ∈ Grid.cIoo r.left r.right := by
    rw [← seamRight_secondFactorIndex r.left hl, ← seamRight_secondFactorIndex r.right hr,
      seamRight_mem_cIoo_iff]
    exact ha
  have hv : seamState p.1 p.2 (seamRight n m a) ∈ Grid.cIoo r.bottom r.top := by
    rw [seamState_secondFactorRow,
      ← seamRetainedSecondRectangle_bottom_recovery p q r hl hr,
      ← seamRetainedSecondRectangle_top_recovery p q r hl hr,
      seamSecondFactorRow_mem_cIoo_iff]
    exact hrow
  exact (isEmpty_iff_forall_notMem_cIoo r).mp he _ hcol hv

/-- The second-factor projection is injective on rectangles with both columns in that block. -/
theorem seamRetainedSecondRectangle_injective
    (p q : GridState (n + 1) × GridState (m + 1))
    (r s : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hrl : n ≤ r.left.val) (hrr : n ≤ r.right.val)
    (hsl : n ≤ s.left.val) (hsr : n ≤ s.right.val)
    (h : seamRetainedSecondRectangle p q r hrl hrr =
      seamRetainedSecondRectangle p q s hsl hsr) : r = s := by
  apply GridRectangleBetween.ext
  · have hh := congrArg (fun t => seamRight n m t.left) h
    simpa only [seamRetainedSecondRectangle_left, seamRight_secondFactorIndex] using hh
  · have hh := congrArg (fun t => seamRight n m t.right) h
    simpa only [seamRetainedSecondRectangle_right, seamRight_secondFactorIndex] using hh

/-- If the second factor changes, both rectangle sides lie in the second block. -/
theorem seamRetainedRectangle_sides_ge_of_second_ne
    (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hne : p.2 ≠ q.2) : n ≤ r.left.val ∧ n ≤ r.right.val := by
  have hn : ¬ (r.left.val < n ∨ r.right.val < n) :=
    fun h => hne (seamRetainedRectangle_second_eq_of_side_lt p q r h)
  omega

end OnLeConjecture.KnotFloer.GridFull
