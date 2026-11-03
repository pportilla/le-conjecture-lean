/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamRetainedSecondProjection

/-!
# Candidate lifts of second-factor rectangles

A second-factor rectangle with the first state fixed lifts through
seamRight on columns and seamSecondFactorRow on rows. Its projection
recovers the factor rectangle. Emptiness is equivalent to factor
emptiness and the absence of an interior state point in a column
strictly before the seam.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- Every column is either strictly before the seam or in the entire second block. -/
theorem seamColumn_cases_strict (c : Fin (n + m + 1)) :
    (∃ a : Fin n, c = seamLeft n m a.castSucc) ∨
      ∃ d : Fin (m + 1), c = seamRight n m d := by
  by_cases hc : c.val < n
  · exact Or.inl ⟨⟨c.val, hc⟩, Fin.ext rfl⟩
  · let d : Fin (m + 1) := ⟨c.val - n, by have := c.isLt; omega⟩
    refine Or.inr ⟨d, ?_⟩
    apply Fin.ext
    change c.val = n + (c.val - n)
    omega

/-- The candidate retained lift of a second-factor rectangle with fixed first state. -/
def seamSecondFactorRectangle (x : GridState (n + 1)) {z w : GridState (m + 1)}
    (r : GridRectangleBetween z w) :
    GridRectangleBetween (seamState x z) (seamState x w) where
  left := seamRight n m r.left
  right := seamRight n m r.right
  left_ne_right := fun h => r.left_ne_right (seamRight_injective h)
  map_left := by rw [seamState_secondFactorRow, seamState_secondFactorRow, r.map_left]
  map_right := by rw [seamState_secondFactorRow, seamState_secondFactorRow, r.map_right]
  map_of_ne c hl hr := by
    rcases seamColumn_cases_strict c with ⟨a, rfl⟩ | ⟨d, rfl⟩
    · rw [seamState_left_castSucc, seamState_left_castSucc]
    · rw [seamState_secondFactorRow, seamState_secondFactorRow,
        r.map_of_ne d (fun h => hl (congrArg (seamRight n m) h))
          (fun h => hr (congrArg (seamRight n m) h))]

@[simp] theorem seamSecondFactorRectangle_left (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    (seamSecondFactorRectangle x r).left = seamRight n m r.left := rfl

@[simp] theorem seamSecondFactorRectangle_right (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    (seamSecondFactorRectangle x r).right = seamRight n m r.right := rfl

@[simp] theorem seamSecondFactorRectangle_bottom (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    (seamSecondFactorRectangle x r).bottom = seamSecondFactorRow x r.bottom := by
  rw [bottom_def, seamSecondFactorRectangle_left, seamState_secondFactorRow, bottom_def]

@[simp] theorem seamSecondFactorRectangle_top (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    (seamSecondFactorRectangle x r).top = seamSecondFactorRow x r.top := by
  rw [top_def, seamSecondFactorRectangle_right, seamState_secondFactorRow, top_def]

theorem seamSecondFactorRectangle_sides_ge (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    n ≤ (seamSecondFactorRectangle x r).left.val ∧
      n ≤ (seamSecondFactorRectangle x r).right.val := by
  simp only [seamSecondFactorRectangle_left, seamSecondFactorRectangle_right, seamRight_val]
  omega

/-- The second-factor projection of its candidate lift is the original rectangle. -/
@[simp] theorem seamSecondFactorRectangle_project (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    seamRetainedSecondRectangle (x, z) (x, w) (seamSecondFactorRectangle x r)
      (seamSecondFactorRectangle_sides_ge x r).1
      (seamSecondFactorRectangle_sides_ge x r).2 = r := by
  apply GridRectangleBetween.ext <;>
    simp only [seamRetainedSecondRectangle_left, seamRetainedSecondRectangle_right,
      seamSecondFactorRectangle_left, seamSecondFactorRectangle_right, seamSecondFactorIndex_right]

/-- The exact additional obstruction to emptiness consists of the first-block state points. -/
theorem seamSecondFactorRectangle_isEmpty_iff_raw (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    (seamSecondFactorRectangle x r).IsEmpty ↔ r.IsEmpty ∧
      ∀ c : Fin n, seamLeft n m c.castSucc ∈ Grid.cIoo
        (seamRight n m r.left) (seamRight n m r.right) →
        seamLeft n m (x c.castSucc) ∉ Grid.cIoo
          (seamSecondFactorRow x r.bottom) (seamSecondFactorRow x r.top) := by
  constructor
  · intro he
    have hproj := seamRetainedSecondRectangle_isEmpty (x, z) (x, w)
      (seamSecondFactorRectangle x r) (seamSecondFactorRectangle_sides_ge x r).1
      (seamSecondFactorRectangle_sides_ge x r).2 he
    rw [seamSecondFactorRectangle_project] at hproj
    refine ⟨hproj, ?_⟩
    intro c hc
    have hh := (isEmpty_iff_forall_notMem_cIoo _).mp he (seamLeft n m c.castSucc) hc
    simpa only [seamState_left_castSucc,
      seamSecondFactorRectangle_bottom, seamSecondFactorRectangle_top] using hh
  · rintro ⟨he, hother⟩
    apply (isEmpty_iff_forall_notMem_cIoo _).mpr
    intro c hc hrow
    rcases seamColumn_cases_strict c with ⟨a, rfl⟩ | ⟨d, rfl⟩
    · apply hother a hc
      simpa only [seamState_left_castSucc,
        seamSecondFactorRectangle_bottom, seamSecondFactorRectangle_top] using hrow
    · simp only [seamSecondFactorRectangle_left, seamSecondFactorRectangle_right,
        seamRight_mem_cIoo_iff] at hc
      simp only [seamState_secondFactorRow, seamSecondFactorRectangle_bottom,
        seamSecondFactorRectangle_top, seamSecondFactorRow_mem_cIoo_iff] at hrow
      exact (isEmpty_iff_forall_notMem_cIoo r).mp he d hc hrow

/-- For an empty factor rectangle, a nonempty lift has a specified first-block interior point. -/
theorem seamSecondFactorRectangle_not_isEmpty_iff (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty) :
    ¬ (seamSecondFactorRectangle x r).IsEmpty ↔ ∃ c : Fin n,
      seamLeft n m c.castSucc ∈ Grid.cIoo (seamRight n m r.left) (seamRight n m r.right) ∧
      seamLeft n m (x c.castSucc) ∈ Grid.cIoo
        (seamSecondFactorRow x r.bottom) (seamSecondFactorRow x r.top) := by
  classical
  rw [seamSecondFactorRectangle_isEmpty_iff_raw]
  simp only [he, true_and, not_forall, not_not, exists_prop]

/-- Lifting the second-factor projection of a retained rectangle recovers that rectangle. -/
@[simp] theorem seamSecondFactorRectangle_lift_project (x : GridState (n + 1))
    {z w : GridState (m + 1)}
    (s : GridRectangleBetween (seamState x z) (seamState x w))
    (hl : n ≤ s.left.val) (hr : n ≤ s.right.val) :
    seamSecondFactorRectangle x (seamRetainedSecondRectangle (x, z) (x, w) s hl hr) = s := by
  apply GridRectangleBetween.ext <;>
    simp only [seamSecondFactorRectangle_left, seamSecondFactorRectangle_right,
      seamRetainedSecondRectangle_left, seamRetainedSecondRectangle_right,
      seamRight_secondFactorIndex]

/-- An empty direct preimage exists exactly when the candidate second-factor lift is empty. -/
theorem seamSecondFactorRectangle_empty_preimage_iff (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    (∃ s : GridRectangleBetween (seamState x z) (seamState x w),
      ∃ hl : n ≤ s.left.val, ∃ hr : n ≤ s.right.val,
        s.IsEmpty ∧ seamRetainedSecondRectangle (x, z) (x, w) s hl hr = r) ↔
      (seamSecondFactorRectangle x r).IsEmpty := by
  constructor
  · rintro ⟨s, hl, hr, he, hproj⟩
    have hh := congrArg (fun a => seamSecondFactorRectangle x a) hproj
    rw [seamSecondFactorRectangle_lift_project] at hh
    exact hh ▸ he
  · intro he
    exact ⟨seamSecondFactorRectangle x r,
      (seamSecondFactorRectangle_sides_ge x r).1,
      (seamSecondFactorRectangle_sides_ge x r).2,
      he, seamSecondFactorRectangle_project x r⟩

/-- Exact criterion for the image of the direct second-factor projection. -/
theorem seamSecondFactorRectangle_empty_preimage_iff_no_obstruction (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) :
    (∃ s : GridRectangleBetween (seamState x z) (seamState x w),
      ∃ hl : n ≤ s.left.val, ∃ hr : n ≤ s.right.val,
        s.IsEmpty ∧ seamRetainedSecondRectangle (x, z) (x, w) s hl hr = r) ↔
      r.IsEmpty ∧ ∀ c : Fin n,
        seamLeft n m c.castSucc ∈ Grid.cIoo (seamRight n m r.left) (seamRight n m r.right) →
        seamLeft n m (x c.castSucc) ∉ Grid.cIoo
          (seamSecondFactorRow x r.bottom) (seamSecondFactorRow x r.top) := by
  rw [seamSecondFactorRectangle_empty_preimage_iff, seamSecondFactorRectangle_isEmpty_iff_raw]

end OnLeConjecture.KnotFloer.GridFull
