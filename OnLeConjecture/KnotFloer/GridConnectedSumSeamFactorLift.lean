/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamRetainedProjection

/-!
# Candidate lifts of first-factor rectangles

The increasing first-factor column embedding lifts any factor rectangle
to a retained rectangle. The lift has an interior state point precisely
when one comes from the factor rectangle or from a nonzero row of the
second factor. The latter obstruction occurs only for a wrapping row
interval, with its second-block column in the lifted column interior.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A first-factor embedded column lies strictly before n exactly when it is not the last column. -/
theorem seamFirstFactorColumn_lt_cut_iff (z : GridState (m + 1)) (a : Fin (n + 1)) :
    (seamFirstFactorColumn z a).val < n ↔ a ≠ Fin.last n := by
  induction a using Fin.lastCases with
  | last =>
    rw [seamFirstFactorColumn_last]
    constructor
    · intro h
      change n + (z.toPerm.symm 0).val < n at h
      omega
    · intro h
      exact False.elim (h rfl)
  | cast a =>
    constructor
    · intro _
      exact Fin.castSucc_ne_last a
    · intro _
      simpa only [seamFirstFactorColumn_castSucc, seamLeft_val, Fin.val_castSucc] using a.isLt

/-- Every column comes from the first-factor embedding or a nonzero second-factor row. -/
theorem seamFirstFactorColumn_or_right_nonzero (z : GridState (m + 1))
    (c : Fin (n + m + 1)) :
    (∃ a, c = seamFirstFactorColumn z a) ∨
      ∃ d : Fin (m + 1), c = seamRight n m d ∧ z d ≠ 0 := by
  by_cases hc : c.val < n
  · let a : Fin n := ⟨c.val, hc⟩
    exact Or.inl ⟨a.castSucc, by rw [seamFirstFactorColumn_castSucc]; exact Fin.ext rfl⟩
  · let d : Fin (m + 1) := ⟨c.val - n, by have := c.isLt; omega⟩
    have hd : seamRight n m d = c := by
      apply Fin.ext
      change n + (c.val - n) = c.val
      omega
    by_cases hz : z d = 0
    · have hz' : z.toPerm.symm 0 = d := z.toPerm.symm_apply_eq.mpr hz.symm
      exact Or.inl ⟨Fin.last n, by rw [seamFirstFactorColumn_last, hz', hd]⟩
    · exact Or.inr ⟨d, hd.symm, hz⟩

/-- The unique candidate retained rectangle with the prescribed first-factor projection. -/
def seamFirstFactorRectangle {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    GridRectangleBetween (seamState x z) (seamState y z) where
  left := seamFirstFactorColumn z r.left
  right := seamFirstFactorColumn z r.right
  left_ne_right := fun h => r.left_ne_right (seamFirstFactorColumn_injective z h)
  map_left := by rw [seamState_firstFactorColumn, seamState_firstFactorColumn, r.map_left]
  map_right := by rw [seamState_firstFactorColumn, seamState_firstFactorColumn, r.map_right]
  map_of_ne c hl hr := by
    rcases seamFirstFactorColumn_or_right_nonzero z c with ⟨a, rfl⟩ | ⟨d, rfl, hd⟩
    · rw [seamState_firstFactorColumn, seamState_firstFactorColumn,
        r.map_of_ne a (fun h => hl (congrArg (seamFirstFactorColumn z) h))
          (fun h => hr (congrArg (seamFirstFactorColumn z) h))]
    · rw [seamState_right_of_ne_zero _ _ _ hd, seamState_right_of_ne_zero _ _ _ hd]

@[simp] theorem seamFirstFactorRectangle_left {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (seamFirstFactorRectangle r z).left = seamFirstFactorColumn z r.left := rfl

@[simp] theorem seamFirstFactorRectangle_right {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (seamFirstFactorRectangle r z).right = seamFirstFactorColumn z r.right := rfl

@[simp] theorem seamFirstFactorRectangle_bottom {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (seamFirstFactorRectangle r z).bottom = seamLeft n m r.bottom := by
  rw [bottom_def, seamFirstFactorRectangle_left, seamState_firstFactorColumn, bottom_def]

@[simp] theorem seamFirstFactorRectangle_top {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (seamFirstFactorRectangle r z).top = seamLeft n m r.top := by
  rw [top_def, seamFirstFactorRectangle_right, seamState_firstFactorColumn, top_def]

theorem seamFirstFactorRectangle_side_lt {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (seamFirstFactorRectangle r z).left.val < n ∨
      (seamFirstFactorRectangle r z).right.val < n := by
  simp only [seamFirstFactorRectangle_left, seamFirstFactorRectangle_right,
    seamFirstFactorColumn_lt_cut_iff]
  by_contra hh
  push Not at hh
  exact r.left_ne_right (hh.1.trans hh.2.symm)

/-- Projecting the candidate lift recovers the original factor rectangle. -/
@[simp] theorem seamFirstFactorRectangle_project {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    seamRetainedFirstRectangle (x, z) (y, z) (seamFirstFactorRectangle r z)
      (seamFirstFactorRectangle_side_lt r z) = r := by
  apply GridRectangleBetween.ext <;>
    simp only [seamRetainedFirstRectangle_left, seamRetainedFirstRectangle_right,
      seamFirstFactorRectangle_left, seamFirstFactorRectangle_right, seamFirstFactorIndex_column]

/-- Emptiness of the candidate is equivalent to factor emptiness and the explicit extra points. -/
theorem seamFirstFactorRectangle_isEmpty_iff_raw {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (seamFirstFactorRectangle r z).IsEmpty ↔ r.IsEmpty ∧
      ∀ d : Fin (m + 1), z d ≠ 0 →
        seamRight n m d ∈ Grid.cIoo (seamFirstFactorColumn z r.left)
          (seamFirstFactorColumn z r.right) →
        seamRight n m (z d) ∉ Grid.cIoo (seamLeft n m r.bottom) (seamLeft n m r.top) := by
  constructor
  · intro he
    have hproj := seamRetainedFirstRectangle_isEmpty (x, z) (y, z)
      (seamFirstFactorRectangle r z) (seamFirstFactorRectangle_side_lt r z) he
    rw [seamFirstFactorRectangle_project] at hproj
    refine ⟨hproj, ?_⟩
    intro d hd hc
    have hh := (isEmpty_iff_forall_notMem_cIoo _).mp he (seamRight n m d) hc
    simpa only [seamState_right_of_ne_zero x z d hd,
      seamFirstFactorRectangle_bottom, seamFirstFactorRectangle_top] using hh
  · rintro ⟨he, hother⟩
    apply (isEmpty_iff_forall_notMem_cIoo _).mpr
    intro c hc hrow
    rcases seamFirstFactorColumn_or_right_nonzero z c with ⟨a, rfl⟩ | ⟨d, rfl, hd⟩
    · simp only [seamFirstFactorRectangle_left, seamFirstFactorRectangle_right,
        seamFirstFactorColumn_mem_cIoo_iff] at hc
      simp only [seamState_firstFactorColumn, seamFirstFactorRectangle_bottom,
        seamFirstFactorRectangle_top, seamLeft_mem_cIoo_iff] at hrow
      exact (isEmpty_iff_forall_notMem_cIoo r).mp he a hc hrow
    · apply hother d hd hc
      simpa only [seamState_right_of_ne_zero x z d hd,
        seamFirstFactorRectangle_bottom, seamFirstFactorRectangle_top] using hrow

set_option backward.isDefEq.respectTransparency false in
/-- A second-factor nonzero row is inside a first-block row interval exactly when it wraps. -/
theorem seamRight_nonzero_mem_first_rows_iff
    (a b : Fin (n + 1)) (hab : a ≠ b) (d : Fin (m + 1)) (hd : d ≠ 0) :
    seamRight n m d ∈ Grid.cIoo (seamLeft n m a) (seamLeft n m b) ↔ b.val < a.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hdv : d.val ≠ 0 := fun hh => hd (Fin.ext hh)
  have habv : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
  constructor
  · intro hh
    obtain ⟨_, hi⟩ := (Grid.mem_cIoo _ _ _).mp hh
    simp only [seamLeft_val, seamRight_val] at hi
    by_contra hba
    have hablt : a.val < b.val := by omega
    rw [if_pos hablt] at hi
    omega
  · intro hba
    apply (Grid.mem_cIoo _ _ _).mpr
    refine ⟨fun hh => hab (seamLeft_injective hh), ?_⟩
    simp only [seamLeft_val, seamRight_val]
    rw [if_neg (by omega)]
    exact Or.inl (by omega)

/-- The extra-point obstruction is exactly a wrapping row interval crossing a nonzero second row. -/
theorem seamFirstFactorRectangle_isEmpty_iff {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (seamFirstFactorRectangle r z).IsEmpty ↔ r.IsEmpty ∧
      (r.top.val < r.bottom.val → ∀ d : Fin (m + 1), z d ≠ 0 →
        seamRight n m d ∉ Grid.cIoo (seamFirstFactorColumn z r.left)
          (seamFirstFactorColumn z r.right)) := by
  rw [seamFirstFactorRectangle_isEmpty_iff_raw]
  constructor
  · rintro ⟨he, hh⟩
    refine ⟨he, ?_⟩
    intro hwrap d hd hc
    exact hh d hd hc ((seamRight_nonzero_mem_first_rows_iff _ _ r.bottom_ne_top _ hd).mpr hwrap)
  · rintro ⟨he, hh⟩
    refine ⟨he, ?_⟩
    intro d hd hc hrow
    exact hh ((seamRight_nonzero_mem_first_rows_iff _ _ r.bottom_ne_top _ hd).mp hrow) d hd hc

/-- A nonwrapping row interval creates no extra second-block interior point. -/
theorem seamFirstFactorRectangle_isEmpty_iff_of_rows_increasing {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (hrows : r.bottom.val < r.top.val) :
    (seamFirstFactorRectangle r z).IsEmpty ↔ r.IsEmpty := by
  rw [seamFirstFactorRectangle_isEmpty_iff]
  simp only [show ¬ r.top.val < r.bottom.val by omega, false_implies, and_true]

/-- For an empty factor rectangle, failure of the lift is exactly a specified second-block point. -/
theorem seamFirstFactorRectangle_not_isEmpty_iff {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (he : r.IsEmpty) :
    ¬ (seamFirstFactorRectangle r z).IsEmpty ↔ r.top.val < r.bottom.val ∧
      ∃ d : Fin (m + 1), z d ≠ 0 ∧
        seamRight n m d ∈ Grid.cIoo (seamFirstFactorColumn z r.left)
          (seamFirstFactorColumn z r.right) := by
  classical
  rw [seamFirstFactorRectangle_isEmpty_iff]
  simp only [he, true_and, not_forall, not_not, exists_prop]

/-- Lifting a projected retained rectangle with fixed second factor recovers the rectangle. -/
@[simp] theorem seamFirstFactorRectangle_lift_project {x y : GridState (n + 1)}
    (z : GridState (m + 1))
    (s : GridRectangleBetween (seamState x z) (seamState y z))
    (hs : s.left.val < n ∨ s.right.val < n) :
    seamFirstFactorRectangle (seamRetainedFirstRectangle (x, z) (y, z) s hs) z = s := by
  apply GridRectangleBetween.ext
  · simp only [seamFirstFactorRectangle_left, seamRetainedFirstRectangle_left,
      seamRetainedRectangle_left_recovery (x, z) (y, z) s hs]
  · simp only [seamFirstFactorRectangle_right, seamRetainedFirstRectangle_right,
      seamRetainedRectangle_right_recovery (x, z) (y, z) s hs]

/-- An empty direct preimage exists exactly when the unique candidate lift is empty. -/
theorem seamFirstFactorRectangle_empty_preimage_iff {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (∃ s : GridRectangleBetween (seamState x z) (seamState y z),
      ∃ hs : s.left.val < n ∨ s.right.val < n,
        s.IsEmpty ∧ seamRetainedFirstRectangle (x, z) (y, z) s hs = r) ↔
      (seamFirstFactorRectangle r z).IsEmpty := by
  constructor
  · rintro ⟨s, hs, he, hproj⟩
    have hh := congrArg (fun a => seamFirstFactorRectangle a z) hproj
    rw [seamFirstFactorRectangle_lift_project] at hh
    exact hh ▸ he
  · intro he
    exact ⟨seamFirstFactorRectangle r z, seamFirstFactorRectangle_side_lt r z,
      he, seamFirstFactorRectangle_project r z⟩

/-- Exact image criterion for the direct first-factor projection. -/
theorem seamFirstFactorRectangle_empty_preimage_iff_no_obstruction {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) :
    (∃ s : GridRectangleBetween (seamState x z) (seamState y z),
      ∃ hs : s.left.val < n ∨ s.right.val < n,
        s.IsEmpty ∧ seamRetainedFirstRectangle (x, z) (y, z) s hs = r) ↔
      r.IsEmpty ∧ (r.top.val < r.bottom.val → ∀ d : Fin (m + 1), z d ≠ 0 →
        seamRight n m d ∉ Grid.cIoo (seamFirstFactorColumn z r.left)
          (seamFirstFactorColumn z r.right)) := by
  rw [seamFirstFactorRectangle_empty_preimage_iff, seamFirstFactorRectangle_isEmpty_iff]

end OnLeConjecture.KnotFloer.GridFull
