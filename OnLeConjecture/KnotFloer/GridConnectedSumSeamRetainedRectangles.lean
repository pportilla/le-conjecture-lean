/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamEntryExit

/-!
# Direct rectangles between retained seam states

A rectangle can change only one factor. Rectangles with both side columns
in the second block fix the first factor. Every rectangle having a side
strictly in the first block fixes the second factor. No emptiness or
marking hypothesis is needed for this restriction.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

theorem seamState_right_eq_factor (x y : GridState (n + 1))
    (z w : GridState (m + 1)) (d : Fin (m + 1))
    (h : seamState x z (seamRight n m d) = seamState y w (seamRight n m d)) : z d = w d := by
  by_cases hz : z d = 0
  · have hl := (seamState_right_row_le_iff x z d).mpr hz
    rw [h] at hl
    exact hz.trans ((seamState_right_row_le_iff y w d).mp hl).symm
  · have hw : w d ≠ 0 := by
      intro hw
      have hl := (seamState_right_row_le_iff y w d).mpr hw
      rw [← h] at hl
      exact hz ((seamState_right_row_le_iff x z d).mp hl)
    rw [seamState_right_of_ne_zero _ _ _ hz, seamState_right_of_ne_zero _ _ _ hw] at h
    exact seamRight_injective h

theorem seamRetainedRectangle_first_eq_of_sides_ge (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val) : p.1 = q.1 := by
  apply seam_gridState_eq_of_castSucc
  intro c
  have hcL : seamLeft n m c.castSucc ≠ r.left := by
    intro h
    have he := congrArg Fin.val h
    simp only [seamLeft_val, Fin.val_castSucc] at he
    omega
  have hcR : seamLeft n m c.castSucc ≠ r.right := by
    intro h
    have he := congrArg Fin.val h
    simp only [seamLeft_val, Fin.val_castSucc] at he
    omega
  have h := r.map_of_ne (seamLeft n m c.castSucc) hcL hcR
  rw [seamState_left_castSucc, seamState_left_castSucc] at h
  exact (seamLeft_injective h).symm

theorem seamRetainedRectangle_second_eq_of_side_lt (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2))
    (hside : r.left.val < n ∨ r.right.val < n) : p.2 = q.2 := by
  apply GridState.ext
  intro d
  let c := seamRight n m d
  have hc : n ≤ c.val := by simp only [c, seamRight_val]; omega
  by_cases hL : c = r.left
  · have hright : r.right.val < n := by
      have h := congrArg Fin.val hL
      omega
    have hs := seamPairSector_row_le (seamState_mem_pairSector p.1 p.2) r.right hright
    have ht := seamPairSector_row_le (seamState_mem_pairSector q.1 q.2) r.right hright
    have hp : (seamState p.1 p.2 c).val ≤ n := by rw [hL, ← r.map_right]; exact ht
    have hq : (seamState q.1 q.2 c).val ≤ n := by rw [hL, r.map_left]; exact hs
    exact ((seamState_right_row_le_iff p.1 p.2 d).mp hp).trans
      ((seamState_right_row_le_iff q.1 q.2 d).mp hq).symm
  · by_cases hR : c = r.right
    · have hleft : r.left.val < n := by
        have h := congrArg Fin.val hR
        omega
      have hs := seamPairSector_row_le (seamState_mem_pairSector p.1 p.2) r.left hleft
      have ht := seamPairSector_row_le (seamState_mem_pairSector q.1 q.2) r.left hleft
      have hp : (seamState p.1 p.2 c).val ≤ n := by rw [hR, ← r.map_left]; exact ht
      have hq : (seamState q.1 q.2 c).val ≤ n := by rw [hR, r.map_right]; exact hs
      exact ((seamState_right_row_le_iff p.1 p.2 d).mp hp).trans
        ((seamState_right_row_le_iff q.1 q.2 d).mp hq).symm
    · exact (seamState_right_eq_factor q.1 p.1 q.2 p.2 d (r.map_of_ne c hL hR)).symm

/-- A direct rectangle between pair states never changes both factors. -/
theorem seamRetainedRectangle_factor_eq (p q : GridState (n + 1) × GridState (m + 1))
    (r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2)) :
    p.1 = q.1 ∨ p.2 = q.2 := by
  by_cases hside : r.left.val < n ∨ r.right.val < n
  · exact Or.inr (seamRetainedRectangle_second_eq_of_side_lt p q r hside)
  · exact Or.inl (seamRetainedRectangle_first_eq_of_sides_ge p q r (by omega) (by omega))

theorem seamRetainedRectangle_isEmpty_of_factor_ne (p q : GridState (n + 1) × GridState (m + 1))
    (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) :
    IsEmpty (GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2)) :=
  ⟨fun r => (seamRetainedRectangle_factor_eq p q r).elim h₁ h₂⟩

theorem seamRetained_emptyRectangles_eq_empty (p q : GridState (n + 1) × GridState (m + 1))
    (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) :
    emptyRectangles (seamState p.1 p.2) (seamState q.1 q.2) = ∅ := by
  have := seamRetainedRectangle_isEmpty_of_factor_ne p q h₁ h₂
  exact Finset.eq_empty_of_isEmpty _

end OnLeConjecture.KnotFloer.GridFull
