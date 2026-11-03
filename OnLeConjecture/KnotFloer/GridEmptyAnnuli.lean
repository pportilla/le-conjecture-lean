/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridComplex

/-!
# Returning pairs of empty grid rectangles

A returning pair of empty rectangles covers one row or one column of squares. This is the
geometric input for the diagonal terms of the full rectangle differential, which allows
rectangles containing X markings.

The proof uses the cyclic interval and annular-domain lemmas of the attributed TauCeti port.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open TauCeti

namespace GridEmptyAnnuli

variable {n : ℕ} {x y : GridState n}

/-- If both returning rectangles are empty and their column arcs agree, that arc has no
interior column. -/
theorem columnInterior_eq_empty (R : GridRectangleBetween x y)
    (S : GridRectangleBetween y x) (hR : R.IsEmpty) (hS : S.IsEmpty)
    (hleft : S.left = R.left) : Grid.cIoo R.left R.right = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hcL := Grid.ne_left_of_mem_cIoo hc
  have hcR := Grid.ne_right_of_mem_cIoo hc
  have hxL : x c ≠ R.bottom := x.toPerm.injective.ne hcL
  have hxR : x c ≠ R.top := x.toPerm.injective.ne hcR
  have hout := (R.isEmpty_iff_forall_notMem_cIoo.mp hR) c hc
  have hin := Grid.mem_cIoo_swap_of_notMem R.bottom_ne_top hxL hxR hout
  have hSc : c ∈ Grid.cIoo S.left S.right := by
    rwa [hleft, R.right_eq_right_of_left_eq_left S hleft]
  have hSout := (S.isEmpty_iff_forall_notMem_cIoo.mp hS) c hSc
  rw [R.bottom_eq_top_of_left_eq_left S hleft,
    R.top_eq_bottom_of_left_eq_left S hleft, R.map_of_ne c hcL hcR] at hSout
  exact hSout hin

/-- An empty returning pair with equal column arcs covers exactly one column of squares. -/
theorem coveredColumns_eq_singleton (R : GridRectangleBetween x y)
    (S : GridRectangleBetween y x) (hR : R.IsEmpty) (hS : S.IsEmpty)
    (hleft : S.left = R.left) : R.toGridRectangle.coveredColumns = {R.left} := by
  change Grid.cIco R.left R.right = {R.left}
  rw [Grid.cIco_of_ne R.left_ne_right, columnInterior_eq_empty R S hR hS hleft]
  rfl

/-- The column sides of an empty vertical returning annulus are cyclically consecutive. -/
theorem right_eq_finRotate_left (R : GridRectangleBetween x y)
    (S : GridRectangleBetween y x) (hR : R.IsEmpty) (hS : S.IsEmpty)
    (hleft : S.left = R.left) : R.right = finRotate n R.left :=
  (Grid.cIco_eq_singleton_iff.mp (coveredColumns_eq_singleton R S hR hS hleft)).2.1

/-- An empty returning pair with complementary column arcs covers one row of squares. -/
theorem coveredRows_eq_singleton (R : GridRectangleBetween x y)
    (S : GridRectangleBetween y x) (hR : R.IsEmpty) (hS : S.IsEmpty)
    (hleft : S.left = R.right) : R.toGridRectangle.coveredRows = {R.bottom} := by
  have h := coveredColumns_eq_singleton R.transpose S.transpose
    ((R.isEmpty_transpose).mpr hR) ((S.isEmpty_transpose).mpr hS)
    (R.bottom_eq_bottom_of_left_eq_right S hleft)
  exact h

/-- Every returning pair of empty rectangles covers a single full row or a single full column. -/
theorem coveredSquares_union (R : GridRectangleBetween x y)
    (S : GridRectangleBetween y x) (hR : R.IsEmpty) (hS : S.IsEmpty) :
    R.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
        {R.left} ×ˢ (Finset.univ : Finset (Fin n)) ∨
      R.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
        (Finset.univ : Finset (Fin n)) ×ˢ {R.bottom} := by
  rcases R.left_right_eq_cases S with ⟨hl, _⟩ | ⟨hl, _⟩
  · left
    rw [R.coveredSquares_union_coveredSquares_of_left_eq_left S hl,
      coveredColumns_eq_singleton R S hR hS hl]
  · right
    rw [R.coveredSquares_union_coveredSquares_of_left_eq_right S hl,
      coveredRows_eq_singleton R S hR hS hl]

end GridEmptyAnnuli

end OnLeConjecture.KnotFloer
