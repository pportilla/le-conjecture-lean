/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstCycle

/-!
# Rectangles leaving a transposition of the corner state

The state differs from the corner in two columns. Reflection turns its
empty-interior test into a cyclic-interval test for a single transposition.
These tests are used to evaluate the triangular boundary.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable (n : ℕ) {a b : Fin (consecutiveTorusGridSize n)}
  {y : GridState (consecutiveTorusGridSize n)}

/-- The exact interval test for emptiness after swapping two corner columns. -/
theorem isEmpty_corner_swap_iff
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y) :
    r.IsEmpty ↔ ∀ c ∈ Grid.cIoo r.left r.right,
      Equiv.swap a b c ∉ Grid.cIoo (Equiv.swap a b r.right) (Equiv.swap a b r.left) := by
  rw [isEmpty_iff_forall_notMem_cIoo]
  simp only [bottom_def, top_def, GridState.swapColumns_apply, reflectedTorusAnchor_apply,
    Grid.mem_cIoo_finRotate_rev]

/-- The exact O-column test for a rectangle leaving that transposition. -/
theorem mem_OColumns_corner_swap_iff
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (c : Fin (consecutiveTorusGridSize n)) :
    c ∈ (reflectedTorusGrid n).OColumns r.toGridRectangle ↔
      c ∈ Grid.cIco r.left r.right ∧
        c ∈ Grid.cIco (Equiv.swap a b r.right) (Equiv.swap a b r.left) := by
  simp only [GridDiagram.mem_OColumns, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    toGridRectangle_left, toGridRectangle_right, toGridRectangle_bottom,
    toGridRectangle_top, bottom_def, top_def, reflectedTorusGrid_O_apply,
    GridState.swapColumns_apply, reflectedTorusAnchor_apply, Grid.rev_mem_cIco_finRotate_rev]

/-- With one transposed column at the initial side, the other must lie outside the open arc. -/
theorem isEmpty_corner_swap_left_iff
    {c : Fin (consecutiveTorusGridSize n)} (hca : c ≠ a) (hcb : c ≠ b)
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hl : r.left = a) (hr : r.right = c) :
    r.IsEmpty ↔ b ∉ Grid.cIoo a c := by
  rw [isEmpty_corner_swap_iff, hl, hr,
    Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
  constructor
  · intro h hb
    have hb' := h b hb
    rw [Equiv.swap_apply_right] at hb'
    simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hb hb' hca hcb
    split_ifs at hb hb' <;> omega
  · intro hb d hd
    have hda : d ≠ a := by
      intro h
      exact Grid.left_notMem_cIoo a c (h ▸ hd)
    have hdb : d ≠ b := by intro h; exact hb (h ▸ hd)
    rw [Equiv.swap_apply_of_ne_of_ne hda hdb]
    simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hb hd hca hcb ⊢
    split_ifs at hb hd ⊢ <;> omega

/-- An empty rectangle of this shape avoids every O marking. -/
theorem OColumns_corner_swap_left_eq_empty
    {c : Fin (consecutiveTorusGridSize n)} (hca : c ≠ a) (hcb : c ≠ b)
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hl : r.left = a) (hr : r.right = c) (he : r.IsEmpty) :
    (reflectedTorusGrid n).OColumns r.toGridRectangle = ∅ := by
  have hb := (isEmpty_corner_swap_left_iff n hca hcb r hl hr).mp he
  ext d
  rw [mem_OColumns_corner_swap_iff, hl, hr,
    Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
  simp only [Finset.notMem_empty, iff_false, Grid.mem_cIco, Grid.mem_cIoo,
    ne_eq, Fin.ext_iff] at hb hca hcb ⊢
  split_ifs at hb ⊢ <;> omega

/-- The analogous test when the transposed column is the terminal side. -/
theorem isEmpty_corner_swap_right_iff
    {c : Fin (consecutiveTorusGridSize n)} (hca : c ≠ a) (hcb : c ≠ b)
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hl : r.left = c) (hr : r.right = a) :
    r.IsEmpty ↔ b ∉ Grid.cIoo c a := by
  rw [isEmpty_corner_swap_iff, hl, hr,
    Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
  constructor
  · intro h hb
    have hb' := h b hb
    rw [Equiv.swap_apply_right] at hb'
    simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hb hb' hca hcb
    split_ifs at hb hb' <;> omega
  · intro hb d hd
    have hda : d ≠ a := by
      intro h
      exact Grid.right_notMem_cIoo c a (h ▸ hd)
    have hdb : d ≠ b := by intro h; exact hb (h ▸ hd)
    rw [Equiv.swap_apply_of_ne_of_ne hda hdb]
    simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hb hd hca hcb ⊢
    split_ifs at hb hd ⊢ <;> omega

/-- Empty rectangles with the transposed terminal column also avoid O markings. -/
theorem OColumns_corner_swap_right_eq_empty
    {c : Fin (consecutiveTorusGridSize n)} (hca : c ≠ a) (hcb : c ≠ b)
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hl : r.left = c) (hr : r.right = a) (he : r.IsEmpty) :
    (reflectedTorusGrid n).OColumns r.toGridRectangle = ∅ := by
  have hb := (isEmpty_corner_swap_right_iff n hca hcb r hl hr).mp he
  ext d
  rw [mem_OColumns_corner_swap_iff, hl, hr,
    Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
  simp only [Finset.notMem_empty, iff_false, Grid.mem_cIco, Grid.mem_cIoo,
    ne_eq, Fin.ext_iff] at hb hca hcb ⊢
  split_ifs at hb ⊢ <;> omega

/-- A second transposition sharing exactly one column has Laurent coefficient one. -/
theorem laurentCoefficient_corner_swap_three (R : Type*) [CommSemiring R]
    (hab : a ≠ b) {c : Fin (consecutiveTorusGridSize n)}
    (hca : c ≠ a) (hcb : c ≠ b) :
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns a b)
      (((reflectedTorusAnchor n).swapColumns a b).swapColumns a c) = 1 := by
  classical
  let x := (reflectedTorusAnchor n).swapColumns a b
  let r := GridRectangleBetween.ofSwapColumns x (x.swapColumns a c) a c hca.symm rfl
  have hl : r.left = a := ofSwapColumns_left _ _ _ _ _ _
  have hr : r.right = c := ofSwapColumns_right _ _ _ _ _ _
  have hsl : r.swapSides.left = c := (swapSides_left r).trans hr
  have hsr : r.swapSides.right = a := (swapSides_right r).trans hl
  have he := isEmpty_corner_swap_left_iff n hca hcb r hl hr
  have hs := isEmpty_corner_swap_right_iff n hca hcb r.swapSides hsl hsr
  rw [laurentCoefficient_eq]
  by_cases hb : b ∈ Grid.cIoo a c
  · have hne : ¬r.IsEmpty := fun h => he.mp h hb
    have hse : r.swapSides.IsEmpty := hs.mpr fun h =>
      Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap a c) hb h
    have hset : emptyRectangles x (x.swapColumns a c) = {r.swapSides} := by
      simp only [emptyRectangles, r.univ_eq_pair, Finset.filter_insert,
        hne, ↓reduceIte, Finset.filter_singleton, hse]
    rw [hset, Finset.sum_singleton,
      OColumns_corner_swap_right_eq_empty n hca hcb r.swapSides hsl hsr hse,
      Finset.card_empty, Nat.cast_zero, LaurentPolynomial.T_zero]
  · have hre : r.IsEmpty := he.mpr hb
    have hb' : b ∈ Grid.cIoo c a :=
      Grid.mem_cIoo_swap_of_notMem hca.symm hab.symm hcb.symm hb
    have hsne : ¬r.swapSides.IsEmpty := fun h => hs.mp h hb'
    have hset : emptyRectangles x (x.swapColumns a c) = {r} := by
      simp only [emptyRectangles, r.univ_eq_pair, Finset.filter_insert,
        hre, ↓reduceIte, Finset.filter_singleton, hsne, Finset.insert_empty]
    rw [hset, Finset.sum_singleton,
      OColumns_corner_swap_left_eq_empty n hca hcb r hl hr hre,
      Finset.card_empty, Nat.cast_zero, LaurentPolynomial.T_zero]

/-- Reversing both sides preserves emptiness when neither side is a transposed column. -/
theorem isEmpty_swapSides_corner_swap_of_disjoint
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hla : r.left ≠ a) (hlb : r.left ≠ b) (hra : r.right ≠ a) (hrb : r.right ≠ b)
    (he : r.IsEmpty) : r.swapSides.IsEmpty := by
  rw [isEmpty_corner_swap_iff] at he ⊢
  simp only [swapSides_left, swapSides_right,
    Equiv.swap_apply_of_ne_of_ne hla hlb,
    Equiv.swap_apply_of_ne_of_ne hra hrb] at he ⊢
  intro c hc hsw
  by_cases hca : c = a
  · subst c
    rw [Equiv.swap_apply_left] at hsw
    have h := he b hsw
    rw [Equiv.swap_apply_right] at h
    exact h hc
  · by_cases hcb : c = b
    · subst c
      rw [Equiv.swap_apply_right] at hsw
      have h := he a hsw
      rw [Equiv.swap_apply_left] at h
      exact h hc
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb] at hsw
      exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap r.right r.left) hc hsw

/-- Both orientations avoid O markings in the disjoint-column case. -/
theorem OColumns_corner_swap_disjoint_eq_empty
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hla : r.left ≠ a) (hlb : r.left ≠ b) (hra : r.right ≠ a) (hrb : r.right ≠ b) :
    (reflectedTorusGrid n).OColumns r.toGridRectangle = ∅ := by
  ext c
  rw [mem_OColumns_corner_swap_iff,
    Equiv.swap_apply_of_ne_of_ne hla hlb, Equiv.swap_apply_of_ne_of_ne hra hrb]
  simp only [Finset.notMem_empty, iff_false]
  exact fun h => Finset.disjoint_left.mp (Grid.disjoint_cIco_swap r.left r.right) h.1 h.2

/-- A second transposition on two disjoint columns has zero full Laurent coefficient. -/
theorem laurentCoefficient_corner_swap_disjoint (R : Type*) [CommSemiring R] [CharP R 2]
    {c d : Fin (consecutiveTorusGridSize n)} (hcd : c ≠ d)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns a b)
      (((reflectedTorusAnchor n).swapColumns a b).swapColumns c d) = 0 := by
  classical
  let x := (reflectedTorusAnchor n).swapColumns a b
  let r := GridRectangleBetween.ofSwapColumns x (x.swapColumns c d) c d hcd rfl
  have hl : r.left = c := ofSwapColumns_left _ _ _ _ _ _
  have hr : r.right = d := ofSwapColumns_right _ _ _ _ _ _
  have hsl : r.swapSides.left = d := (swapSides_left r).trans hr
  have hsr : r.swapSides.right = c := (swapSides_right r).trans hl
  have ho := OColumns_corner_swap_disjoint_eq_empty n r
    (by simpa only [hl] using hca) (by simpa only [hl] using hcb)
    (by simpa only [hr] using hda) (by simpa only [hr] using hdb)
  have hso := OColumns_corner_swap_disjoint_eq_empty n r.swapSides
    (by simpa only [hsl] using hda) (by simpa only [hsl] using hdb)
    (by simpa only [hsr] using hca) (by simpa only [hsr] using hcb)
  have heq : r.swapSides.IsEmpty ↔ r.IsEmpty := by
    constructor
    · intro h
      simpa only [swapSides_swapSides] using
        isEmpty_swapSides_corner_swap_of_disjoint n r.swapSides
          (by simpa only [hsl] using hda) (by simpa only [hsl] using hdb)
          (by simpa only [hsr] using hca) (by simpa only [hsr] using hcb) h
    · exact isEmpty_swapSides_corner_swap_of_disjoint n r
        (by simpa only [hl] using hca) (by simpa only [hl] using hcb)
        (by simpa only [hr] using hda) (by simpa only [hr] using hdb)
  rw [laurentCoefficient_eq]
  by_cases he : r.IsEmpty
  · have hse := heq.mpr he
    have hset : emptyRectangles x (x.swapColumns c d) = {r, r.swapSides} := by
      simp only [emptyRectangles, r.univ_eq_pair, Finset.filter_insert, he,
        ↓reduceIte, Finset.filter_singleton, hse]
    rw [hset, Finset.sum_pair r.swapSides_ne_self.symm, ho, hso, Finset.card_empty,
      Nat.cast_zero, LaurentPolynomial.T_zero]
    ext k
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero,
      Finsupp.add_apply, Finsupp.zero_apply, CharTwo.add_self_eq_zero]
  · have hse : ¬r.swapSides.IsEmpty := fun h => he (heq.mp h)
    have hset : emptyRectangles x (x.swapColumns c d) = ∅ := by
      simp only [emptyRectangles, r.univ_eq_pair, Finset.filter_insert, he,
        ↓reduceIte, Finset.filter_singleton, hse]
    rw [hset, Finset.sum_empty]

/-- A rectangle undoing the corner transposition is empty exactly when its column arc is empty. -/
theorem isEmpty_corner_swap_backtrack_iff
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hl : r.left = a) (hr : r.right = b) :
    r.IsEmpty ↔ Grid.cIoo a b = ∅ := by
  rw [isEmpty_corner_swap_iff, hl, hr, Equiv.swap_apply_left, Equiv.swap_apply_right]
  constructor
  · intro he
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hca : c ≠ a := fun h => Grid.left_notMem_cIoo a b (h ▸ hc)
    have hcb : c ≠ b := fun h => Grid.right_notMem_cIoo a b (h ▸ hc)
    have h := he c hc
    rw [Equiv.swap_apply_of_ne_of_ne hca hcb] at h
    exact h hc
  · intro he c hc
    rw [he] at hc
    exact (Finset.notMem_empty c hc).elim

/-- Its O columns are precisely that half-open column arc. -/
theorem OColumns_corner_swap_backtrack
    (r : GridRectangleBetween ((reflectedTorusAnchor n).swapColumns a b) y)
    (hl : r.left = a) (hr : r.right = b) :
    (reflectedTorusGrid n).OColumns r.toGridRectangle = Grid.cIco a b := by
  ext c
  rw [mem_OColumns_corner_swap_iff, hl, hr, Equiv.swap_apply_left, Equiv.swap_apply_right,
    and_self]

/-- Inside the chosen linear column range, only an adjacent swap returns to the corner. -/
theorem laurentCoefficient_corner_swap_anchor_of_lt (R : Type*) [CommSemiring R]
    (hab : (a : ℕ) < b) (hb : (b : ℕ) + 1 < consecutiveTorusGridSize n) :
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns a b) (reflectedTorusAnchor n) =
      if (b : ℕ) = (a : ℕ) + 1 then LaurentPolynomial.T 1 else 0 := by
  classical
  have hne : a ≠ b := by intro h; subst b; omega
  let x := (reflectedTorusAnchor n).swapColumns a b
  let r := GridRectangleBetween.ofSwapColumns x (reflectedTorusAnchor n) a b hne
    (GridState.swapColumns_swapColumns _ _ _).symm
  have hl : r.left = a := ofSwapColumns_left _ _ _ _ _ _
  have hr : r.right = b := ofSwapColumns_right _ _ _ _ _ _
  have hi : Grid.cIoo a b = ∅ ↔ (b : ℕ) = (a : ℕ) + 1 := by
    constructor
    · intro h
      by_contra hne'
      let c : Fin (consecutiveTorusGridSize n) := ⟨(a : ℕ) + 1, by omega⟩
      have hc : c ∈ Grid.cIoo a b := by
        rw [Grid.mem_cIoo]
        exact ⟨hne, by simp only [hab, ↓reduceIte]; dsimp [c]; omega⟩
      rw [h] at hc
      exact Finset.notMem_empty c hc
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      rw [Grid.mem_cIoo] at hc
      simp only [hab, ↓reduceIte] at hc
      omega
  have hback : Grid.cIoo b a ≠ ∅ := by
    intro h
    let c : Fin (consecutiveTorusGridSize n) := ⟨(b : ℕ) + 1, hb⟩
    have hc : c ∈ Grid.cIoo b a := by
      rw [Grid.mem_cIoo]
      refine ⟨hne.symm, ?_⟩
      simp only [show ¬(b : ℕ) < a by omega, ↓reduceIte]
      exact Or.inl (by dsimp [c]; omega)
    rw [h] at hc
    exact Finset.notMem_empty c hc
  have hsne : ¬r.swapSides.IsEmpty := by
    have ht := isEmpty_corner_swap_backtrack_iff n (a := b) (b := a)
      (y := reflectedTorusAnchor n)
    rw [GridState.swapColumns_comm b a] at ht
    exact fun h => hback ((ht r.swapSides
      ((swapSides_left r).trans hr) ((swapSides_right r).trans hl)).mp h)
  rw [laurentCoefficient_eq]
  by_cases hadj : (b : ℕ) = (a : ℕ) + 1
  · have he := (isEmpty_corner_swap_backtrack_iff n r hl hr).mpr (hi.mpr hadj)
    have hset : emptyRectangles x (reflectedTorusAnchor n) = {r} := by
      simp only [emptyRectangles, r.univ_eq_pair, Finset.filter_insert, he, ↓reduceIte,
        Finset.filter_singleton, hsne, Finset.insert_empty]
    rw [hset, Finset.sum_singleton, if_pos hadj, OColumns_corner_swap_backtrack n r hl hr,
      Grid.cIco_of_ne hne, hi.mpr hadj, Finset.insert_empty, Finset.card_singleton, Nat.cast_one]
  · have he : ¬r.IsEmpty := fun h => hadj (hi.mp
      ((isEmpty_corner_swap_backtrack_iff n r hl hr).mp h))
    have hset : emptyRectangles x (reflectedTorusAnchor n) = ∅ := by
      simp only [emptyRectangles, r.univ_eq_pair, Finset.filter_insert, he, ↓reduceIte,
        Finset.filter_singleton, hsne]
    rw [hset, Finset.sum_empty, if_neg hadj]

end OnLeConjecture.KnotFloer.GridFull
