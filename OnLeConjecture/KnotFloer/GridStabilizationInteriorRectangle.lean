/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Stabilization.Rectangle
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Juxtaposition
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Factoring a rectangle through its unique interior state point

A rectangle with one interior state point factors into three empty rectangles. This is
the geometric Type 2 rectangle used in stabilization domain decompositions in
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
The full stabilization matrix identity is not assumed here.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} {x y : GridState n} (r : GridRectangleBetween x y)
  (p : Fin n) (hp : p ∈ Grid.cIoo r.left r.right)

/-- The state after exchanging the initial corner and the interior point. -/
def interiorRectangleStateOne : GridState n := x.swapColumns r.left p

/-- The state after then exchanging the interior column and the terminal corner. -/
def interiorRectangleStateTwo : GridState n :=
  (interiorRectangleStateOne r p).swapColumns p r.right

include hp in
/-- The third exchange restores the interior point and produces the original target state. -/
theorem interiorRectangleStateTwo_swap :
    y = (interiorRectangleStateTwo r p).swapColumns r.left p := by
  have hpl := Grid.ne_left_of_mem_cIoo hp
  have hpr := Grid.ne_right_of_mem_cIoo hp
  refine r.target_eq_swapColumns.trans ?_
  apply GridState.ext
  intro c
  by_cases hl : c = r.left
  · subst c
    simp [interiorRectangleStateTwo, interiorRectangleStateOne, GridState.swapColumns_apply,
      Equiv.swap_apply_def, Ne.symm hpr, Ne.symm r.left_ne_right]
  · by_cases hp' : c = p
    · subst c
      simp [interiorRectangleStateTwo, interiorRectangleStateOne, GridState.swapColumns_apply,
        Equiv.swap_apply_def, hpl, hpr, r.left_ne_right, Ne.symm hpl]
    · by_cases hr : c = r.right
      · subst c
        simp [interiorRectangleStateTwo, interiorRectangleStateOne, GridState.swapColumns_apply,
          Equiv.swap_apply_def, Ne.symm hpr, Ne.symm r.left_ne_right]
      · simp [interiorRectangleStateTwo, interiorRectangleStateOne, GridState.swapColumns_apply,
          Equiv.swap_apply_of_ne_of_ne hl hp', Equiv.swap_apply_of_ne_of_ne hp' hr,
          Equiv.swap_apply_of_ne_of_ne hl hr]

/-- The lower initial-column part of the rectangle. -/
def interiorRectangleOne : GridRectangleBetween x (interiorRectangleStateOne r p) :=
  { left := r.left
    right := p
    left_ne_right := Ne.symm (Grid.ne_left_of_mem_cIoo hp)
    map_left := by simp [interiorRectangleStateOne, GridState.swapColumns_apply]
    map_right := by simp [interiorRectangleStateOne, GridState.swapColumns_apply]
    map_of_ne := by
      intro c hcl hcp
      simp [interiorRectangleStateOne, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hcl hcp] }

/-- The full-height terminal-column part of the rectangle. -/
def interiorRectangleTwo : GridRectangleBetween
    (interiorRectangleStateOne r p) (interiorRectangleStateTwo r p) :=
  { left := p
    right := r.right
    left_ne_right := Grid.ne_right_of_mem_cIoo hp
    map_left := by simp [interiorRectangleStateTwo, GridState.swapColumns_apply]
    map_right := by simp [interiorRectangleStateTwo, GridState.swapColumns_apply]
    map_of_ne := by
      intro c hcp hcr
      simp [interiorRectangleStateTwo, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hcp hcr] }

/-- The upper initial-column part of the rectangle. -/
def interiorRectangleThree : GridRectangleBetween (interiorRectangleStateTwo r p) y :=
  { left := r.left
    right := p
    left_ne_right := Ne.symm (Grid.ne_left_of_mem_cIoo hp)
    map_left := by
      simpa only [GridState.swapColumns_apply, Equiv.swap_apply_left] using
        congrArg (fun z => z r.left) (interiorRectangleStateTwo_swap r p hp)
    map_right := by
      simpa only [GridState.swapColumns_apply, Equiv.swap_apply_right] using
        congrArg (fun z => z p) (interiorRectangleStateTwo_swap r p hp)
    map_of_ne := by
      intro c hcl hcp
      simpa only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcl hcp] using
        congrArg (fun z => z c) (interiorRectangleStateTwo_swap r p hp) }

/-- The three rectangle shapes use exactly the two cuts through the interior state point. -/
theorem interiorRectangle_shapes :
    (interiorRectangleOne r p hp).toGridRectangle =
      { left := r.left, right := p, bottom := x r.left, top := x p } ∧
    (interiorRectangleTwo r p hp).toGridRectangle =
      { left := p, right := r.right, bottom := x r.left, top := x r.right } ∧
    (interiorRectangleThree r p hp).toGridRectangle =
      { left := r.left, right := p, bottom := x p, top := x r.right } := by
  have hpl := Grid.ne_left_of_mem_cIoo hp
  have hpr := Grid.ne_right_of_mem_cIoo hp
  simp only [interiorRectangleOne, interiorRectangleTwo, interiorRectangleThree,
    GridRectangleBetween.toGridRectangle_eq, interiorRectangleStateOne, interiorRectangleStateTwo,
    GridState.swapColumns_apply]
  simp [Equiv.swap_apply_def, r.left_ne_right, Ne.symm hpl, Ne.symm hpr,
    Ne.symm r.left_ne_right]

/-- The three factors are empty when the indicated point is the only interior state point. -/
theorem interiorRectangles_empty
    (hrow : x p ∈ Grid.cIoo (x r.left) (x r.right))
    (hunique : ∀ c ∈ Grid.cIoo r.left r.right,
      x c ∈ Grid.cIoo (x r.left) (x r.right) → c = p) :
    (interiorRectangleOne r p hp).IsEmpty ∧
      (interiorRectangleTwo r p hp).IsEmpty ∧ (interiorRectangleThree r p hp).IsEmpty := by
  have hs := interiorRectangle_shapes r p hp
  have hpl := Grid.ne_left_of_mem_cIoo hp
  have hpr := Grid.ne_right_of_mem_cIoo hp
  have hleft := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hp
  have hright := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hp
  have hbottom := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hrow
  have htop := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hrow
  refine ⟨?_, ?_, ?_⟩
  · rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor, hs.1,
      GridRectangle.isEmptyFor_iff_forall_notMem_cIoo]
    intro c hc hr
    have heq := hunique c (hleft hc) (hbottom hr)
    exact Grid.ne_right_of_mem_cIoo hc heq
  · rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor, hs.2.1,
      GridRectangle.isEmptyFor_iff_forall_notMem_cIoo]
    intro c hc hr
    have hcp := Grid.ne_left_of_mem_cIoo hc
    have hcl := Grid.ne_left_of_mem_cIoo (hright hc)
    have hvalue : interiorRectangleStateOne r p c = x c := by
      simp [interiorRectangleStateOne, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hcl hcp]
    rw [hvalue] at hr
    exact hcp (hunique c (hright hc) hr)
  · rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor, hs.2.2,
      GridRectangle.isEmptyFor_iff_forall_notMem_cIoo]
    intro c hc hr
    have hcl := Grid.ne_left_of_mem_cIoo hc
    have hcp := Grid.ne_right_of_mem_cIoo hc
    have hcr := Grid.ne_right_of_mem_cIoo (hleft hc)
    have hvalue : interiorRectangleStateTwo r p c = x c := by
      simp [interiorRectangleStateTwo, interiorRectangleStateOne, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hcp hcr, Equiv.swap_apply_of_ne_of_ne hcl hcp]
    rw [hvalue] at hr
    exact hcp (hunique c (hleft hc) (htop hr))

/-- The three covered-square sets partition the original rectangle. -/
theorem interiorRectangles_coveredSquares
    (hrow : x p ∈ Grid.cIoo (x r.left) (x r.right)) :
    (interiorRectangleOne r p hp).toGridRectangle.coveredSquares ∪
        (interiorRectangleTwo r p hp).toGridRectangle.coveredSquares ∪
        (interiorRectangleThree r p hp).toGridRectangle.coveredSquares =
      r.toGridRectangle.coveredSquares := by
  have hs := interiorRectangle_shapes r p hp
  rw [hs.1, hs.2.1, hs.2.2, GridRectangleBetween.toGridRectangle_eq]
  simp only [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
    GridRectangle.coveredRows_def]
  rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hp,
    ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
  ext z
  simp only [Finset.mem_union, Finset.mem_product]
  tauto

/-- The three square sets are pairwise disjoint. -/
theorem interiorRectangles_pairwise_disjoint
    (hrow : x p ∈ Grid.cIoo (x r.left) (x r.right)) :
    Disjoint (interiorRectangleOne r p hp).toGridRectangle.coveredSquares
        (interiorRectangleTwo r p hp).toGridRectangle.coveredSquares ∧
    Disjoint (interiorRectangleOne r p hp).toGridRectangle.coveredSquares
        (interiorRectangleThree r p hp).toGridRectangle.coveredSquares ∧
    Disjoint (interiorRectangleTwo r p hp).toGridRectangle.coveredSquares
        (interiorRectangleThree r p hp).toGridRectangle.coveredSquares := by
  have hs := interiorRectangle_shapes r p hp
  rw [hs.1, hs.2.1, hs.2.2]
  exact ⟨GridRectangle.disjoint_coveredSquares_of_col_cut hp,
    GridRectangle.disjoint_coveredSquares_of_row_cut hrow,
    (GridRectangle.disjoint_coveredSquares_of_col_cut hp).symm⟩

/-- Any multiplicative square weight factors through the three rectangles. -/
theorem interiorRectangles_weight {S : Type*} [CommMonoid S] (w : Fin n × Fin n → S)
    (hrow : x p ∈ Grid.cIoo (x r.left) (x r.right)) :
    (∏ a ∈ (interiorRectangleOne r p hp).toGridRectangle.coveredSquares, w a) *
        (∏ a ∈ (interiorRectangleTwo r p hp).toGridRectangle.coveredSquares, w a) *
        (∏ a ∈ (interiorRectangleThree r p hp).toGridRectangle.coveredSquares, w a) =
      ∏ a ∈ r.toGridRectangle.coveredSquares, w a := by
  classical
  obtain ⟨h12, h13, h23⟩ := interiorRectangles_pairwise_disjoint r p hp hrow
  rw [← Finset.prod_union h12, ← Finset.prod_union (Finset.disjoint_union_left.mpr ⟨h13, h23⟩),
    interiorRectangles_coveredSquares r p hp hrow]

/-- An inserted point is the only possible obstruction to emptiness of a lifted empty rectangle. -/
theorem insertedRectangle_uniqueInterior (old : GridRectangleBetween x y) (he : old.IsEmpty)
    (newColumn newRow : Fin (n + 1)) :
    ∀ c ∈ Grid.cIoo (old.insertPoint newColumn newRow).left
        (old.insertPoint newColumn newRow).right,
      x.insertPoint newColumn newRow c ∈
        Grid.cIoo (x.insertPoint newColumn newRow (old.insertPoint newColumn newRow).left)
          (x.insertPoint newColumn newRow (old.insertPoint newColumn newRow).right) →
        c = newColumn := by
  intro c
  induction c using Fin.succAboveCases newColumn with
  | x => intros; rfl
  | p c =>
    intro hc hr
    simp only [GridRectangleBetween.insertPoint_left, GridRectangleBetween.insertPoint_right,
      GridState.insertPoint_apply_succAbove, Grid.mem_cIoo_succAbove_succAbove] at hc hr
    have hempty := (old.toGridRectangle.isEmptyFor_iff_forall_notMem_cIoo x).mp he
    exact False.elim (hempty c hc hr)

/-- Lifting an old empty rectangle through the new center gives three actual empty rectangles. -/
theorem insertedInteriorRectangles_empty (old : GridRectangleBetween x y) (he : old.IsEmpty)
    (newColumn newRow : Fin (n + 1))
    (hi : (newColumn, newRow) ∈ (old.insertPoint newColumn newRow).toGridRectangle.interior) :
    ∃ hp : newColumn ∈ Grid.cIoo (old.insertPoint newColumn newRow).left
        (old.insertPoint newColumn newRow).right,
      (interiorRectangleOne (old.insertPoint newColumn newRow) newColumn hp).IsEmpty ∧
      (interiorRectangleTwo (old.insertPoint newColumn newRow) newColumn hp).IsEmpty ∧
      (interiorRectangleThree (old.insertPoint newColumn newRow) newColumn hp).IsEmpty := by
  rw [GridRectangleBetween.mem_toGridRectangle_interior] at hi
  refine ⟨hi.1, interiorRectangles_empty _ _ hi.1 ?_
    (insertedRectangle_uniqueInterior old he newColumn newRow)⟩
  simpa only [GridState.insertPoint_apply_newColumn] using hi.2

end OnLeConjecture.KnotFloer.GridFull
