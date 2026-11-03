/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: Pablo Portilla Cuadrado, The Tau Ceti contributors
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurent
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Relabeling

/-!
# Row reflection of the full grid differential

Reflection of grid points uses negation modulo the grid size, while reflection
of marking squares uses `Fin.rev`. Keeping this distinction gives a bijection
from empty rectangles `x → y` to empty rectangles between the reflected states
in the opposite direction. Each O column, and hence its polynomial weight, is
unchanged. Thus the full differential matrix of the reflected diagram is the
transpose of the original matrix after the explicit state relabelling.

The rectangle proof adapts the half-turn argument in TauCeti's
`KnotTheory/Grid/Rectangle/Relabeling.lean` at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`, under Apache 2.0.
This is a grid calculation. No geometric mirror identification or staircase
homotopy equivalence is assumed or asserted.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable {n : ℕ}

/-- Reflection on integer grid rows, namely negation modulo the grid size. -/
def reflectedPointRows (n : ℕ) : Equiv.Perm (Fin n) := Fin.revPerm.trans (finRotate n)

/-- The reflected state uses integer grid rows rather than marking-square rows. -/
def reflectedState (x : GridState n) : GridState n := x.relabelRows (reflectedPointRows n)

@[simp] theorem reflectedState_apply (x : GridState n) (c : Fin n) :
    reflectedState x c = finRotate n (x c).rev := rfl

@[simp] theorem reflectedState_reflectedState (x : GridState n) :
    reflectedState (reflectedState x) = x := by
  ext c
  simp only [reflectedState_apply, Fin.finRotate_rev_finRotate_rev]

/-- Reflection of marking squares across a horizontal grid circle. -/
def reflectedDiagram (G : GridDiagram n) : GridDiagram n := G.relabelRows Fin.revPerm

@[simp] theorem reflectedDiagram_O (G : GridDiagram n) (c : Fin n) :
    (reflectedDiagram G).O c = (G.O c).rev := rfl

@[simp] theorem reflectedDiagram_X (G : GridDiagram n) (c : Fin n) :
    (reflectedDiagram G).X c = (G.X c).rev := rfl

@[simp] theorem reflectedDiagram_reflectedDiagram (G : GridDiagram n) :
    reflectedDiagram (reflectedDiagram G) = G := by
  apply GridDiagram.ext <;> apply GridState.ext <;> intro c <;>
    simp only [reflectedDiagram_O, reflectedDiagram_X, Fin.rev_rev]

/-- Row reflection reverses the direction of an oriented rectangle. -/
def reflectedRectangleEquiv (x y : GridState n) :
    GridRectangleBetween x y ≃ GridRectangleBetween (reflectedState y) (reflectedState x) where
  toFun r :=
    { left := r.left
      right := r.right
      left_ne_right := r.left_ne_right
      map_left := by simp only [reflectedState_apply, r.map_right]
      map_right := by simp only [reflectedState_apply, r.map_left]
      map_of_ne := fun c hl hr => by simp only [reflectedState_apply, r.map_of_ne c hl hr] }
  invFun r :=
    { left := r.left
      right := r.right
      left_ne_right := r.left_ne_right
      map_left := by
        have h := r.map_right
        simp only [reflectedState_apply] at h
        exact (Fin.rev_injective ((finRotate n).injective h)).symm
      map_right := by
        have h := r.map_left
        simp only [reflectedState_apply] at h
        exact (Fin.rev_injective ((finRotate n).injective h)).symm
      map_of_ne := fun c hl hr => by
        have h := r.map_of_ne c hl hr
        simp only [reflectedState_apply] at h
        exact (Fin.rev_injective ((finRotate n).injective h)).symm }
  left_inv _ := GridRectangleBetween.ext rfl rfl
  right_inv _ := GridRectangleBetween.ext rfl rfl

@[simp] theorem reflectedRectangleEquiv_left {x y : GridState n}
    (r : GridRectangleBetween x y) : (reflectedRectangleEquiv x y r).left = r.left := rfl

@[simp] theorem reflectedRectangleEquiv_right {x y : GridState n}
    (r : GridRectangleBetween x y) : (reflectedRectangleEquiv x y r).right = r.right := rfl

@[simp] theorem reflectedRectangleEquiv_bottom {x y : GridState n}
    (r : GridRectangleBetween x y) :
    (reflectedRectangleEquiv x y r).bottom = finRotate n r.top.rev := by
  rw [bottom_def, reflectedRectangleEquiv_left, reflectedState_apply, r.map_left, top_def]

@[simp] theorem reflectedRectangleEquiv_top {x y : GridState n}
    (r : GridRectangleBetween x y) :
    (reflectedRectangleEquiv x y r).top = finRotate n r.bottom.rev := by
  rw [top_def, reflectedRectangleEquiv_right, reflectedState_apply, r.map_right, bottom_def]

/-- Reflection preserves and reflects emptiness, using the target-state emptiness test. -/
@[simp] theorem isEmpty_reflectedRectangleEquiv {x y : GridState n}
    (r : GridRectangleBetween x y) :
    (reflectedRectangleEquiv x y r).IsEmpty ↔ r.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo, isEmpty_iff_forall_notMem_cIoo_target]
  simp only [reflectedRectangleEquiv_left, reflectedRectangleEquiv_right, reflectedState_apply,
    Grid.mem_cIoo_finRotate_rev, r.map_left, r.map_right, bottom_def, top_def]

/-- Marking-square reflection preserves the covered-square condition. -/
theorem mem_coveredSquares_reflectedRectangleEquiv {x y : GridState n}
    (r : GridRectangleBetween x y) (c j : Fin n) :
    (c, j.rev) ∈ (reflectedRectangleEquiv x y r).toGridRectangle.coveredSquares ↔
      (c, j) ∈ r.toGridRectangle.coveredSquares := by
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, reflectedRectangleEquiv_left,
    reflectedRectangleEquiv_right, reflectedRectangleEquiv_bottom,
    reflectedRectangleEquiv_top, Grid.rev_mem_cIco_finRotate_rev]

/-- Every O-variable appears in exactly the same reflected rectangle weight. -/
theorem OColumns_reflectedRectangleEquiv (G : GridDiagram n) {x y : GridState n}
    (r : GridRectangleBetween x y) :
    (reflectedDiagram G).OColumns (reflectedRectangleEquiv x y r).toGridRectangle =
      G.OColumns r.toGridRectangle := by
  ext c
  simp only [GridDiagram.mem_OColumns, reflectedDiagram_O,
    mem_coveredSquares_reflectedRectangleEquiv]

/-- Full polynomial rectangle coefficients transpose under the explicit reflection. -/
theorem coefficient_reflectedDiagram (G : GridDiagram n) (R : Type*) [CommSemiring R]
    (x y : GridState n) :
    coefficient (reflectedDiagram G) R (reflectedState y) (reflectedState x) =
      coefficient G R x y := by
  classical
  rw [coefficient, coefficient]
  refine (Finset.sum_equiv (reflectedRectangleEquiv x y) (fun r => ?_)
    (fun r _ => ?_)).symm
  · simp only [mem_emptyRectangles, isEmpty_reflectedRectangleEquiv]
  · rw [OMonomial_eq_monomial_oExponent, OMonomial_eq_monomial_oExponent]
    congr 1
    ext c
    simp only [oExponent, OColumns_reflectedRectangleEquiv]

/-- The same transpose identity holds after all O variables become one Laurent variable. -/
theorem laurentCoefficient_reflectedDiagram (G : GridDiagram n) (R : Type*) [CommSemiring R]
    (x y : GridState n) :
    laurentCoefficient (reflectedDiagram G) R (reflectedState y) (reflectedState x) =
      laurentCoefficient G R x y := by
  simp only [laurentCoefficient, coefficient_reflectedDiagram]

end OnLeConjecture.KnotFloer.GridFull
