/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingGeometry

/-!
# Laurent weights of the short matching paths

The matching rectangles have O count zero. Their Maslov changes and the
center-state grading identify the total O count of every two- or
three-rectangle matching path with that of an old empty rectangle having
the same endpoints. This checks weights independently of the geometric
short-path bijection, which still needs to be proved.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The unit matching edge lowers Maslov grading by exactly one. -/
theorem stabilizationMatchingTarget_maslovO (a : StabilizationMatchingNode G s) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ
        (stabilizationMatchingTargetState G s a) =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ a.val - 1 := by
  have h := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns
    (G.isEmpty_stabilizeXRowSwapRectangle s a.val)
  rw [stabilizationRowRectangle_source_OColumns G s a.val a.property.1,
    Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero] at h
  exact h

/-- The entry/exit path and an old empty rectangle have the same total O count. -/
theorem stabilizationMatching_two_rectangle_OCount
    {x y : GridState n} (a : StabilizationMatchingNode G s)
    (r : GridRectangleBetween x y) (hr : r.IsEmpty)
    (entry : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : entry.IsEmpty)
    (exit : GridRectangleBetween a.val (y.insertPoint s.succ (G.X s).succ))
    (hx : exit.IsEmpty) :
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns entry.toGridRectangle).card +
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns exit.toGridRectangle).card =
      (G.OColumns r.toGridRectangle).card := by
  have ho := G.maslovOℤ_sub_two_mul_card_OColumns hr
  have heM := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns he
  have hxM := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns hx
  rw [stabilizationMatchingTarget_maslovO,
    GridDiagram.maslovOℤ_stabilizeX_insertPoint] at heM
  rw [GridDiagram.maslovOℤ_stabilizeX_insertPoint] at hxM
  omega

/-- One internal matching transition preserves the same total O-count identity. -/
theorem stabilizationMatching_three_rectangle_OCount
    {x y : GridState n} (a b : StabilizationMatchingNode G s)
    (r : GridRectangleBetween x y) (hr : r.IsEmpty)
    (entry : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : entry.IsEmpty)
    (middle : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hm : middle.IsEmpty)
    (exit : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ))
    (hx : exit.IsEmpty) :
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns entry.toGridRectangle).card +
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns middle.toGridRectangle).card +
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns exit.toGridRectangle).card =
      (G.OColumns r.toGridRectangle).card := by
  have ho := G.maslovOℤ_sub_two_mul_card_OColumns hr
  have heM := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns he
  have hmM := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns hm
  have hxM := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns hx
  rw [stabilizationMatchingTarget_maslovO,
    GridDiagram.maslovOℤ_stabilizeX_insertPoint] at heM
  rw [stabilizationMatchingTarget_maslovO] at hmM
  rw [GridDiagram.maslovOℤ_stabilizeX_insertPoint] at hxM
  omega

variable (R : Type*) [CommSemiring R]

/-- The two actual rectangle monomials multiply to the old rectangle monomial. -/
theorem stabilizationMatching_two_rectangle_weight
    {x y : GridState n} (a : StabilizationMatchingNode G s)
    (r : GridRectangleBetween x y) (hr : r.IsEmpty)
    (entry : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : entry.IsEmpty)
    (exit : GridRectangleBetween a.val (y.insertPoint s.succ (G.X s).succ))
    (hx : exit.IsEmpty) :
    (LaurentPolynomial.T
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns entry.toGridRectangle).card : ℤ) :
          LaurentPolynomial R) *
      LaurentPolynomial.T
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns exit.toGridRectangle).card : ℤ) =
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [← LaurentPolynomial.T_add, ← Nat.cast_add,
    stabilizationMatching_two_rectangle_OCount G s a r hr entry he exit hx]

/-- The same weight identity includes one internal full rectangle. -/
theorem stabilizationMatching_three_rectangle_weight
    {x y : GridState n} (a b : StabilizationMatchingNode G s)
    (r : GridRectangleBetween x y) (hr : r.IsEmpty)
    (entry : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a)) (he : entry.IsEmpty)
    (middle : GridRectangleBetween a.val (stabilizationMatchingTargetState G s b))
    (hm : middle.IsEmpty)
    (exit : GridRectangleBetween b.val (y.insertPoint s.succ (G.X s).succ))
    (hx : exit.IsEmpty) :
    (LaurentPolynomial.T
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns entry.toGridRectangle).card : ℤ) :
          LaurentPolynomial R) *
      LaurentPolynomial.T
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns middle.toGridRectangle).card : ℤ) *
      LaurentPolynomial.T
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns exit.toGridRectangle).card : ℤ) =
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add, ← Nat.cast_add, ← Nat.cast_add,
    stabilizationMatching_three_rectangle_OCount G s a b r hr entry he middle hm exit hx]

end OnLeConjecture.KnotFloer.GridFull
