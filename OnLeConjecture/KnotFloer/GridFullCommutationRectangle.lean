/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationGauge

/-!
# Empty pentagons and rectangles crossing one adjacent square

For each turn, both orientations of empty pentagons correspond exactly
to the empty rectangles containing one of the two adjacent turn squares.
The pentagon O weight is the rectangle O weight times the target state's
diagonal Laurent factor.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

namespace CommutationPentagon

variable {C : GridDiagram.ColumnTurn n} {x y : GridState n}

/-- The rectangle with the same four state corners as the pentagon. -/
def toRectangle : CommutationPentagon C x y → GridRectangleBetween x y
  | .inl P => P.toGridRectangleBetween
  | .inr P => P.toGridRectangleBetween

@[simp]
theorem isEmpty_toRectangle (P : CommutationPentagon C x y) :
    P.toRectangle.IsEmpty ↔ P.IsEmpty := by
  cases P <;> rfl

/-- The two pentagon orientations have different underlying rectangles. -/
theorem toRectangle_injective : Function.Injective
    (toRectangle : CommutationPentagon C x y → GridRectangleBetween x y) := by
  intro P Q h
  rcases P with P | P <;> rcases Q with Q | Q
  · exact congrArg Sum.inl (Subsingleton.elim P Q)
  · have he := congrArg GridRectangleBetween.left h
    exact (P.left_ne (he.trans Q.left_eq)).elim
  · have he := congrArg GridRectangleBetween.left h
    exact (Q.left_ne (he.symm.trans P.left_eq)).elim
  · exact congrArg Sum.inr (Subsingleton.elim P Q)

end CommutationPentagon

/-- A rectangle contains exactly one of the two squares adjacent to a turn. -/
def crossesOneTurnSquare (C : GridDiagram.ColumnTurn n) {x y : GridState n}
    (r : GridRectangleBetween x y) : Prop :=
  Xor ((C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares)
    ((finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares)

/-- Crossing exactly one adjacent square means that one vertical side is the replaced line. -/
theorem crossesOneTurnSquare_iff (C : GridDiagram.ColumnTurn n) {x y : GridState n}
    (r : GridRectangleBetween x y) :
    crossesOneTurnSquare C r ↔
      (r.left = finRotate n C.column ∨ r.right = finRotate n C.column) ∧
        C.turnRow ∈ Grid.cIco r.bottom r.top := by
  classical
  simp only [crossesOneTurnSquare, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top]
  by_cases hl : r.left = finRotate n C.column
  · have ha : C.column ∉ Grid.cIco r.left r.right := by rw [hl]; simp
    have hb : finRotate n C.column ∈ Grid.cIco r.left r.right := by
      simpa only [← hl] using Grid.left_mem_cIco r.left_ne_right
    simp only [ha, hb, Xor]
    tauto
  · by_cases hr : r.right = finRotate n C.column
    · have ha : C.column ∈ Grid.cIco r.left r.right := by
        rw [hr]
        exact Grid.self_mem_cIco_finRotate hl
      have hb : finRotate n C.column ∉ Grid.cIco r.left r.right := by
        rw [hr]
        exact Grid.right_notMem_cIco _ _
      simp only [ha, hb, Xor]
      tauto
    · have hsame := Grid.mem_cIco_finRotate_iff_of_ne hl hr
      simp only [hsame, Xor]
      tauto

/-- Every commutation pentagon crosses precisely one of the adjacent turn squares. -/
theorem CommutationPentagon.crossesOneTurnSquare {C : GridDiagram.ColumnTurn n}
    {x y : GridState n} (P : CommutationPentagon C x y) :
    crossesOneTurnSquare C P.toRectangle := by
  rw [crossesOneTurnSquare_iff]
  rcases P with P | P
  · exact ⟨Or.inr P.right_eq, P.turn_mem⟩
  · exact ⟨Or.inl P.left_eq, P.turn_mem⟩

/-- Every rectangle crossing exactly one turn square determines a commutation pentagon. -/
theorem exists_pentagon_toRectangle (C : GridDiagram.ColumnTurn n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : crossesOneTurnSquare C r) :
    ∃ P : CommutationPentagon C x y, P.toRectangle = r := by
  obtain ⟨hl | hr, hs⟩ := (crossesOneTurnSquare_iff C r).mp hr
  · exact ⟨.inr { toGridRectangleBetween := r, left_eq := hl, turn_mem := hs }, rfl⟩
  · exact ⟨.inl (GridPentagonBetween.ofRightEq r hr hs),
      GridPentagonBetween.ofRightEq_toGridRectangleBetween r hr hs⟩

/-- Pentagon and rectangle marking counts differ by the explicit target gauge exponent. -/
theorem fullCommutationPentagon_oCount_eq (G : GridDiagram n)
    (C : GridDiagram.ColumnCommutationData G) {x y : GridState n}
    (P : CommutationPentagon C x y) (hP : P.IsEmpty) :
    (P.oCount G : ℤ) = (G.OColumns P.toRectangle.toGridRectangle).card +
      commutationGaugeExponent G C y := by
  have hp := (fullCommutationPentagon_maslov_changes G C P hP).1
  have hr := laurentMaslovDegree_add_card_OColumns G P.toRectangle
    (P.isEmpty_toRectangle.mpr hP) 0
  simp only [laurentMaslovDegree, zero_add, mul_zero, sub_zero] at hr
  rw [maslov_swapColumns_eq_gauge] at hp
  omega

open Classical in
/-- The polygon coefficient is a diagonal factor times the selected rectangle sum. -/
theorem laurentCommutationCoefficient_eq_rectangle_sum (G : GridDiagram n)
    (R : Type*) [CommSemiring R] (C : GridDiagram.ColumnCommutationData G)
    (x y : GridState n) :
    laurentCommutationCoefficient G R C x y =
      LaurentPolynomial.T (commutationGaugeExponent G C y) *
        ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter (crossesOneTurnSquare C),
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [laurentCommutationCoefficient, Finset.mul_sum]
  apply Finset.sum_bij (fun P _ => P.toRectangle)
  · intro P hP
    exact Finset.mem_filter.mpr
      ⟨(GridRectangleBetween.mem_emptyRectangles _).mpr
        (P.isEmpty_toRectangle.mpr (mem_fullCommutationPentagons P |>.mp hP)),
        P.crossesOneTurnSquare⟩
  · intro P _ Q _ h
    exact CommutationPentagon.toRectangle_injective h
  · intro r hr
    obtain ⟨hre, hrc⟩ := Finset.mem_filter.mp hr
    obtain ⟨P, rfl⟩ := exists_pentagon_toRectangle C r hrc
    exact ⟨P, (mem_fullCommutationPentagons P).mpr
      (P.isEmpty_toRectangle.mp ((GridRectangleBetween.mem_emptyRectangles _).mp hre)), rfl⟩
  · intro P hP
    rw [← LaurentPolynomial.T_add, fullCommutationPentagon_oCount_eq G C P
      ((mem_fullCommutationPentagons P).mp hP)]
    congr 1
    omega

end OnLeConjecture.KnotFloer.GridFull
