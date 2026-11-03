/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationHexagon

/-!
# Rectangle coefficients of the full geometric hexagon map

A hexagon is an empty rectangle whose side on the commuted line encloses the two turns in
one specified order. The removed bigon has one O marking. This identifies the hexagon count
with a filtered sum of rectangle weights multiplied by `T (-1)`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} {G : GridDiagram n}

/-- The cyclic order of the two turns for a terminal-side hexagon. -/
theorem terminal_hexagon_rows_iff {s t u v : Fin n} (hst : s ≠ t) :
    (t ∈ Grid.cIco u v ∧ s ∈ Grid.cIoo t v) ↔
      s ∈ Grid.cIco u v ∧ u ∈ Grid.cIco (finRotate n s) (finRotate n t) := by
  rw [Grid.mem_cIco_finRotate_iff_mem_insert_cIoo hst]
  simp only [Finset.mem_insert, Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hst ⊢
  split_ifs <;> omega

/-- The cyclic order of the two turns for an initial-side hexagon. -/
theorem initial_hexagon_rows_iff {s t u v : Fin n} (hst : s ≠ t) :
    (s ∈ Grid.cIco u v ∧ t ∈ Grid.cIoo s v) ↔
      s ∈ Grid.cIco u v ∧ v ∉ Grid.cIco (finRotate n s) (finRotate n t) := by
  rw [Grid.mem_cIco_finRotate_iff_mem_insert_cIoo hst]
  simp only [Finset.mem_insert, Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hst ⊢
  split_ifs <;> omega

/-- The two permitted side and row orders of a geometric commutation hexagon. -/
def enclosesCommutationBigon (C : GridDiagram.ColumnCommutationData G) {x y : GridState n}
    (r : GridRectangleBetween x y) : Prop :=
  (r.right = finRotate n C.column ∧
    C.oppositeTurnRow ∈ Grid.cIco r.bottom r.top ∧
    C.turnRow ∈ Grid.cIoo C.oppositeTurnRow r.top) ∨
  (r.left = finRotate n C.column ∧
    C.turnRow ∈ Grid.cIco r.bottom r.top ∧
    C.oppositeTurnRow ∈ Grid.cIoo C.turnRow r.top)

namespace FullCommutationHexagon

variable {C : GridDiagram.ColumnCommutationData G} {x y : GridState n}

/-- The two orientations never have the same rectangle. -/
theorem toRectangle_injective : Function.Injective
    (toRectangle : FullCommutationHexagon C x y → GridRectangleBetween x y) := by
  intro P Q h
  rcases P with P | P <;> rcases Q with Q | Q
  · exact congrArg Sum.inl (Subsingleton.elim P Q)
  · have he := congrArg GridRectangleBetween.left h
    exact (P.left_ne (he.trans Q.left_eq)).elim
  · have he := congrArg GridRectangleBetween.left h
    exact (Q.left_ne (he.symm.trans P.left_eq)).elim
  · exact congrArg Sum.inr (Subsingleton.elim P Q)

/-- The rectangle under a hexagon encloses the appropriate bigon. -/
theorem enclosesBigon (P : FullCommutationHexagon C x y) :
    enclosesCommutationBigon C P.toRectangle := by
  rcases P with P | P
  · exact Or.inl ⟨P.right_eq, P.lower_mem, P.upper_mem⟩
  · exact Or.inr ⟨P.left_eq, P.lower_mem, P.upper_mem⟩

end FullCommutationHexagon

/-- Every rectangle with the specified side and row order determines a geometric hexagon. -/
theorem exists_hexagon_toRectangle (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (r : GridRectangleBetween x y) (hr : enclosesCommutationBigon C r) :
    ∃ P : FullCommutationHexagon C x y, P.toRectangle = r := by
  rcases hr with ⟨hside, hlow, hupp⟩ | ⟨hside, hlow, hupp⟩
  · exact ⟨.inl ⟨r, hside, hlow, hupp⟩, rfl⟩
  · exact ⟨.inr ⟨r, hside, hlow, hupp⟩, rfl⟩

/-- The hexagon row condition is a turn crossing selected by the target's row band. -/
theorem enclosesCommutationBigon_iff_turnBand (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (r : GridRectangleBetween x y) :
    enclosesCommutationBigon C r ↔
      crossesOneTurnSquare C r ∧
        (if r.left = finRotate n C.column then
          y (finRotate n C.column) ∉
            Grid.cIco (finRotate n C.turnRow) (finRotate n C.oppositeTurnRow)
        else y (finRotate n C.column) ∈
            Grid.cIco (finRotate n C.turnRow) (finRotate n C.oppositeTurnRow)) := by
  classical
  rw [crossesOneTurnSquare_iff]
  simp only [enclosesCommutationBigon,
    terminal_hexagon_rows_iff C.turnRow_ne_oppositeTurnRow,
    initial_hexagon_rows_iff C.turnRow_ne_oppositeTurnRow]
  by_cases hl : r.left = finRotate n C.column
  · have hr : r.right ≠ finRotate n C.column := fun h => r.left_ne_right (hl.trans h.symm)
    have hy : y (finRotate n C.column) = r.top := by rw [← hl]; exact r.map_left
    simp only [hl, hr, hy, if_true, true_and, false_and, false_or, true_or]
  · by_cases hr : r.right = finRotate n C.column
    · have hy : y (finRotate n C.column) = r.bottom := by rw [← hr]; exact r.map_right
      simp only [hl, hr, hy, if_false, true_and, false_and, or_false, or_true]
    · simp only [hl, hr, false_and, or_self]

/-- A crossing rectangle begins on the commuted line exactly when it contains the second square. -/
theorem left_eq_iff_second_turn_square_of_crosses
    (C : GridDiagram.ColumnTurn n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : crossesOneTurnSquare C r) :
    r.left = finRotate n C.column ↔
      (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares := by
  obtain ⟨hside, hrow⟩ := (crossesOneTurnSquare_iff C r).mp hr
  rcases hside with hl | hr
  · have hb : (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares := by
      rw [GridRectangle.mem_coveredSquares]
      constructor
      · change finRotate n C.column ∈ Grid.cIco r.left r.right
        simpa only [← hl] using Grid.left_mem_cIco r.left_ne_right
      · exact hrow
    exact iff_of_true hl hb
  · have hl : r.left ≠ finRotate n C.column := fun h => r.left_ne_right (h.trans hr.symm)
    have hb : (finRotate n C.column, C.turnRow) ∉ r.toGridRectangle.coveredSquares := by
      intro h
      have hc := (GridRectangle.mem_coveredSquares _ _).mp h |>.1
      change finRotate n C.column ∈ Grid.cIco r.left r.right at hc
      rw [hr] at hc
      exact Grid.right_notMem_cIco _ _ hc
    exact iff_of_false hl hb

/-- The hexagon selection is an exclusive-or test on the second square and target row band. -/
theorem enclosesCommutationBigon_iff_xor (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (r : GridRectangleBetween x y) :
    enclosesCommutationBigon C r ↔ crossesOneTurnSquare C r ∧
      Xor ((finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares)
        (y (finRotate n C.column) ∈
          Grid.cIco (finRotate n C.turnRow) (finRotate n C.oppositeTurnRow)) := by
  classical
  rw [enclosesCommutationBigon_iff_turnBand]
  by_cases hc : crossesOneTurnSquare C r
  · have hl := left_eq_iff_second_turn_square_of_crosses C r hc
    by_cases hb : (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares
    · simp only [hc, true_and, hl.mpr hb, if_true, hb, Xor]
      tauto
    · have hnl : r.left ≠ finRotate n C.column := fun h => hb (hl.mp h)
      simp only [hc, true_and, hnl, if_false, hb, Xor]
      tauto
  · simp only [hc, false_and]

variable (G)

open Classical in
/-- The full geometric hexagon coefficient is the selected rectangle sum divided by `U`. -/
theorem laurentCommutationHexagonCoefficient_eq_rectangle_sum
    (R : Type*) [CommSemiring R] (C : GridDiagram.ColumnCommutationData G)
    (x y : GridState n) :
    laurentCommutationHexagonCoefficient G R C x y =
      LaurentPolynomial.T (-1) *
        ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter (enclosesCommutationBigon C),
          LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [laurentCommutationHexagonCoefficient, Finset.mul_sum]
  apply Finset.sum_bij (fun P _ => P.toRectangle)
  · intro P hP
    exact Finset.mem_filter.mpr ⟨(GridRectangleBetween.mem_emptyRectangles _).mpr
      ((mem_fullCommutationHexagons G P).mp hP), P.enclosesBigon⟩
  · intro P _ Q _ h
    exact FullCommutationHexagon.toRectangle_injective h
  · intro r hr
    obtain ⟨hre, hrc⟩ := Finset.mem_filter.mp hr
    obtain ⟨P, rfl⟩ := exists_hexagon_toRectangle C r hrc
    exact ⟨P, (mem_fullCommutationHexagons G P).mpr
      ((GridRectangleBetween.mem_emptyRectangles _).mp hre), rfl⟩
  · intro P _
    rw [← LaurentPolynomial.T_add]
    congr 1
    have h := (fullCommutationHexagon_rectangle_counts G C P).1
    rw [← G.card_OColumns] at h
    omega

open Classical in
/-- The quadratic deformation coefficient records rectangles containing both turn squares. -/
theorem coeff_two_squareWeight_adjacentSquareDeformation
    (R : Type*) [CommSemiring R] (C : GridDiagram.ColumnTurn n)
    {x y : GridState n} (r : GridRectangleBetween x y) :
    (squareWeight (adjacentSquareDeformationWeight G R C.column C.turnRow)
      r.toGridRectangle).coeff 2 =
      if (C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares ∧
        (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares then
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) else 0 := by
  rw [squareWeight_adjacentSquareDeformation]
  by_cases ha : (C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares <;>
    by_cases hb : (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares <;>
      simp only [ha, hb, if_true, if_false, and_self, and_false, false_and] <;>
        simp [mul_add, add_mul]

open Classical in
/-- The geometric hexagon selector is the quadratic term, one single-square term, and the
row-band correction of the linear term. -/
theorem fullCommutationHexagon_rectangle_weight_decomposition
    (R : Type*) [CommSemiring R] [CharP R 2] (C : GridDiagram.ColumnCommutationData G)
    {x y : GridState n} (r : GridRectangleBetween x y) :
    (if enclosesCommutationBigon C r then
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) else 0) =
      (squareWeight (adjacentSquareDeformationWeight G R C.column C.turnRow)
        r.toGridRectangle).coeff 2 +
      (if (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares then
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) else 0) +
      (if y (finRotate n C.column) ∈
          Grid.cIco (finRotate n C.turnRow) (finRotate n C.oppositeTurnRow) then 1 else 0) *
        (squareWeight (adjacentSquareDeformationWeight G R C.column C.turnRow)
          r.toGridRectangle).coeff 1 := by
  rw [coeff_two_squareWeight_adjacentSquareDeformation,
    coeff_one_squareWeight_adjacentSquareDeformation,
    enclosesCommutationBigon_iff_xor]
  by_cases ha : (C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares <;>
    by_cases hb : (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares <;>
      by_cases ht : y (finRotate n C.column) ∈
        Grid.cIco (finRotate n C.turnRow) (finRotate n C.oppositeTurnRow) <;>
          simp only [crossesOneTurnSquare, Xor, ha, hb, ht, not_true_eq_false,
            not_false_eq_true, and_true, and_false, or_true, or_false, if_true, if_false] <;>
              simp [CharTwo.add_self_eq_zero]

end OnLeConjecture.KnotFloer.GridFull
