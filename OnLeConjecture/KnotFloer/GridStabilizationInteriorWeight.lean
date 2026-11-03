/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationInteriorRectangle
public import OnLeConjecture.KnotFloer.GridFullStabilizationBasic

/-!
# Weights of the three-rectangle stabilization factorization

A transported rectangle covering the split X square contains exactly one additional O
marking, the new O. Its three empty factors therefore have product weight U times the
old rectangle weight. This complements the avoided-square case in the pinned TauCeti
`OColumns_stabilizeX_insertPoint` theorem.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- A lift through the center contains the new O and the embedded old O markings. -/
theorem OColumns_stabilization_lift_of_splitSquare_mem {x y : GridState n}
    (r : GridRectangleBetween x y) (hXs : (s, G.X s) ∈ r.toGridRectangle.coveredSquares) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        (r.insertPoint s.succ (G.X s).succ).toGridRectangle =
      insert s.castSucc ((G.OColumns r.toGridRectangle).map s.castSucc.succAboveEmb) := by
  classical
  ext c
  simp only [GridDiagram.mem_OColumns, Finset.mem_insert, Finset.mem_map,
    Fin.coe_succAboveEmb, GridRectangleBetween.mem_coveredSquares_insertPoint_succ_succ]
  induction c using Fin.succAboveCases s.castSucc with
  | x =>
    simp only [GridDiagram.stabilizeX_O, GridState.insertPoint_apply_newColumn,
      Fin.predAbove_castSucc_self, hXs, true_or]
  | p i =>
    simp only [GridDiagram.stabilizeX_O, GridState.insertPoint_apply_succAbove,
      Fin.predAbove_succAbove, Fin.succAbove_ne, false_or,
      Fin.succAbove_right_inj, exists_eq_right]

/-- The new O increases the transported rectangle's O count by exactly one. -/
theorem card_OColumns_stabilization_lift_of_splitSquare_mem {x y : GridState n}
    (r : GridRectangleBetween x y) (hXs : (s, G.X s) ∈ r.toGridRectangle.coveredSquares) :
    ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
      (r.insertPoint s.succ (G.X s).succ).toGridRectangle).card =
      (G.OColumns r.toGridRectangle).card + 1 := by
  rw [OColumns_stabilization_lift_of_splitSquare_mem G s r hXs,
    Finset.card_insert_of_notMem, Finset.card_map]
  simp only [Finset.mem_map, Fin.coe_succAboveEmb, not_exists, not_and]
  intro c _ hc
  exact Fin.succAbove_ne s.castSucc c hc

/-- The Laurent O weights multiply under the disjoint three-rectangle partition. -/
theorem interiorRectangles_laurentWeight (R : Type*) [CommSemiring R]
    {x y : GridState n} (r : GridRectangleBetween x y) (p : Fin n)
    (hp : p ∈ Grid.cIoo r.left r.right) (hrow : x p ∈ Grid.cIoo (x r.left) (x r.right)) :
    (LaurentPolynomial.T ((G.OColumns (interiorRectangleOne r p hp).toGridRectangle).card : ℤ) :
        LaurentPolynomial R) *
      LaurentPolynomial.T ((G.OColumns (interiorRectangleTwo r p hp).toGridRectangle).card : ℤ) *
      LaurentPolynomial.T ((G.OColumns (interiorRectangleThree r p hp).toGridRectangle).card : ℤ) =
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  have h := interiorRectangles_weight r p hp (oSquareWeight (R := R) G) hrow
  change squareWeight (oSquareWeight G) (interiorRectangleOne r p hp).toGridRectangle *
    squareWeight (oSquareWeight G) (interiorRectangleTwo r p hp).toGridRectangle *
    squareWeight (oSquareWeight G) (interiorRectangleThree r p hp).toGridRectangle =
    squareWeight (oSquareWeight G) r.toGridRectangle at h
  simpa only [squareWeight_oSquareWeight, laurentSpecialization_OMonomial] using h

/-- The three-rectangle factorization has exactly U times the old Laurent weight. -/
theorem stabilizationInteriorRectangles_laurentWeight (R : Type*) [CommSemiring R]
    {x y : GridState n} (r : GridRectangleBetween x y)
    (hXs : (s, G.X s) ∈ r.toGridRectangle.coveredSquares)
    (hp : s.succ ∈ Grid.cIoo (r.insertPoint s.succ (G.X s).succ).left
      (r.insertPoint s.succ (G.X s).succ).right) :
    let G' := G.stabilizeX s.castSucc (G.X s).castSucc s
    let r' := r.insertPoint s.succ (G.X s).succ
    (LaurentPolynomial.T
      ((G'.OColumns (interiorRectangleOne r' s.succ hp).toGridRectangle).card : ℤ) :
        LaurentPolynomial R) *
      LaurentPolynomial.T
        ((G'.OColumns (interiorRectangleTwo r' s.succ hp).toGridRectangle).card : ℤ) *
      LaurentPolynomial.T
        ((G'.OColumns (interiorRectangleThree r' s.succ hp).toGridRectangle).card : ℤ) =
        LaurentPolynomial.T 1 * LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  dsimp only
  have hi := (stabilizationCenter_mem_interior_iff G s r).mpr hXs
  rw [GridRectangleBetween.mem_toGridRectangle_interior] at hi
  have hrow : x.insertPoint s.succ (G.X s).succ s.succ ∈
      Grid.cIoo (x.insertPoint s.succ (G.X s).succ (r.insertPoint s.succ (G.X s).succ).left)
        (x.insertPoint s.succ (G.X s).succ (r.insertPoint s.succ (G.X s).succ).right) := by
    simpa only [GridState.insertPoint_apply_newColumn] using hi.2
  rw [interiorRectangles_laurentWeight _ R _ _ hp hrow,
    card_OColumns_stabilization_lift_of_splitSquare_mem G s r hXs]
  simp only [Nat.cast_add, Nat.cast_one, LaurentPolynomial.T_add, mul_comm]

/-- Inverting the additional O weight recovers exactly the old rectangle weight. -/
theorem stabilization_lift_normalized_laurentWeight (R : Type*) [CommSemiring R]
    {x y : GridState n} (r : GridRectangleBetween x y)
    (hXs : (s, G.X s) ∈ r.toGridRectangle.coveredSquares) :
    (LaurentPolynomial.T (-1) : LaurentPolynomial R) *
      LaurentPolynomial.T
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          (r.insertPoint s.succ (G.X s).succ).toGridRectangle).card : ℤ) =
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [card_OColumns_stabilization_lift_of_splitSquare_mem G s r hXs,
    ← LaurentPolynomial.T_add]
  congr 1
  push_cast
  omega

end OnLeConjecture.KnotFloer.GridFull
