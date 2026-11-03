/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationChainMap

/-!
# Changing the turn in the linear rectangle operator

Changing the selected row of the turn changes the operator by the
boundary of a concrete diagonal map. Its diagonal entry is the indicator
that the state point on the replaced vertical line lies between the two
turns. The proof uses the cyclic interval crossing identity.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} {R : Type*} [CommRing R] [CharP R 2]

/-- The indicator of the band of grid lines between two turn rows. -/
noncomputable def turnBandCoefficient (R : Type*) [CommSemiring R]
    (C : GridDiagram.ColumnTurn n) (t : Fin n) (x : GridState n) : LaurentPolynomial R :=
  if x (finRotate n C.column) ∈ Grid.cIco (finRotate n C.turnRow) (finRotate n t)
    then 1 else 0

/-- Crossing a shifted row band counts its two boundary rows in characteristic two. -/
theorem shiftedArc_indicator_add
    (p q s t : Fin n) (hpq : p ≠ q) (hst : s ≠ t) :
    (if s ∈ Grid.cIco p q then 1 else 0 : LaurentPolynomial R) +
        (if t ∈ Grid.cIco p q then 1 else 0) =
      (if p ∈ Grid.cIco (finRotate n s) (finRotate n t) then 1 else 0) +
        (if q ∈ Grid.cIco (finRotate n s) (finRotate n t) then 1 else 0) := by
  have hZ := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco_finRotate hpq hst
  split_ifs at hZ ⊢ <;> norm_num at hZ <;> simp [CharTwo.add_self_eq_zero]

open Classical in
/-- The two turn-crossing indicators differ by the state-band indicators at the corners. -/
theorem crossesOneTurnSquare_indicator_add (C : GridDiagram.ColumnTurn n) (t : Fin n)
    (hst : C.turnRow ≠ t) {x y : GridState n} (r : GridRectangleBetween x y) :
    (if crossesOneTurnSquare C r then 1 else 0 : LaurentPolynomial R) +
        (if crossesOneTurnSquare (C.withTurnRow t) r then 1 else 0) =
      turnBandCoefficient R C t x + turnBandCoefficient R C t y := by
  simp only [crossesOneTurnSquare_iff]
  by_cases hl : r.left = finRotate n C.column
  · simp only [hl, true_or, true_and]
    have hx : x (finRotate n C.column) = r.bottom := by rw [← hl, r.bottom_def]
    have hy : y (finRotate n C.column) = r.top := by rw [← hl, r.map_left, r.top_def]
    unfold turnBandCoefficient
    rw [hx, hy]
    exact shiftedArc_indicator_add (R := R) r.bottom r.top C.turnRow t r.bottom_ne_top hst
  · by_cases hr : r.right = finRotate n C.column
    · simp only [hr, or_true, true_and]
      have hx : x (finRotate n C.column) = r.top := by rw [← hr, r.top_def]
      have hy : y (finRotate n C.column) = r.bottom := by rw [← hr, r.map_right, r.bottom_def]
      unfold turnBandCoefficient
      rw [hx, hy, add_comm]
      simpa only [add_comm] using
        shiftedArc_indicator_add (R := R) r.bottom r.top C.turnRow t r.bottom_ne_top hst
    · simp only [hl, hr, false_or, false_and, if_false, zero_add]
      have hxy := r.map_of_ne (finRotate n C.column) (Ne.symm hl) (Ne.symm hr)
      simp only [turnBandCoefficient, hxy, CharTwo.add_self_eq_zero]

/-- The diagonal map recording state points between the turns. -/
noncomputable def turnBandMap (R : Type*) [CommSemiring R]
    (C : GridDiagram.ColumnTurn n) (t : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n where
  toFun c := (Finsupp.linearEquivFunOnFinite (LaurentPolynomial R)
    (LaurentPolynomial R) (GridState n)).symm (fun x => turnBandCoefficient R C t x * c x)
  map_add' c d := by
    apply Finsupp.ext
    intro x
    simp [mul_add]
  map_smul' a c := by
    apply Finsupp.ext
    intro x
    simp [mul_left_comm]

omit [CharP R 2] in
@[simp]
theorem turnBandMap_apply (C : GridDiagram.ColumnTurn n) (t : Fin n)
    (c : LaurentChain R n) (x : GridState n) :
    turnBandMap R C t c x = turnBandCoefficient R C t x * c x := by
  simp [turnBandMap]

/-- Changing the turn is the boundary of the explicit diagonal state-band map. -/
theorem adjacentSquareOperator_turn_change (G : GridDiagram n)
    (C : GridDiagram.ColumnTurn n) (t : Fin n) (hst : C.turnRow ≠ t) :
    adjacentSquareOperator G R C.column C.turnRow 1 +
        adjacentSquareOperator G R C.column t 1 =
      laurentDifferential G R ∘ₗ turnBandMap R C t +
        turnBandMap R C t ∘ₗ laurentDifferential G R := by
  classical
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.add_apply, adjacentSquareOperator,
    polynomialCoefficientOperator_apply_apply, laurentDifferential_apply_apply, turnBandMap_apply]
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [turnBandMap_apply]
  have hcoeff :
      (squareWeightedCoefficient (adjacentSquareDeformationWeight G R C.column C.turnRow)
        x y).coeff 1 +
      (squareWeightedCoefficient (adjacentSquareDeformationWeight G R C.column t)
        x y).coeff 1 =
      (turnBandCoefficient R C t x + turnBandCoefficient R C t y) *
        laurentCoefficient G R x y := by
    simp only [squareWeightedCoefficient, Polynomial.finsetSum_coeff, laurentCoefficient_eq,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have ht := coeff_one_squareWeight_adjacentSquareDeformation (R := R)
      G (C.withTurnRow t) r
    have hs := coeff_one_squareWeight_adjacentSquareDeformation (R := R) G C r
    rw [hs, ht]
    rw [← crossesOneTurnSquare_indicator_add (R := R) C t hst r]
    split_ifs <;> simp_all [add_mul]
  calc
    _ = c x * ((squareWeightedCoefficient
        (adjacentSquareDeformationWeight G R C.column C.turnRow) x y).coeff 1 +
        (squareWeightedCoefficient (adjacentSquareDeformationWeight G R C.column t) x y).coeff 1) :=
      (mul_add _ _ _).symm
    _ = _ := by rw [hcoeff]; ring

end OnLeConjecture.KnotFloer.GridFull
