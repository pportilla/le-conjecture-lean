/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationPentagon

/-!
# The diagonal Laurent change for an adjacent column swap

Swapping the O markings of two adjacent columns changes every state Maslov
grade by one or minus one. The resulting diagonal Laurent change has
Maslov degree one and intertwines the full differentials. It is an
auxiliary factor in the degree-zero pentagon map, not a filtered move map.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-- The diagonal exponent needed to compare O weights across an adjacent column swap. -/
noncomputable def commutationGaugeExponent (G : GridDiagram n) (C : GridDiagram.ColumnTurn n)
    (x : GridState n) : ℤ := by
  classical
  exact if x (finRotate n C.column) ∈
    Grid.cIco (finRotate n (G.O C.column)) (finRotate n (G.O (finRotate n C.column)))
    then 0 else -1

/-- The diagonal exponent records the exact integer change of the state Maslov grading. -/
theorem maslov_swapColumns_eq_gauge (G : GridDiagram n) (C : GridDiagram.ColumnTurn n)
    (x : GridState n) :
    (G.swapColumns C.column (finRotate n C.column)).maslovOℤ x =
      G.maslovOℤ x + 2 * commutationGaugeExponent G C x + 1 := by
  rw [G.maslovOℤ_swapColumns_finRotate C.column_ne_next, commutationGaugeExponent]
  split_ifs <;> omega

/-- Rectangle O counts change by the difference of the diagonal exponents at their corners. -/
theorem commutationGaugeExponent_rectangle (G : GridDiagram n) (C : GridDiagram.ColumnTurn n)
    {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    ((G.swapColumns C.column (finRotate n C.column)).OColumns r.toGridRectangle).card +
        commutationGaugeExponent G C x =
      (G.OColumns r.toGridRectangle).card + commutationGaugeExponent G C y := by
  have hG := laurentMaslovDegree_add_card_OColumns G r hr 0
  have hH := laurentMaslovDegree_add_card_OColumns
    (G.swapColumns C.column (finRotate n C.column)) r hr 0
  simp only [laurentMaslovDegree, zero_add, mul_zero, sub_zero] at hG hH
  rw [maslov_swapColumns_eq_gauge, maslov_swapColumns_eq_gauge] at hH
  omega

/-- Multiplication of each grid-state coefficient by its prescribed Laurent power. -/
noncomputable def diagonalLaurentMap (R : Type*) [CommSemiring R]
    (e : GridState n → ℤ) : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n where
  toFun c := (Finsupp.linearEquivFunOnFinite (LaurentPolynomial R)
    (LaurentPolynomial R) (GridState n)).symm (fun x => LaurentPolynomial.T (e x) * c x)
  map_add' c d := by
    apply Finsupp.ext
    intro x
    simp [mul_add]
  map_smul' a c := by
    apply Finsupp.ext
    intro x
    simp [mul_left_comm]

@[simp]
theorem diagonalLaurentMap_apply (R : Type*) [CommSemiring R] (e : GridState n → ℤ)
    (c : LaurentChain R n) (x : GridState n) :
    diagonalLaurentMap R e c x = LaurentPolynomial.T (e x) * c x := by
  simp [diagonalLaurentMap]

/-- The diagonal Laurent map is invertible, with opposite exponents. -/
noncomputable def diagonalLaurentEquiv (R : Type*) [CommSemiring R] (e : GridState n → ℤ) :
    LaurentChain R n ≃ₗ[LaurentPolynomial R] LaurentChain R n :=
  { diagonalLaurentMap R e with
    invFun := diagonalLaurentMap R (fun x => -e x)
    left_inv := by
      intro c
      apply Finsupp.ext
      intro x
      change diagonalLaurentMap R (fun x => -e x) (diagonalLaurentMap R e c) x = c x
      simp only [diagonalLaurentMap_apply, ← mul_assoc, ← LaurentPolynomial.T_add,
        neg_add_cancel, LaurentPolynomial.T_zero, one_mul]
    right_inv := by
      intro c
      apply Finsupp.ext
      intro x
      change diagonalLaurentMap R e (diagonalLaurentMap R (fun x => -e x) c) x = c x
      simp only [diagonalLaurentMap_apply, ← mul_assoc, ← LaurentPolynomial.T_add,
        add_neg_cancel, LaurentPolynomial.T_zero, one_mul] }

@[simp]
theorem diagonalLaurentEquiv_apply (R : Type*) [CommSemiring R] (e : GridState n → ℤ)
    (c : LaurentChain R n) (x : GridState n) :
    diagonalLaurentEquiv R e c x = LaurentPolynomial.T (e x) * c x :=
  diagonalLaurentMap_apply R e c x

/-- The explicit diagonal Laurent change for an adjacent column swap. -/
noncomputable def commutationGauge (G : GridDiagram n) (R : Type*) [CommSemiring R]
    (C : GridDiagram.ColumnTurn n) :
    LaurentChain R n ≃ₗ[LaurentPolynomial R] LaurentChain R n :=
  diagonalLaurentEquiv R (commutationGaugeExponent G C)

@[simp]
theorem commutationGauge_apply (G : GridDiagram n) (R : Type*) [CommSemiring R]
    (C : GridDiagram.ColumnTurn n) (c : LaurentChain R n) (x : GridState n) :
    commutationGauge G R C c x = LaurentPolynomial.T (commutationGaugeExponent G C x) * c x :=
  diagonalLaurentEquiv_apply R _ c x

/-- The rectangle weight identity after the diagonal change. -/
theorem laurentCoefficient_mul_commutationGauge (G : GridDiagram n) (R : Type*)
    [CommSemiring R] (C : GridDiagram.ColumnTurn n) (x y : GridState n) :
    LaurentPolynomial.T (commutationGaugeExponent G C x) *
        laurentCoefficient (G.swapColumns C.column (finRotate n C.column)) R x y =
      LaurentPolynomial.T (commutationGaugeExponent G C y) * laurentCoefficient G R x y := by
  classical
  simp only [laurentCoefficient_eq, Finset.mul_sum, ← LaurentPolynomial.T_add]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  have h := commutationGaugeExponent_rectangle G C r
    ((GridRectangleBetween.mem_emptyRectangles r).mp hr)
  omega

/-- The diagonal Laurent change intertwines the actual full differentials. -/
theorem laurentDifferential_commutationGauge (G : GridDiagram n) (R : Type*)
    [CommSemiring R] (C : GridDiagram.ColumnTurn n) (c : LaurentChain R n) :
    laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R
        (commutationGauge G R C c) = commutationGauge G R C (laurentDifferential G R c) := by
  classical
  apply Finsupp.ext
  intro y
  rw [commutationGauge_apply, laurentDifferential_apply_apply,
    laurentDifferential_apply_apply]
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [commutationGauge_apply]
  calc
    _ = c x * (LaurentPolynomial.T (commutationGaugeExponent G C x) *
        laurentCoefficient (G.swapColumns C.column (finRotate n C.column)) R x y) := by ring
    _ = c x * (LaurentPolynomial.T (commutationGaugeExponent G C y) *
        laurentCoefficient G R x y) := by rw [laurentCoefficient_mul_commutationGauge]
    _ = _ := by ring

/-- The auxiliary diagonal change raises the actual Maslov degree by one. -/
theorem commutationGauge_maslovDegree (G : GridDiagram n) (C : GridDiagram.ColumnTurn n)
    (k : ℤ) (x : GridState n) :
    laurentMaslovDegree (G.swapColumns C.column (finRotate n C.column))
        (commutationGaugeExponent G C x + k) x = laurentMaslovDegree G k x + 1 := by
  simp only [laurentMaslovDegree, maslov_swapColumns_eq_gauge]
  ring

end OnLeConjecture.KnotFloer.GridFull
