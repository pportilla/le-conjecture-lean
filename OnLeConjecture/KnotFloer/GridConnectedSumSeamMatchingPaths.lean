/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamMatchingWeights
public import Mathlib.Data.Matrix.Basic

/-!
# The normalized complementary-state matrix

Rows and columns are the increasing sources of the complementary-state
pairing. The row normalization divides by that row's proved full matching
coefficient. Its diagonal is one. Subtracting the identity leaves actual
nonmatching empty-rectangle steps. The X-Maslov grading is nondecreasing
along these steps, with its exact increase given by the X count.
Valid auxiliary diagrams with same-block transpositions prove that any
rectangle on a return path avoids both diagonal blocks. A strict order
on the remaining steps is not assumed here.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- Increasing sources index the disjoint pairs in the full seam complement. -/
abbrev SeamMatchingSource (n m : ℕ) :=
  {x : SeamComplement n m // SeamComplementSource x}

/-- The full source-to-target coefficient matrix, normalized by each target row's unit. -/
def seamMatchingMatrix
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommSemiring R] :
    Matrix (SeamMatchingSource n m) (SeamMatchingSource n m) (LaurentPolynomial R) :=
  fun y x => LaurentPolynomial.T (-(seamComplementOCount G H y.val : ℤ)) *
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R
      x.val.val (seamComplementPartner y.val).val

/-- The matching rectangle supplies the unit diagonal, without an additional invertibility input. -/
@[simp] theorem seamMatchingMatrix_diag
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommSemiring R] (x : SeamMatchingSource n m) :
    seamMatchingMatrix G H hG hH R x x = 1 := by
  change LaurentPolynomial.T _ * _ = _
  rw [connectedSumSeamGrid_complement_coefficient G H hG hH x.val x.property R,
    ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

/-- The off-diagonal internal transition matrix. -/
def seamMatchingTransitionMatrix
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    Matrix (SeamMatchingSource n m) (SeamMatchingSource n m) (LaurentPolynomial R) := by
  classical
  exact seamMatchingMatrix G H hG hH R - 1

@[simp] theorem seamMatchingTransitionMatrix_diag
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (x : SeamMatchingSource n m) :
    seamMatchingTransitionMatrix G H hG hH R x x = 0 := by
  classical
  simp [seamMatchingTransitionMatrix]

theorem seamMatchingTransitionMatrix_offDiag
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m) (hxy : x ≠ y) :
    seamMatchingTransitionMatrix G H hG hH R y x = seamMatchingMatrix G H hG hH R y x := by
  classical
  simp [seamMatchingTransitionMatrix, hxy.symm]

/-- A step consists of a full empty rectangle followed by the selected matching inverse. -/
def SeamMatchingStep (x y : SeamMatchingSource n m) : Prop :=
  x ≠ y ∧ ∃ r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val, r.IsEmpty

/-- Every covered square lies in one of the two off-diagonal blocks. -/
def SeamDiagonalBlockFree (r : GridRectangle (n + m + 1)) : Prop :=
  ∀ c d : Fin (n + m + 1), (c, d) ∈ r.coveredSquares →
    (c.val < n ∧ n ≤ d.val) ∨ (n ≤ c.val ∧ d.val < n)

/-- A nonzero off-diagonal entry has an actual empty-rectangle witness. -/
theorem seamMatchingStep_of_transition_ne_zero
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m)
    (h : seamMatchingTransitionMatrix G H hG hH R y x ≠ 0) : SeamMatchingStep x y := by
  classical
  have hxy : x ≠ y := by
    rintro rfl
    exact h (seamMatchingTransitionMatrix_diag G H hG hH R x)
  rw [seamMatchingTransitionMatrix_offDiag G H hG hH R x y hxy] at h
  have hc : laurentCoefficient (connectedSumSeamGrid G H hG hH) R
      x.val.val (seamComplementPartner y.val).val ≠ 0 := by
    intro hc
    exact h (by simp [seamMatchingMatrix, hc])
  have hn : (emptyRectangles x.val.val (seamComplementPartner y.val).val).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    exact hc (by rw [laurentCoefficient_eq, hn, Finset.sum_empty])
  obtain ⟨r, hr⟩ := hn
  exact ⟨hxy, r, (mem_emptyRectangles r).mp hr⟩

/-- Row normalization makes the exponent depend only on the two source Maslov gradings. -/
theorem seamMatchingMatrix_support_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommSemiring R] (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ (seamMatchingMatrix G H hG hH R y x).coeff.support) :
    2 * j = (connectedSumSeamGrid G H hG hH).maslovOℤ y.val.val -
      (connectedSumSeamGrid G H hG hH).maslovOℤ x.val.val := by
  have hs := AddMonoidAlgebra.support_coeff_single_mul_subset
    (laurentCoefficient (connectedSumSeamGrid G H hG hH) R
      x.val.val (seamComplementPartner y.val).val)
    (1 : R) (-(seamComplementOCount G H y.val : ℤ)) hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨r, hr, rfl⟩ := exists_rectangle_of_mem_support_laurentCoefficient
    (connectedSumSeamGrid G H hG hH) R hk
  have hd := laurentMaslovDegree_add_card_OColumns (connectedSumSeamGrid G H hG hH)
    r ((mem_emptyRectangles r).mp hr) 0
  have hm := connectedSumSeamGrid_complement_maslov G H hG hH y.val y.property
  simp only [zero_add, laurentMaslovDegree, mul_zero, sub_zero] at hd
  omega

/-- The selected matching rectangle drops the X-Maslov grading by one. -/
theorem seamMatching_maslovX_partner
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (y : SeamMatchingSource n m) :
    (connectedSumSeamGrid G H hG hH).maslovXℤ y.val.val =
      (connectedSumSeamGrid G H hG hH).maslovXℤ (seamComplementPartner y.val).val + 1 := by
  let K := connectedSumSeamGrid G H hG hH
  have he := K.maslovX_sub_maslovX_eq_one_sub_two_mul_card
    (seamComplementRectangle y.val) (seamComplementRectangle_isEmpty y.val y.property)
  have hX : (K.XSet ∩ (seamComplementRectangle y.val).toGridRectangle.coveredSquares).card = 0 := by
    change (K.swapMarkings.OSet ∩ _).card = 0
    rw [← K.swapMarkings.card_OColumns,
      connectedSumSeamGrid_complement_XColumns G H hG hH y.val y.property, Finset.card_empty]
  rw [hX, Nat.cast_zero, mul_zero, sub_zero, K.maslovX_eq_intCast,
    K.maslovX_eq_intCast] at he
  exact_mod_cast (show (K.maslovXℤ y.val.val : ℚ) =
    (K.maslovXℤ (seamComplementPartner y.val).val : ℚ) + 1 by linarith)

/-- The exact X-Maslov increase along a rectangle and the following matching inverse. -/
theorem seamMatchingRectangle_maslovX_change
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) (hr : r.IsEmpty) :
    (connectedSumSeamGrid G H hG hH).maslovXℤ y.val.val =
      (connectedSumSeamGrid G H hG hH).maslovXℤ x.val.val +
        2 * (((connectedSumSeamGrid G H hG hH).swapMarkings.OColumns
          r.toGridRectangle).card : ℤ) := by
  let K := connectedSumSeamGrid G H hG hH
  have he := K.maslovX_sub_maslovX_eq_one_sub_two_mul_card r hr
  have hm := seamMatching_maslovX_partner G H hG hH y
  change K.maslovXℤ y.val.val = K.maslovXℤ (seamComplementPartner y.val).val + 1 at hm
  rw [K.maslovX_eq_intCast, K.maslovX_eq_intCast] at he
  change _ = 1 - 2 * ((K.swapMarkings.OSet ∩ _).card : ℚ) at he
  rw [← K.swapMarkings.card_OColumns] at he
  have hh : (K.maslovXℤ x.val.val : ℤ) - K.maslovXℤ (seamComplementPartner y.val).val =
      1 - 2 * (K.swapMarkings.OColumns r.toGridRectangle).card := by exact_mod_cast he
  change K.maslovXℤ y.val.val = K.maslovXℤ x.val.val +
    2 * ((K.swapMarkings.OColumns r.toGridRectangle).card : ℤ)
  omega

/-- X-Maslov grading is nondecreasing along every possible off-diagonal step. -/
theorem SeamMatchingStep.maslovX_mono
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : SeamMatchingSource n m} (h : SeamMatchingStep x y) :
    (connectedSumSeamGrid G H hG hH).maslovXℤ x.val.val ≤
      (connectedSumSeamGrid G H hG hH).maslovXℤ y.val.val := by
  obtain ⟨hne, r, hr⟩ := h
  have he := seamMatchingRectangle_maslovX_change G H hG hH x y r hr
  omega

/-- The weak grading order propagates along any finite alternating path. -/
theorem seamMatchingPath_maslovX_mono
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : SeamMatchingSource n m} (h : Relation.ReflTransGen SeamMatchingStep x y) :
    (connectedSumSeamGrid G H hG hH).maslovXℤ x.val.val ≤
      (connectedSumSeamGrid G H hG hH).maslovXℤ y.val.val := by
  induction h with
  | refl => exact le_rfl
  | @tail y z hp hyz ih => exact ih.trans (hyz.maslovX_mono G H hG hH)

/-- A rectangle in a closed alternating path must avoid every X marking. -/
theorem seamMatchingRectangle_XColumns_eq_empty_of_return_path
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) (hr : r.IsEmpty)
    (hp : Relation.ReflTransGen SeamMatchingStep y x) :
    (connectedSumSeamGrid G H hG hH).swapMarkings.OColumns r.toGridRectangle = ∅ := by
  apply Finset.card_eq_zero.mp
  have he := seamMatchingRectangle_maslovX_change G H hG hH x y r hr
  have hb := seamMatchingPath_maslovX_mono G H hG hH hp
  omega

/-- A complementary state supplies the size bound for the auxiliary diagrams. -/
theorem seamComplement_two_le_size (x : SeamComplement n m) : 2 ≤ n + m + 1 := by
  have hp := seamComplementFirst_lt_second x
  have hq := (seamComplementSecond x).isLt
  change (seamComplementFirst x).val < (seamComplementSecond x).val at hp
  omega

/-- A valid auxiliary diagram whose O permutation exchanges two selected indices. -/
def seamSwapAuxiliaryGrid (hsize : 2 ≤ n + m + 1) (a b : Fin (n + m + 1)) :
    GridDiagram (n + m + 1) where
  O := ⟨Equiv.swap a b⟩
  X := ⟨(Equiv.swap a b).trans (finRotate (n + m + 1))⟩
  disjoint c := (Grid.finRotate_ne_self hsize (Equiv.swap a b c)).symm

@[simp] theorem seamSwapAuxiliaryGrid_O (hsize : 2 ≤ n + m + 1)
    (a b c : Fin (n + m + 1)) :
    (seamSwapAuxiliaryGrid hsize a b).O c = Equiv.swap a b c := rfl

/-- Exchanging indices in the same block preserves the right row block. -/
theorem seamSwapAuxiliaryGrid_O_row_ge (hsize : 2 ≤ n + m + 1)
    (a b : Fin (n + m + 1)) (hab : a.val < n ↔ b.val < n)
    (c : Fin (n + m + 1)) (hc : n ≤ c.val) :
    n ≤ ((seamSwapAuxiliaryGrid hsize a b).O c).val := by
  rw [seamSwapAuxiliaryGrid_O]
  by_cases hca : c = a
  · subst c
    rw [Equiv.swap_apply_left]
    omega
  · by_cases hcb : c = b
    · subst c
      rw [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
      exact hc

/-- Every selected matching rectangle avoids every such block-preserving O marking. -/
theorem seamSwapAuxiliaryGrid_matching_OColumns
    (hsize : 2 ≤ n + m + 1) (a b : Fin (n + m + 1))
    (hab : a.val < n ↔ b.val < n) (y : SeamMatchingSource n m) :
    (seamSwapAuxiliaryGrid hsize a b).OColumns
      (seamComplementRectangle y.val).toGridRectangle = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hh := (mem_toGridRectangle_coveredSquares _).mp ((GridDiagram.mem_OColumns _).mp hc)
  rw [seamComplementRectangle_left, seamComplementRectangle_right,
    Grid.mem_cIco_iff_of_left_lt_right (seamComplementFirst_lt_second y.val)] at hh
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem y.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem y.val)).2
  have hmark := seamSwapAuxiliaryGrid_O_row_ge hsize a b hab c (hp.trans hh.1.1)
  have hr := hh.2
  rw [Grid.mem_cIco_iff_of_left_lt_right y.property] at hr
  change _ ≤ ((seamSwapAuxiliaryGrid hsize a b).O c).val ∧
    ((seamSwapAuxiliaryGrid hsize a b).O c).val < _ at hr
  omega

/-- The auxiliary O-Maslov grading drops by one across each selected matching arrow. -/
theorem seamMatching_auxiliary_maslov_partner
    (hsize : 2 ≤ n + m + 1) (a b : Fin (n + m + 1))
    (hab : a.val < n ↔ b.val < n) (y : SeamMatchingSource n m) :
    (seamSwapAuxiliaryGrid hsize a b).maslovOℤ y.val.val =
      (seamSwapAuxiliaryGrid hsize a b).maslovOℤ (seamComplementPartner y.val).val + 1 := by
  have hd := laurentMaslovDegree_add_card_OColumns (seamSwapAuxiliaryGrid hsize a b)
    (seamComplementRectangle y.val) (seamComplementRectangle_isEmpty y.val y.property) 0
  rw [seamSwapAuxiliaryGrid_matching_OColumns hsize a b hab y, Finset.card_empty] at hd
  simp only [zero_add, Nat.cast_zero, laurentMaslovDegree, mul_zero, sub_zero] at hd
  omega

/-- The exact auxiliary Maslov increase counts the O marks covered by the actual rectangle. -/
theorem seamMatchingRectangle_auxiliary_maslov_change
    (hsize : 2 ≤ n + m + 1) (a b : Fin (n + m + 1))
    (hab : a.val < n ↔ b.val < n) (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) (hr : r.IsEmpty) :
    (seamSwapAuxiliaryGrid hsize a b).maslovOℤ y.val.val =
      (seamSwapAuxiliaryGrid hsize a b).maslovOℤ x.val.val +
        2 * (((seamSwapAuxiliaryGrid hsize a b).OColumns r.toGridRectangle).card : ℤ) := by
  have hd := laurentMaslovDegree_add_card_OColumns (seamSwapAuxiliaryGrid hsize a b) r hr 0
  have hm := seamMatching_auxiliary_maslov_partner hsize a b hab y
  simp only [zero_add, laurentMaslovDegree, mul_zero, sub_zero] at hd
  omega

/-- All block-preserving auxiliary potentials are nondecreasing on the same full steps. -/
theorem SeamMatchingStep.auxiliary_maslov_mono
    (hsize : 2 ≤ n + m + 1) (a b : Fin (n + m + 1))
    (hab : a.val < n ↔ b.val < n) {x y : SeamMatchingSource n m}
    (h : SeamMatchingStep x y) :
    (seamSwapAuxiliaryGrid hsize a b).maslovOℤ x.val.val ≤
      (seamSwapAuxiliaryGrid hsize a b).maslovOℤ y.val.val := by
  obtain ⟨hne, r, hr⟩ := h
  have he := seamMatchingRectangle_auxiliary_maslov_change hsize a b hab x y r hr
  omega

/-- Every finite alternating path respects all auxiliary Maslov potentials. -/
theorem seamMatchingPath_auxiliary_maslov_mono
    (hsize : 2 ≤ n + m + 1) (a b : Fin (n + m + 1))
    (hab : a.val < n ↔ b.val < n) {x y : SeamMatchingSource n m}
    (h : Relation.ReflTransGen SeamMatchingStep x y) :
    (seamSwapAuxiliaryGrid hsize a b).maslovOℤ x.val.val ≤
      (seamSwapAuxiliaryGrid hsize a b).maslovOℤ y.val.val := by
  induction h with
  | refl => exact le_rfl
  | @tail y z hp hyz ih => exact ih.trans (hyz.auxiliary_maslov_mono hsize a b hab)

/-- A rectangle on a closed alternating path contains no square in either diagonal block. -/
theorem seamMatchingRectangle_blockFree_of_return_path
    (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) (hr : r.IsEmpty)
    (hp : Relation.ReflTransGen SeamMatchingStep y x) :
    SeamDiagonalBlockFree r.toGridRectangle := by
  intro a b hab
  by_contra hn
  have hs : a.val < n ↔ b.val < n := by omega
  let hsize := seamComplement_two_le_size x.val
  have he := seamMatchingRectangle_auxiliary_maslov_change hsize a b hs x y r hr
  have hm := seamMatchingPath_auxiliary_maslov_mono hsize a b hs hp
  have hzero : ((seamSwapAuxiliaryGrid hsize a b).OColumns r.toGridRectangle).card = 0 := by
    omega
  have ha : a ∈ (seamSwapAuxiliaryGrid hsize a b).OColumns r.toGridRectangle := by
    rw [GridDiagram.mem_OColumns, seamSwapAuxiliaryGrid_O, Equiv.swap_apply_left]
    exact hab
  have hpos := Finset.card_pos.mpr ⟨a, ha⟩
  omega

end OnLeConjecture.KnotFloer.GridFull
