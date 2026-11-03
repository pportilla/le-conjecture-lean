/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamMatching

/-!
# Full rectangle weights of the complementary-state pairing

The first two southwest columns give an empty rectangle when their rows
are increasing. A northeast point lies inside the opposite rectangle.
Every X marking is excluded. Only the relocated southwest O marking can
occur, so the full coefficient is one or U. Its inverse has filtration
shift (k,0), where k is this O count, and Maslov degree one. No bound on
composed matching paths or transferred differential is asserted.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The rectangle oriented from the first southwest column to the second. -/
def seamComplementRectangle (x : SeamComplement n m) :
    GridRectangleBetween x.val (seamComplementPartner x).val :=
  ofSwapColumns _ _ (seamComplementFirst x) (seamComplementSecond x)
    (seamComplementFirst_ne_second x) rfl

@[simp] theorem seamComplementRectangle_left (x : SeamComplement n m) :
    (seamComplementRectangle x).left = seamComplementFirst x := by
  unfold seamComplementRectangle
  exact ofSwapColumns_left _ _ _ _ _ _

@[simp] theorem seamComplementRectangle_right (x : SeamComplement n m) :
    (seamComplementRectangle x).right = seamComplementSecond x := by
  unfold seamComplementRectangle
  exact ofSwapColumns_right _ _ _ _ _ _

@[simp] theorem seamComplementRectangle_bottom (x : SeamComplement n m) :
    (seamComplementRectangle x).bottom = x.val (seamComplementFirst x) := by
  rw [bottom_def, seamComplementRectangle_left]

@[simp] theorem seamComplementRectangle_top (x : SeamComplement n m) :
    (seamComplementRectangle x).top = x.val (seamComplementSecond x) := by
  rw [top_def, seamComplementRectangle_right]

/-- Consecutive southwest columns have no state points in the intervening low-row rectangle. -/
theorem seamComplementRectangle_isEmpty (x : SeamComplement n m) (hx : SeamComplementSource x) :
    (seamComplementRectangle x).IsEmpty := by
  unfold SeamComplementSource at hx
  have hpq : (seamComplementFirst x).val < (seamComplementSecond x).val :=
    seamComplementFirst_lt_second x
  have htop := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x)).2
  rw [isEmpty_iff_forall_notMem_cIoo]
  intro c hc hr
  rw [seamComplementRectangle_left, seamComplementRectangle_right, Grid.mem_cIoo,
    if_pos hpq] at hc
  have hhigh := seamComplement_between_row_gt x c hc.2.1 hc.2.2
  rw [seamComplementRectangle_bottom, seamComplementRectangle_top, Grid.mem_cIoo,
    if_pos hx] at hr
  omega

/-- A northeast state point belongs to the interior of the opposite rectangle. -/
theorem seamComplementRectangle_swap_not_isEmpty
    (x : SeamComplement n m) (hx : SeamComplementSource x) :
    ¬ (seamComplementRectangle x).swapSides.IsEmpty := by
  obtain ⟨c, hc⟩ := (seamNortheastColumns_nonempty_iff x.val).mpr x.property
  obtain ⟨hcfirst, hchigh⟩ := (mem_seamNortheastColumns _ _).mp hc
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x)
  have hpq : (seamComplementFirst x).val < (seamComplementSecond x).val :=
    seamComplementFirst_lt_second x
  have hcol : c ∈ Grid.cIoo (seamComplementRectangle x).swapSides.left
      (seamComplementRectangle x).swapSides.right := by
    rw [swapSides_left, swapSides_right, seamComplementRectangle_right,
      seamComplementRectangle_left, Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨(seamComplementFirst_ne_second x).symm, Or.inr (by omega)⟩
  have hrow : x.val c ∈ Grid.cIoo (seamComplementRectangle x).swapSides.bottom
      (seamComplementRectangle x).swapSides.top := by
    rw [swapSides_bottom, swapSides_top, seamComplementRectangle_top,
      seamComplementRectangle_bottom, Grid.mem_cIoo,
      if_neg (by unfold SeamComplementSource at hx; omega)]
    refine ⟨fun h => (seamComplementFirst_ne_second x).symm (x.val.toPerm.injective h), ?_⟩
    exact Or.inl (by omega)
  intro he
  exact ((isEmpty_iff_forall_notMem_cIoo _).mp he) c hcol hrow

/-- Exactly one empty rectangle contributes to each selected full coefficient. -/
theorem seamComplementRectangle_emptyRectangles
    (x : SeamComplement n m) (hx : SeamComplementSource x) :
    emptyRectangles x.val (seamComplementPartner x).val = {seamComplementRectangle x} := by
  classical
  ext r
  rcases (seamComplementRectangle x).eq_or_eq_swapSides r with rfl | rfl <;>
    simp [seamComplementRectangle_isEmpty x hx, seamComplementRectangle_swap_not_isEmpty x hx,
      swapSides_ne_self]

/-- Every column at or after the shared column has a second-block index. -/
theorem exists_seamRight_of_le (c : Fin (n + m + 1)) (hc : n ≤ c.val) :
    ∃ a : Fin (m + 1), c = seamRight n m a := by
  refine ⟨⟨c.val - n, by have := c.isLt; omega⟩, ?_⟩
  apply Fin.ext
  change c.val = n + (c.val - n)
  omega

/-- Every X row in the right block is at least n. -/
theorem connectedSumSeamGrid_X_row_ge
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (c : Fin (n + m + 1)) (hc : n ≤ c.val) :
    n ≤ ((connectedSumSeamGrid G H hG hH).X c).val := by
  obtain ⟨a, rfl⟩ := exists_seamRight_of_le c hc
  change n ≤ (seamState G.X H.X (seamRight n m a)).val
  by_cases ha : H.X a = 0
  · rw [seamState_right_of_zero _ _ _ ha, hG, seamLeft_val, Fin.val_last]
  · rw [seamState_right_of_ne_zero _ _ _ ha, seamRight_val]
    omega

/-- The unique right-block column whose O row lies at most n. -/
theorem connectedSumSeamGrid_O_row_le_iff
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (c : Fin (n + m + 1)) (hc : n ≤ c.val) :
    ((connectedSumSeamGrid G H hG hH).O c).val ≤ n ↔
      c = seamRight n m (H.O.toPerm.symm 0) := by
  obtain ⟨a, rfl⟩ := exists_seamRight_of_le c hc
  change (seamState G.O H.O (seamRight n m a)).val ≤ n ↔ _
  rw [seamState_right_row_le_iff]
  constructor
  · intro ha
    apply congrArg (seamRight n m)
    exact (H.O.toPerm.eq_symm_apply).mpr ha
  · intro ha
    have he := seamRight_injective ha
    rw [he]
    exact H.O.toPerm.apply_symm_apply 0

/-- The relocated O square has the first factor's last O row. -/
theorem connectedSumSeamGrid_relocated_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) :
    (connectedSumSeamGrid G H hG hH).O (seamRight n m (H.O.toPerm.symm 0)) =
      seamLeft n m (G.O (Fin.last n)) :=
  seamState_right_of_zero G.O H.O _ (H.O.toPerm.apply_symm_apply 0)

/-- The selected rectangle avoids every X marking. -/
theorem connectedSumSeamGrid_complement_XColumns
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x) :
    (connectedSumSeamGrid G H hG hH).swapMarkings.OColumns
      (seamComplementRectangle x).toGridRectangle = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hh := (mem_toGridRectangle_coveredSquares _).mp
    ((GridDiagram.mem_OColumns _).mp hc)
  rw [seamComplementRectangle_left, seamComplementRectangle_right,
    Grid.mem_cIco_iff_of_left_lt_right (seamComplementFirst_lt_second x)] at hh
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x)).2
  have hmark := connectedSumSeamGrid_X_row_ge G H hG hH c (hp.trans hh.1.1)
  have hr := hh.2
  rw [Grid.mem_cIco_iff_of_left_lt_right hx] at hr
  change _ ≤ ((connectedSumSeamGrid G H hG hH).X c).val ∧
    ((connectedSumSeamGrid G H hG hH).X c).val < _ at hr
  omega

/-- The full O-column set is either empty or the singleton relocated O column. -/
theorem connectedSumSeamGrid_complement_OColumns
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x) :
    (connectedSumSeamGrid G H hG hH).OColumns (seamComplementRectangle x).toGridRectangle =
      if (seamRight n m (H.O.toPerm.symm 0), seamLeft n m (G.O (Fin.last n))) ∈
          (seamComplementRectangle x).toGridRectangle.coveredSquares
      then {seamRight n m (H.O.toPerm.symm 0)} else ∅ := by
  classical
  let K := connectedSumSeamGrid G H hG hH
  let b := seamRight n m (H.O.toPerm.symm 0)
  have hsub : K.OColumns (seamComplementRectangle x).toGridRectangle ⊆ {b} := by
    intro c hc
    have hh := (mem_toGridRectangle_coveredSquares _).mp ((GridDiagram.mem_OColumns K).mp hc)
    rw [seamComplementRectangle_left, seamComplementRectangle_right,
      Grid.mem_cIco_iff_of_left_lt_right (seamComplementFirst_lt_second x)] at hh
    have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x)).1
    have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x)).2
    have hr := hh.2
    rw [Grid.mem_cIco_iff_of_left_lt_right hx] at hr
    apply Finset.mem_singleton.mpr
    exact (connectedSumSeamGrid_O_row_le_iff G H hG hH c (hp.trans hh.1.1)).mp
      ((Nat.le_of_lt hr.2).trans hq)
  have hb : b ∈ K.OColumns (seamComplementRectangle x).toGridRectangle ↔
      (b, seamLeft n m (G.O (Fin.last n))) ∈
        (seamComplementRectangle x).toGridRectangle.coveredSquares := by
    rw [GridDiagram.mem_OColumns, connectedSumSeamGrid_relocated_O]
  split_ifs with h
  · apply Finset.Subset.antisymm hsub
    intro c hc
    have he := Finset.mem_singleton.mp hc
    subst c
    exact hb.mpr h
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have he := Finset.mem_singleton.mp (hsub hc)
    subst c
    exact h (hb.mp hc)

/-- The only possible O count of an increasing selected rectangle. -/
def seamComplementOCount (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (x : SeamComplement n m) : ℕ :=
  if (seamRight n m (H.O.toPerm.symm 0), seamLeft n m (G.O (Fin.last n))) ∈
      (seamComplementRectangle x).toGridRectangle.coveredSquares then 1 else 0

theorem seamComplementOCount_eq_zero_or_one
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1)) (x : SeamComplement n m) :
    seamComplementOCount G H x = 0 ∨ seamComplementOCount G H x = 1 := by
  unfold seamComplementOCount
  split_ifs <;> simp

theorem connectedSumSeamGrid_complement_O_count
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x) :
    ((connectedSumSeamGrid G H hG hH).OColumns (seamComplementRectangle x).toGridRectangle).card =
      seamComplementOCount G H x := by
  rw [connectedSumSeamGrid_complement_OColumns G H hG hH x hx]
  unfold seamComplementOCount
  split_ifs <;> simp

/-- The actual full coefficient of every pair in the complement is one or U. -/
theorem connectedSumSeamGrid_complement_coefficient
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x)
    (R : Type*) [CommSemiring R] :
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R x.val (seamComplementPartner x).val =
      LaurentPolynomial.T (seamComplementOCount G H x : ℤ) := by
  rw [laurentCoefficient_eq, seamComplementRectangle_emptyRectangles x hx,
    Finset.sum_singleton, connectedSumSeamGrid_complement_O_count G H hG hH x hx]

/-- The reciprocal Laurent monomial is an actual inverse of the full matrix coefficient. -/
theorem connectedSumSeamGrid_complement_coefficient_inverse
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x)
    (R : Type*) [CommSemiring R] :
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R x.val (seamComplementPartner x).val *
      LaurentPolynomial.T (-(seamComplementOCount G H x : ℤ)) = 1 := by
  rw [connectedSumSeamGrid_complement_coefficient G H hG hH x hx R,
    ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- The O count is precisely the increase in Alexander grading across the selected arrow. -/
theorem connectedSumSeamGrid_complement_alexander
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x) :
    (connectedSumSeamGrid G H hG hH).alexander x.val + seamComplementOCount G H x =
      (connectedSumSeamGrid G H hG hH).alexander (seamComplementPartner x).val := by
  let K := connectedSumSeamGrid G H hG hH
  let r := seamComplementRectangle x
  have hXc : (K.XSet ∩ r.toGridRectangle.coveredSquares).card = 0 := by
    change (K.swapMarkings.OSet ∩ r.toGridRectangle.coveredSquares).card = 0
    rw [← K.swapMarkings.card_OColumns, connectedSumSeamGrid_complement_XColumns G H hG hH x hx,
      Finset.card_empty]
  have he := K.alexander_sub_alexander_eq_card_sub_card r
  rw [hXc, ← K.card_OColumns, connectedSumSeamGrid_complement_O_count G H hG hH x hx] at he
  simp only [Nat.cast_zero, zero_sub] at he
  change K.alexander x.val + _ = K.alexander (seamComplementPartner x).val
  linarith

/-- The exact Maslov grading relation, including the possible O factor. -/
theorem connectedSumSeamGrid_complement_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x) :
    (connectedSumSeamGrid G H hG hH).maslovOℤ x.val =
      (connectedSumSeamGrid G H hG hH).maslovOℤ (seamComplementPartner x).val -
        2 * (seamComplementOCount G H x : ℤ) + 1 := by
  have he := laurentMaslovDegree_add_card_OColumns (connectedSumSeamGrid G H hG hH)
    (seamComplementRectangle x) (seamComplementRectangle_isEmpty x hx) 0
  rw [connectedSumSeamGrid_complement_O_count G H hG hH x hx] at he
  simp only [zero_add, laurentMaslovDegree, mul_zero, sub_zero] at he
  omega

/-- The reciprocal of one selected arrow, extended by zero on other basis states. -/
def seamComplementInverse (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (x : SeamComplement n m) (R : Type*) [CommSemiring R] :
    LaurentChain R (n + m + 1) →ₗ[LaurentPolynomial R] LaurentChain R (n + m + 1) :=
  (LaurentPolynomial.T (-(seamComplementOCount G H x : ℤ)) : LaurentPolynomial R) •
    (Finsupp.lsingle x.val ∘ₗ Finsupp.lapply (seamComplementPartner x).val)

@[simp] theorem seamComplementInverse_apply
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (x : SeamComplement n m) (R : Type*) [CommSemiring R] (c : LaurentChain R (n + m + 1)) :
    seamComplementInverse G H x R c = Finsupp.single x.val
      (LaurentPolynomial.T (-(seamComplementOCount G H x : ℤ)) *
        c (seamComplementPartner x).val) := by
  simp [seamComplementInverse, Finsupp.smul_single, smul_eq_mul]

/-- The inverse shift is (k,0), with k exactly zero or one, and is not asserted to be (0,0). -/
theorem seamComplementInverse_mem_bifiltrationLevel
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x)
    (R : Type*) [CommRing R] {u v : ℝ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v) :
    seamComplementInverse G H x R c ∈
      laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R
        (u + seamComplementOCount G H x) v := by
  classical
  intro y k hk
  rw [seamComplementInverse_apply] at hk
  by_cases hy : y = x.val
  · subst y
    rw [Finsupp.single_eq_same] at hk
    have hk' := AddMonoidAlgebra.support_coeff_single_mul_subset
      (c (seamComplementPartner x).val) (1 : R) (-(seamComplementOCount G H x : ℤ)) hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk'
    have hb := hc (seamComplementPartner x).val j hj
    have hA : ((connectedSumSeamGrid G H hG hH).alexander x.val : ℝ) +
        (seamComplementOCount G H x : ℝ) =
        ((connectedSumSeamGrid G H hG hH).alexander (seamComplementPartner x).val : ℝ) := by
      exact_mod_cast connectedSumSeamGrid_complement_alexander G H hG hH x hx
    push_cast
    constructor <;> linarith [hb.1, hb.2]
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

/-- The reciprocal of the weighted arrow has Maslov degree one. -/
theorem seamComplementInverse_mem_maslovPiece
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : SeamComplement n m) (hx : SeamComplementSource x)
    (R : Type*) [CommRing R] {d : ℤ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d) :
    seamComplementInverse G H x R c ∈
      laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R (d + 1) := by
  classical
  rw [mem_laurentMaslovPiece] at hc ⊢
  intro y k hk
  rw [seamComplementInverse_apply] at hk
  by_cases hy : y = x.val
  · subst y
    rw [Finsupp.single_eq_same] at hk
    have hk' := AddMonoidAlgebra.support_coeff_single_mul_subset
      (c (seamComplementPartner x).val) (1 : R) (-(seamComplementOCount G H x : ℤ)) hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk'
    have hh := hc (seamComplementPartner x).val j hj
    have hM := connectedSumSeamGrid_complement_maslov G H hG hH x hx
    simp only [laurentMaslovDegree] at hh ⊢
    omega
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

end OnLeConjecture.KnotFloer.GridFull
