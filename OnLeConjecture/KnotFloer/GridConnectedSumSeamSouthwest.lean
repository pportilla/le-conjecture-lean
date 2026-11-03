/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSector

/-!
# Full-differential unit edges in the complement of the seam pair image

If the shared column and its immediate successor contain two increasing
rows at most n, the intervening width-one rectangle has no O or X marking.
Both endpoint states lie outside the image of all factor pairs. The other
rectangle between them contains a state point, so the actual full
coefficient is one. The reverse rank-one operator preserves both
filtrations. No global matching or contraction is asserted.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween

variable {n m : ℕ}

/-- A second-block column has a first-block row exactly at the preimage of zero in z. -/
theorem seamState_right_row_le_iff (x : GridState (n + 1)) (z : GridState (m + 1))
    (c : Fin (m + 1)) :
    (seamState x z (seamRight n m c)).val ≤ n ↔ z c = 0 := by
  by_cases hc : z c = 0
  · rw [seamState_right_of_zero _ _ _ hc, seamLeft_val]
    exact iff_of_true (Nat.le_of_lt_succ (x (Fin.last n)).isLt) hc
  · rw [seamState_right_of_ne_zero _ _ _ hc, seamRight_val]
    have hv : 0 < (z c).val := by
      have hne : (z c).val ≠ 0 := fun h => hc (Fin.ext h)
      omega
    exact iff_of_false (by omega) hc

/-- Two distinct second-block columns in first-block rows force a state into the complement. -/
theorem not_pairSector_of_two_right_rows (w : GridState (n + m + 1))
    (a b : Fin (m + 1)) (hab : a ≠ b)
    (ha : (w (seamRight n m a)).val ≤ n) (hb : (w (seamRight n m b)).val ≤ n) :
    ¬ SeamPairSector (n := n) (m := m) w := by
  intro hw
  obtain ⟨x, z, rfl⟩ := (seamPairSector_iff_exists w).mp hw
  have hza := (seamState_right_row_le_iff x z a).mp ha
  have hzb := (seamState_right_row_le_iff x z b).mp hb
  exact hab (z.toPerm.injective (hza.trans hzb.symm))

/-- Exchange the two adjacent columns on the southwest side of the seam. -/
def seamSouthwestTarget (w : GridState (n + m + 1)) (hm : 0 < m) : GridState (n + m + 1) :=
  w.swapColumns (seamLeft n m (Fin.last n)) (seamRight n m (seamNextIndex m hm))

/-- The orientation with initial side at the shared column. -/
def seamSouthwestRectangle (w : GridState (n + m + 1)) (hm : 0 < m) :
    GridRectangleBetween w (seamSouthwestTarget w hm) :=
  ofSwapColumns _ _ (seamLeft n m (Fin.last n)) (seamRight n m (seamNextIndex m hm))
    (seamCorner_ne_next hm) rfl

@[simp] theorem seamSouthwestRectangle_left (w : GridState (n + m + 1)) (hm : 0 < m) :
    (seamSouthwestRectangle w hm).left = seamLeft n m (Fin.last n) := by
  unfold seamSouthwestRectangle
  exact ofSwapColumns_left _ _ _ _ _ _

@[simp] theorem seamSouthwestRectangle_right (w : GridState (n + m + 1)) (hm : 0 < m) :
    (seamSouthwestRectangle w hm).right = seamRight n m (seamNextIndex m hm) := by
  unfold seamSouthwestRectangle
  exact ofSwapColumns_right _ _ _ _ _ _

@[simp] theorem seamSouthwestRectangle_bottom (w : GridState (n + m + 1)) (hm : 0 < m) :
    (seamSouthwestRectangle w hm).bottom = w (seamLeft n m (Fin.last n)) := by
  rw [bottom_def, seamSouthwestRectangle_left]

@[simp] theorem seamSouthwestRectangle_top (w : GridState (n + m + 1)) (hm : 0 < m) :
    (seamSouthwestRectangle w hm).top = w (seamRight n m (seamNextIndex m hm)) := by
  rw [top_def, seamSouthwestRectangle_right]

/-- Swapping these columns leaves every first n column unchanged, preserving complement status. -/
theorem seamSouthwestTarget_pairSector_iff (w : GridState (n + m + 1)) (hm : 0 < m) :
    SeamPairSector (n := n) (m := m) (seamSouthwestTarget w hm) ↔ SeamPairSector w := by
  have he (c : Fin n) : seamSouthwestTarget w hm (seamLeft n m c.castSucc) =
      w (seamLeft n m c.castSucc) := by
    have ha : seamLeft n m c.castSucc ≠ seamLeft n m (Fin.last n) :=
      fun h => Fin.castSucc_ne_last c (seamLeft_injective h)
    have hb : seamLeft n m c.castSucc ≠ seamRight n m (seamNextIndex m hm) :=
      fun h => Fin.castSucc_ne_last c ((seamLeft_eq_seamRight_iff _ _).mp h).1
    rw [seamSouthwestTarget, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne ha hb]
  simp only [SeamPairSector, he]

/-- Both states of an increasing southwest rectangle lie in the classified complement. -/
theorem seamSouthwest_states_not_pairSector (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n) :
    ¬ SeamPairSector (n := n) (m := m) w ∧
      ¬ SeamPairSector (n := n) (m := m) (seamSouthwestTarget w hm) := by
  have hleft : (w (seamRight n m 0)).val ≤ n := by
    rw [← seamLeft_last]
    omega
  have hw := not_pairSector_of_two_right_rows w 0 (seamNextIndex m hm)
    (seamNextIndex_ne_zero hm).symm hleft htop
  exact ⟨hw, fun h => hw ((seamSouthwestTarget_pairSector_iff w hm).mp h)⟩

theorem seamSouthwestRectangle_isEmpty (w : GridState (n + m + 1)) (hm : 0 < m) :
    (seamSouthwestRectangle w hm).IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo]
  intro c hc
  rw [seamSouthwestRectangle_left, seamSouthwestRectangle_right, Grid.mem_cIoo] at hc
  change _ ∧ (if n < n + 1 then n < c.val ∧ c.val < n + 1
    else n < c.val ∨ c.val < n + 1) at hc
  rw [if_pos (by omega)] at hc
  omega

/-- The opposite rectangle contains the state point on the global final row. -/
theorem seamSouthwestRectangle_swap_not_isEmpty (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n) :
    ¬ (seamSouthwestRectangle w hm).swapSides.IsEmpty := by
  let c := w.toPerm.symm (Fin.last (n + m))
  have hc : w c = Fin.last (n + m) := w.toPerm.apply_symm_apply _
  have hca : c ≠ seamLeft n m (Fin.last n) := by
    intro h
    have hh := congrArg Fin.val (h ▸ hc)
    simp only [Fin.val_last] at hh
    omega
  have hcb : c ≠ seamRight n m (seamNextIndex m hm) := by
    intro h
    have hh := congrArg Fin.val (h ▸ hc)
    simp only [Fin.val_last] at hh
    omega
  have hcol : c ∈ Grid.cIoo (seamSouthwestRectangle w hm).swapSides.left
      (seamSouthwestRectangle w hm).swapSides.right := by
    rw [swapSides_left, swapSides_right, seamSouthwestRectangle_right,
      seamSouthwestRectangle_left, Grid.mem_cIoo]
    refine ⟨(seamCorner_ne_next hm).symm, ?_⟩
    have hcan : c.val ≠ n := fun h => hca (Fin.ext h)
    have hcbn : c.val ≠ n + 1 := fun h => hcb (Fin.ext h)
    change if n + 1 < n then n + 1 < c.val ∧ c.val < n else n + 1 < c.val ∨ c.val < n
    rw [if_neg (by omega)]
    omega
  have hrow : Fin.last (n + m) ∈ Grid.cIoo (seamSouthwestRectangle w hm).swapSides.bottom
      (seamSouthwestRectangle w hm).swapSides.top := by
    rw [swapSides_bottom, swapSides_top, seamSouthwestRectangle_top,
      seamSouthwestRectangle_bottom, Grid.mem_cIoo]
    refine ⟨fun h => (ne_of_gt hrows) (congrArg Fin.val h), ?_⟩
    rw [if_neg (by omega)]
    left
    change (w (seamRight n m (seamNextIndex m hm))).val < n + m
    omega
  intro he
  have hh := ((isEmpty_iff_forall_notMem_cIoo _).mp he) c hcol
  rw [hc] at hh
  exact hh hrow

/-- The southwest rectangle is the only empty rectangle for these endpoints. -/
theorem seamSouthwestRectangle_emptyRectangles (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n) :
    emptyRectangles w (seamSouthwestTarget w hm) = {seamSouthwestRectangle w hm} := by
  classical
  ext r
  rcases (seamSouthwestRectangle w hm).eq_or_eq_swapSides r with rfl | rfl <;>
    simp [seamSouthwestRectangle_isEmpty, seamSouthwestRectangle_swap_not_isEmpty w hm hrows htop,
      swapSides_ne_self]

/-- The only covered column is the shared column. -/
theorem seamSouthwestRectangle_column_mem_iff (w : GridState (n + m + 1)) (hm : 0 < m)
    (c : Fin (n + m + 1)) :
    c ∈ Grid.cIco (seamSouthwestRectangle w hm).left (seamSouthwestRectangle w hm).right ↔
      c = seamLeft n m (Fin.last n) := by
  rw [seamSouthwestRectangle_left, seamSouthwestRectangle_right,
    Grid.mem_cIco_iff_of_left_lt_right (by change n < n + 1; omega)]
  change n ≤ c.val ∧ c.val < n + 1 ↔ c = seamLeft n m (Fin.last n)
  constructor
  · intro h
    apply Fin.ext
    change c.val = n
    omega
  · rintro rfl
    change n ≤ n ∧ n < n + 1
    omega

/-- Any marking at or above row n misses the increasing southwest rectangle. -/
theorem seamSouthwestRectangle_OColumns_of_row_ge
    (K : GridDiagram (n + m + 1)) (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n)
    (hmark : n ≤ (K.O (seamLeft n m (Fin.last n))).val) :
    K.OColumns (seamSouthwestRectangle w hm).toGridRectangle = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hh := (mem_toGridRectangle_coveredSquares _).mp ((GridDiagram.mem_OColumns K).mp hc)
  have he := (seamSouthwestRectangle_column_mem_iff w hm c).mp hh.1
  subst c
  have hr := hh.2
  rw [seamSouthwestRectangle_left, seamSouthwestRectangle_right] at hr
  change K.O (seamLeft n m (Fin.last n)) ∈ Grid.cIco
    (w (seamLeft n m (Fin.last n))) (w (seamRight n m (seamNextIndex m hm))) at hr
  rw [Grid.mem_cIco_iff_of_left_lt_right hrows] at hr
  omega

/-- The actual seam O marking lies above the southwest rectangle. -/
theorem connectedSumSeamGrid_southwest_OColumns
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n) :
    (connectedSumSeamGrid G H hG hH).OColumns
      (seamSouthwestRectangle w hm).toGridRectangle = ∅ := by
  apply seamSouthwestRectangle_OColumns_of_row_ge _ w hm hrows htop
  have hO : H.O 0 ≠ 0 := by simpa only [hH] using H.disjoint 0
  change n ≤ (seamState G.O H.O (seamLeft n m (Fin.last n))).val
  rw [seamLeft_last, seamState_right_of_ne_zero _ _ _ hO, seamRight_val]
  omega

/-- The actual seam X marking is on row n, outside the half-open rectangle. -/
theorem connectedSumSeamGrid_southwest_XColumns
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n) :
    (connectedSumSeamGrid G H hG hH).swapMarkings.OColumns
      (seamSouthwestRectangle w hm).toGridRectangle = ∅ := by
  apply seamSouthwestRectangle_OColumns_of_row_ge _ w hm hrows htop
  change n ≤ ((connectedSumSeamGrid G H hG hH).X (seamLeft n m (Fin.last n))).val
  rw [connectedSumSeamGrid_X_corner, seamLeft_val, Fin.val_last]

/-- The full Laurent coefficient is exactly one, including all competing rectangles. -/
theorem connectedSumSeamGrid_southwest_coefficient
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n)
    (R : Type*) [CommSemiring R] :
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R w (seamSouthwestTarget w hm) = 1 := by
  rw [laurentCoefficient_eq, seamSouthwestRectangle_emptyRectangles w hm hrows htop,
    Finset.sum_singleton, connectedSumSeamGrid_southwest_OColumns G H hG hH w hm hrows htop]
  simp

/-- The two endpoint states have exactly the same Alexander grading. -/
theorem connectedSumSeamGrid_southwest_alexander
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n) :
    (connectedSumSeamGrid G H hG hH).alexander w =
      (connectedSumSeamGrid G H hG hH).alexander (seamSouthwestTarget w hm) := by
  let K := connectedSumSeamGrid G H hG hH
  let r := seamSouthwestRectangle w hm
  have hO := connectedSumSeamGrid_southwest_OColumns G H hG hH w hm hrows htop
  have hX := connectedSumSeamGrid_southwest_XColumns G H hG hH w hm hrows htop
  have hOc : (K.OSet ∩ r.toGridRectangle.coveredSquares).card = 0 := by
    rw [← K.card_OColumns, hO, Finset.card_empty]
  have hXc : (K.XSet ∩ r.toGridRectangle.coveredSquares).card = 0 := by
    change (K.swapMarkings.OSet ∩ r.toGridRectangle.coveredSquares).card = 0
    rw [← K.swapMarkings.card_OColumns, hX, Finset.card_empty]
  have he := K.alexander_sub_alexander_eq_card_sub_card r
  rw [hOc, hXc] at he
  exact sub_eq_zero.mp (by simpa using he)

/-- The source grading is one more than the target grading. -/
theorem connectedSumSeamGrid_southwest_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n) :
    (connectedSumSeamGrid G H hG hH).maslovOℤ w =
      (connectedSumSeamGrid G H hG hH).maslovOℤ (seamSouthwestTarget w hm) + 1 := by
  have he := laurentMaslovDegree_add_card_OColumns (connectedSumSeamGrid G H hG hH)
    (seamSouthwestRectangle w hm) (seamSouthwestRectangle_isEmpty w hm) 0
  rw [connectedSumSeamGrid_southwest_OColumns G H hG hH w hm hrows htop,
    Finset.card_empty] at he
  simp only [Nat.cast_zero, zero_add, laurentMaslovDegree_zero] at he
  omega

/-- The inverse of this coefficient-one arrow, zero on all other basis states. -/
def seamSouthwestInverse (w : GridState (n + m + 1)) (hm : 0 < m)
    (R : Type*) [CommSemiring R] :
    LaurentChain R (n + m + 1) →ₗ[LaurentPolynomial R] LaurentChain R (n + m + 1) :=
  Finsupp.lsingle w ∘ₗ Finsupp.lapply (seamSouthwestTarget w hm)

@[simp] theorem seamSouthwestInverse_apply (w : GridState (n + m + 1)) (hm : 0 < m)
    (R : Type*) [CommSemiring R] (c : LaurentChain R (n + m + 1)) :
    seamSouthwestInverse w hm R c = Finsupp.single w (c (seamSouthwestTarget w hm)) := rfl

/-- The actual inverse arrow has filtration shift (0,0). -/
theorem seamSouthwestInverse_mem_bifiltrationLevel
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n)
    (R : Type*) [CommRing R] {u v : ℝ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v) :
    seamSouthwestInverse w hm R c ∈
      laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v := by
  classical
  intro y k hk
  rw [seamSouthwestInverse_apply] at hk
  by_cases hy : y = w
  · subst y
    rw [Finsupp.single_eq_same] at hk
    have hh := hc (seamSouthwestTarget w hm) k hk
    rw [connectedSumSeamGrid_southwest_alexander G H hG hH w hm hrows htop]
    exact hh
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

/-- The inverse arrow raises Maslov degree by one. -/
theorem seamSouthwestInverse_mem_maslovPiece
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val)
    (htop : (w (seamRight n m (seamNextIndex m hm))).val ≤ n)
    (R : Type*) [CommRing R] {d : ℤ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d) :
    seamSouthwestInverse w hm R c ∈
      laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R (d + 1) := by
  classical
  rw [mem_laurentMaslovPiece] at hc ⊢
  intro y k hk
  rw [seamSouthwestInverse_apply] at hk
  by_cases hy : y = w
  · subst y
    rw [Finsupp.single_eq_same] at hk
    have hh := hc (seamSouthwestTarget w hm) k hk
    have hM := connectedSumSeamGrid_southwest_maslov G H hG hH w hm hrows htop
    simp only [laurentMaslovDegree] at hh ⊢
    omega
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

/-- The same exchange reverses the endpoint pairing. -/
theorem seamSouthwestTarget_involutive (hm : 0 < m) :
    Function.Involutive (fun w : GridState (n + m + 1) => seamSouthwestTarget w hm) := by
  intro w
  exact GridState.swapColumns_swapColumns _ _ _

/-- No two different source states in this family share their paired target. -/
theorem seamSouthwestTarget_injective (hm : 0 < m) :
    Function.Injective (fun w : GridState (n + m + 1) => seamSouthwestTarget w hm) :=
  (seamSouthwestTarget_involutive hm).injective

/-- The increasing orientation and its exchanged endpoint cannot both be sources. -/
theorem seamSouthwestTarget_not_increasing (w : GridState (n + m + 1)) (hm : 0 < m)
    (hrows : (w (seamLeft n m (Fin.last n))).val <
      (w (seamRight n m (seamNextIndex m hm))).val) :
    ¬ (seamSouthwestTarget w hm (seamLeft n m (Fin.last n))).val <
      (seamSouthwestTarget w hm (seamRight n m (seamNextIndex m hm))).val := by
  rw [seamSouthwestTarget, GridState.swapColumns_apply, GridState.swapColumns_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  omega

end OnLeConjecture.KnotFloer.GridFull
