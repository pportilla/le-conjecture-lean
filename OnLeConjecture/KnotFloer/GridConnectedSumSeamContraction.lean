/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentXBlocking
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# The shared-corner seam grid

The two grids have sizes n+1 and m+1. Their final and initial X squares are
identified, giving a grid of size n+m+1. Extending and composing the O
permutations splices the two O arrows through the shared column. The size is
exactly the sum of the factor sizes minus one.

This module constructs the diagram and verifies rectangle identities needed
for cancellation at the seam. It does not yet construct a contraction or
identify the diagram with a connected sum of embedded knots.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween

variable {n m : ℕ}

/-- Embed the first block, including its final corner. -/
def seamLeft (n m : ℕ) (c : Fin (n + 1)) : Fin (n + m + 1) :=
  ⟨c.val, by omega⟩

/-- Embed the second block, including its initial corner. -/
def seamRight (n m : ℕ) (c : Fin (m + 1)) : Fin (n + m + 1) :=
  ⟨n + c.val, by omega⟩

@[simp] theorem seamLeft_val (c : Fin (n + 1)) : (seamLeft n m c).val = c.val := rfl
@[simp] theorem seamRight_val (c : Fin (m + 1)) : (seamRight n m c).val = n + c.val := rfl

theorem seamLeft_injective : Function.Injective (seamLeft n m) := by
  intro c d h
  exact Fin.ext (congrArg (fun x : Fin (n + m + 1) => x.val) h)

theorem seamRight_injective : Function.Injective (seamRight n m) := by
  intro c d h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [seamRight_val] at this
  omega

@[simp] theorem seamLeft_last : seamLeft n m (Fin.last n) = seamRight n m 0 := by
  apply Fin.ext
  simp

/-- A first-block point equals a second-block point only at the common corner. -/
theorem seamLeft_eq_seamRight_iff (c : Fin (n + 1)) (d : Fin (m + 1)) :
    seamLeft n m c = seamRight n m d ↔ c = Fin.last n ∧ d = 0 := by
  constructor
  · intro h
    have := congrArg Fin.val h
    simp only [seamLeft_val, seamRight_val] at this
    constructor <;> apply Fin.ext <;> simp only [Fin.val_last, Fin.val_zero] <;> omega
  · rintro ⟨rfl, rfl⟩
    exact seamLeft_last

/-- The two blocks cover every column. -/
theorem seam_cases (c : Fin (n + m + 1)) :
    (∃ a, c = seamLeft n m a) ∨ ∃ b, c = seamRight n m b := by
  by_cases hc : c.val ≤ n
  · exact Or.inl ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨c.val - n, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [seamRight_val]
    omega

def seamLeftIndexEquiv (n m : ℕ) : Fin (n + 1) ⊕ Fin m ≃ Fin (n + m + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def seamRightIndexEquiv (n m : ℕ) : Fin n ⊕ Fin (m + 1) ≃ Fin (n + m + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Extend a first-block permutation by the identity outside that block. -/
def seamExtendLeft (x : GridState (n + 1)) : GridState (n + m + 1) :=
  ⟨(seamLeftIndexEquiv n m).symm.trans
    ((Equiv.sumCongr x.toPerm (Equiv.refl (Fin m))).trans (seamLeftIndexEquiv n m))⟩

/-- Extend a second-block permutation by the identity outside that block. -/
def seamExtendRight (x : GridState (m + 1)) : GridState (n + m + 1) :=
  ⟨(seamRightIndexEquiv n m).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin n)) x.toPerm).trans (seamRightIndexEquiv n m))⟩

theorem seamLeftIndexEquiv_inl (c : Fin (n + 1)) :
    seamLeftIndexEquiv n m (Sum.inl c) = seamLeft n m c := by
  apply Fin.ext
  simp [seamLeftIndexEquiv, seamLeft]

theorem seamLeftIndexEquiv_inr (c : Fin m) :
    seamLeftIndexEquiv n m (Sum.inr c) = seamRight n m c.succ := by
  apply Fin.ext
  simp [seamLeftIndexEquiv, seamRight]
  omega

theorem seamRightIndexEquiv_inl (c : Fin n) :
    seamRightIndexEquiv n m (Sum.inl c) = seamLeft n m c.castSucc := by
  apply Fin.ext
  simp [seamRightIndexEquiv, seamLeft]

theorem seamRightIndexEquiv_inr (c : Fin (m + 1)) :
    seamRightIndexEquiv n m (Sum.inr c) = seamRight n m c := by
  apply Fin.ext
  simp [seamRightIndexEquiv, seamRight]

@[simp] theorem seamExtendLeft_left (x : GridState (n + 1)) (c : Fin (n + 1)) :
    seamExtendLeft (m := m) x (seamLeft n m c) = seamLeft n m (x c) := by
  rw [← seamLeftIndexEquiv_inl, seamExtendLeft]
  change (seamLeftIndexEquiv n m)
    (Equiv.sumCongr x.toPerm (Equiv.refl (Fin m))
      ((seamLeftIndexEquiv n m).symm ((seamLeftIndexEquiv n m) (Sum.inl c)))) = _
  simp only [Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inl]
  exact seamLeftIndexEquiv_inl _

@[simp] theorem seamExtendLeft_right_succ (x : GridState (n + 1)) (c : Fin m) :
    seamExtendLeft x (seamRight n m c.succ) = seamRight n m c.succ := by
  rw [← seamLeftIndexEquiv_inr, seamExtendLeft]
  simp

@[simp] theorem seamExtendRight_right (x : GridState (m + 1)) (c : Fin (m + 1)) :
    seamExtendRight (n := n) x (seamRight n m c) = seamRight n m (x c) := by
  rw [← seamRightIndexEquiv_inr, seamExtendRight]
  change (seamRightIndexEquiv n m)
    (Equiv.sumCongr (Equiv.refl (Fin n)) x.toPerm
      ((seamRightIndexEquiv n m).symm ((seamRightIndexEquiv n m) (Sum.inr c)))) = _
  simp only [Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inr]
  exact seamRightIndexEquiv_inr _

@[simp] theorem seamExtendRight_left_castSucc (x : GridState (m + 1)) (c : Fin n) :
    seamExtendRight x (seamLeft n m c.castSucc) = seamLeft n m c.castSucc := by
  rw [← seamRightIndexEquiv_inl, seamExtendRight]
  simp

/-- Compose the two extended permutations through the common corner. -/
def seamState (x : GridState (n + 1)) (y : GridState (m + 1)) : GridState (n + m + 1) :=
  ⟨(seamExtendRight (n := n) y).toPerm.trans (seamExtendLeft (m := m) x).toPerm⟩

@[simp] theorem seamState_left_castSucc (x : GridState (n + 1))
    (y : GridState (m + 1)) (c : Fin n) :
    seamState x y (seamLeft n m c.castSucc) = seamLeft n m (x c.castSucc) := by
  change seamExtendLeft x (seamExtendRight y _) = _
  simp

@[simp] theorem seamState_right_of_ne_zero (x : GridState (n + 1))
    (y : GridState (m + 1)) (c : Fin (m + 1)) (hc : y c ≠ 0) :
    seamState x y (seamRight n m c) = seamRight n m (y c) := by
  change seamExtendLeft x (seamExtendRight y _) = _
  rw [seamExtendRight_right]
  obtain ⟨d, hd⟩ := Fin.exists_succ_eq_of_ne_zero hc
  rw [← hd, seamExtendLeft_right_succ]

@[simp] theorem seamState_right_of_zero (x : GridState (n + 1))
    (y : GridState (m + 1)) (c : Fin (m + 1)) (hc : y c = 0) :
    seamState x y (seamRight n m c) = seamLeft n m (x (Fin.last n)) := by
  change seamExtendLeft x (seamExtendRight y _) = _
  rw [seamExtendRight_right, hc, ← seamLeft_last, seamExtendLeft_left]

/-- Glue the final and initial X corners, and splice the O permutations. -/
def connectedSumSeamGrid (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) :
    GridDiagram (n + m + 1) where
  O := seamState G.O H.O
  X := seamState G.X H.X
  disjoint c := by
    rcases seam_cases c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · induction a using Fin.lastCases with
      | last =>
        rw [seamLeft_last, seamState_right_of_zero _ _ _ hH, hG, seamLeft_last]
        have hO : H.O 0 ≠ 0 := by simpa only [hH] using H.disjoint 0
        rw [seamState_right_of_ne_zero _ _ _ hO]
        exact fun h => hO (seamRight_injective h)
      | cast a =>
        rw [seamState_left_castSucc, seamState_left_castSucc]
        exact fun h => G.disjoint _ (seamLeft_injective h)
    · by_cases hb : b = 0
      · subst b
        rw [seamState_right_of_zero _ _ _ hH, hG, seamLeft_last]
        have hO : H.O 0 ≠ 0 := by simpa only [hH] using H.disjoint 0
        rw [seamState_right_of_ne_zero _ _ _ hO]
        exact fun h => hO (seamRight_injective h)
      · have hX : H.X b ≠ 0 := fun h => hb (H.X.toPerm.injective (h.trans hH.symm))
        rw [seamState_right_of_ne_zero _ _ _ hX]
        by_cases hO : H.O b = 0
        · rw [seamState_right_of_zero _ _ _ hO]
          intro he
          exact hX (seamLeft_eq_seamRight_iff _ _ |>.mp he).2
        · rw [seamState_right_of_ne_zero _ _ _ hO]
          exact fun h => H.disjoint _ (seamRight_injective h)

/-- If the second state fixes its corner, every first-block value is retained. -/
theorem seamState_left (x : GridState (n + 1)) (y : GridState (m + 1))
    (hy : y 0 = 0) (c : Fin (n + 1)) :
    seamState x y (seamLeft n m c) = seamLeft n m (x c) := by
  induction c using Fin.lastCases with
  | last => rw [seamLeft_last, seamState_right_of_zero _ _ _ hy]
  | cast c => exact seamState_left_castSucc x y c

/-- Every column belongs either to the first block or strictly beyond it. -/
theorem seam_cases_succ (c : Fin (n + m + 1)) :
    (∃ a, c = seamLeft n m a) ∨ ∃ b : Fin m, c = seamRight n m b.succ := by
  rcases seam_cases c with h | ⟨b, rfl⟩
  · exact Or.inl h
  · by_cases hb : b = 0
    · subst b
      exact Or.inl ⟨Fin.last n, seamLeft_last.symm⟩
    · obtain ⟨d, hd⟩ := Fin.exists_succ_eq_of_ne_zero hb
      exact Or.inr ⟨d, congrArg (seamRight n m) hd.symm⟩

@[simp] theorem seamLeft_mem_cIoo_iff (a b c : Fin (n + 1)) :
    seamLeft n m c ∈ Grid.cIoo (seamLeft n m a) (seamLeft n m b) ↔ c ∈ Grid.cIoo a b := by
  simp only [Grid.mem_cIoo, seamLeft, ne_eq, Fin.ext_iff]

@[simp] theorem seamLeft_mem_cIco_iff (a b c : Fin (n + 1)) :
    seamLeft n m c ∈ Grid.cIco (seamLeft n m a) (seamLeft n m b) ↔ c ∈ Grid.cIco a b := by
  simp only [Grid.mem_cIco, seamLeft, ne_eq, Fin.ext_iff]

/-- A nonwrapping interval in the first block misses every column beyond it. -/
theorem seamRight_succ_not_mem_left_cIoo (a b : Fin (n + 1))
    (hab : a.val < b.val) (c : Fin m) :
    seamRight n m c.succ ∉ Grid.cIoo (seamLeft n m a) (seamLeft n m b) := by
  simp only [Grid.mem_cIoo, seamLeft, seamRight, Fin.val_succ, if_pos hab]
  omega

/-- A nonwrapping half-open interval in the first block misses every later column. -/
theorem seamRight_succ_not_mem_left_cIco (a b : Fin (n + 1))
    (hab : a.val < b.val) (c : Fin m) :
    seamRight n m c.succ ∉ Grid.cIco (seamLeft n m a) (seamLeft n m b) := by
  simp only [Grid.mem_cIco, seamLeft, seamRight, Fin.val_succ, if_pos hab]
  omega

/-- Embed a first-factor rectangle, holding a corner-fixing second-factor state fixed. -/
def seamLeftRectangle {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0) :
    GridRectangleBetween (seamState x z) (seamState y z) where
  left := seamLeft n m r.left
  right := seamLeft n m r.right
  left_ne_right := fun h => r.left_ne_right (seamLeft_injective h)
  map_left := by rw [seamState_left _ _ hz, seamState_left _ _ hz, r.map_left]
  map_right := by rw [seamState_left _ _ hz, seamState_left _ _ hz, r.map_right]
  map_of_ne c hl hr := by
    rcases seam_cases_succ c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [seamState_left _ _ hz, seamState_left _ _ hz,
        r.map_of_ne a (fun h => hl (congrArg (seamLeft n m) h))
          (fun h => hr (congrArg (seamLeft n m) h))]
    · have hb : z b.succ ≠ 0 := fun h =>
        Fin.succ_ne_zero b (z.toPerm.injective (h.trans hz.symm))
      rw [seamState_right_of_ne_zero _ _ _ hb, seamState_right_of_ne_zero _ _ _ hb]

@[simp] theorem seamLeftRectangle_left {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0) :
    (seamLeftRectangle r z hz).left = seamLeft n m r.left := rfl

@[simp] theorem seamLeftRectangle_right {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0) :
    (seamLeftRectangle r z hz).right = seamLeft n m r.right := rfl

@[simp] theorem seamLeftRectangle_bottom {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0) :
    (seamLeftRectangle r z hz).bottom = seamLeft n m r.bottom := by
  simp only [bottom_def, seamLeftRectangle_left, seamState_left _ _ hz]

@[simp] theorem seamLeftRectangle_top {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0) :
    (seamLeftRectangle r z hz).top = seamLeft n m r.top := by
  simp only [top_def, seamLeftRectangle_right, seamState_left _ _ hz]

/-- For a nonwrapping first-factor rectangle, emptiness is preserved in both directions. -/
theorem seamLeftRectangle_isEmpty_iff {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0)
    (hr : r.left.val < r.right.val) : (seamLeftRectangle r z hz).IsEmpty ↔ r.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo, isEmpty_iff_forall_notMem_cIoo]
  constructor
  · intro h c hc
    have hh := h (seamLeft n m c) (by simpa only [seamLeftRectangle_left,
      seamLeftRectangle_right, seamLeft_mem_cIoo_iff] using hc)
    simpa only [seamLeftRectangle_bottom, seamLeftRectangle_top,
      seamState_left _ _ hz, seamLeft_mem_cIoo_iff] using hh
  · intro h c hc
    rcases seam_cases_succ c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have ha : a ∈ Grid.cIoo r.left r.right := by
        simpa only [seamLeftRectangle_left, seamLeftRectangle_right,
          seamLeft_mem_cIoo_iff] using hc
      simpa only [seamLeftRectangle_bottom, seamLeftRectangle_top,
        seamState_left _ _ hz, seamLeft_mem_cIoo_iff] using h a ha
    · exact (seamRight_succ_not_mem_left_cIoo r.left r.right hr b hc).elim

/-- Markings in a nonwrapping first-factor rectangle are exactly its original markings,
provided the first-block marking values agree away from the common corner. -/
theorem seamLeftRectangle_OColumns_of_marking
    (G : GridDiagram (n + 1)) (K : GridDiagram (n + m + 1))
    (hK : ∀ c : Fin n, K.O (seamLeft n m c.castSucc) = seamLeft n m (G.O c.castSucc))
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0) (hr : r.left.val < r.right.val) :
    K.OColumns (seamLeftRectangle r z hz).toGridRectangle =
      (G.OColumns r.toGridRectangle).image (seamLeft n m) := by
  classical
  have hmem (a : Fin (n + 1)) :
      seamLeft n m a ∈ K.OColumns (seamLeftRectangle r z hz).toGridRectangle ↔
        a ∈ G.OColumns r.toGridRectangle := by
    rw [GridDiagram.mem_OColumns, GridDiagram.mem_OColumns,
      mem_toGridRectangle_coveredSquares, mem_toGridRectangle_coveredSquares]
    simp only [seamLeftRectangle_left, seamLeftRectangle_right,
      seamState_left _ _ hz, seamLeft_mem_cIco_iff]
    by_cases ha : a ∈ Grid.cIco r.left r.right
    · have hlt := (Grid.mem_cIco_iff_of_left_lt_right hr a).mp ha
      have halast : a ≠ Fin.last n := by
        intro hh
        have hav := congrArg Fin.val hh
        simp only [Fin.val_last] at hav
        have := r.right.isLt
        omega
      obtain ⟨b, rfl⟩ := Fin.eq_castSucc_of_ne_last halast
      rw [hK, seamLeft_mem_cIco_iff]
    · simp only [ha, false_and]
  ext c
  rcases seam_cases_succ c with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [hmem, Finset.mem_image]
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨d, hd, hda⟩
      exact seamLeft_injective hda ▸ hd
  · have hnot : seamRight n m b.succ ∉ K.OColumns
        (seamLeftRectangle r z hz).toGridRectangle := by
      rw [GridDiagram.mem_OColumns, mem_toGridRectangle_coveredSquares]
      exact fun h => seamRight_succ_not_mem_left_cIco r.left r.right hr b h.1
    rw [iff_false_intro hnot]
    symm
    rw [iff_false]
    intro him
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp him
    have := (seamLeft_eq_seamRight_iff a b.succ).mp ha
    exact Fin.succ_ne_zero b this.2

/-- The full O weight of every nonwrapping first-factor rectangle is unchanged. -/
theorem connectedSumSeamGrid_OColumns_left
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0) (hr : r.left.val < r.right.val) :
    (connectedSumSeamGrid G H hG hH).OColumns (seamLeftRectangle r z hz).toGridRectangle =
      (G.OColumns r.toGridRectangle).image (seamLeft n m) := by
  apply seamLeftRectangle_OColumns_of_marking G _ _ r z hz hr
  intro c
  exact seamState_left_castSucc G.O H.O c

/-- The X markings of every nonwrapping first-factor rectangle are unchanged as well. -/
theorem connectedSumSeamGrid_XColumns_left
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0) (hr : r.left.val < r.right.val) :
    (connectedSumSeamGrid G H hG hH).swapMarkings.OColumns
        (seamLeftRectangle r z hz).toGridRectangle =
      (G.swapMarkings.OColumns r.toGridRectangle).image (seamLeft n m) := by
  apply seamLeftRectangle_OColumns_of_marking G.swapMarkings _ _ r z hz hr
  intro c
  exact seamState_left_castSucc G.X H.X c

/-- Equality of individual Laurent coefficients carried by the embedded rectangles. -/
theorem connectedSumSeamGrid_rectangle_weight_left
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0) (hr : r.left.val < r.right.val)
    (R : Type*) [CommSemiring R] :
    (LaurentPolynomial.T (((connectedSumSeamGrid G H hG hH).OColumns
      (seamLeftRectangle r z hz).toGridRectangle).card : ℤ) : LaurentPolynomial R) =
      LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  rw [connectedSumSeamGrid_OColumns_left G H hG hH r z hz hr,
    Finset.card_image_of_injective _ seamLeft_injective]

/-- An embedded rectangle wrapping around both factor cuts contains an outside state point. -/
theorem seamLeftRectangle_not_isEmpty_of_two_wraps {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0)
    (hm : 0 < m) (hc : r.right.val < r.left.val) (hv : r.top.val < r.bottom.val) :
    ¬ (seamLeftRectangle r z hz).IsEmpty := by
  let b : Fin m := ⟨0, hm⟩
  have hb : z b.succ ≠ 0 := fun h =>
    Fin.succ_ne_zero b (z.toPerm.injective (h.trans hz.symm))
  obtain ⟨d, hd⟩ := Fin.exists_succ_eq_of_ne_zero hb
  have hcol : seamRight n m b.succ ∈
      Grid.cIoo (seamLeft n m r.left) (seamLeft n m r.right) := by
    rw [Grid.mem_cIoo]
    refine ⟨fun h => r.left_ne_right (seamLeft_injective h), ?_⟩
    change (if r.left.val < r.right.val then _ else _)
    rw [if_neg (by omega)]
    left
    change r.left.val < n + (b.val + 1)
    have := r.left.isLt
    omega
  have hrow : seamRight n m d.succ ∈
      Grid.cIoo (seamLeft n m r.bottom) (seamLeft n m r.top) := by
    rw [Grid.mem_cIoo]
    refine ⟨fun h => r.bottom_ne_top (seamLeft_injective h), ?_⟩
    change (if r.bottom.val < r.top.val then _ else _)
    rw [if_neg (by omega)]
    left
    change r.bottom.val < n + (d.val + 1)
    have := r.bottom.isLt
    omega
  intro he
  have h := ((isEmpty_iff_forall_notMem_cIoo (seamLeftRectangle r z hz)).mp he)
    (seamRight n m b.succ) hcol
  rw [seamLeftRectangle_bottom, seamLeftRectangle_top,
    seamState_right_of_ne_zero _ _ _ hb, ← hd] at h
  exact h hrow

/-- Emptiness in the seam grid always implies emptiness of the factor rectangle. -/
theorem seamLeftRectangle_factor_isEmpty {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0)
    (he : (seamLeftRectangle r z hz).IsEmpty) : r.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo] at he ⊢
  intro c hc
  have h := he (seamLeft n m c) (by simpa only [seamLeftRectangle_left,
    seamLeftRectangle_right, seamLeft_mem_cIoo_iff] using hc)
  simpa only [seamLeftRectangle_bottom, seamLeftRectangle_top,
    seamState_left _ _ hz, seamLeft_mem_cIoo_iff] using h

/-- If the row interval does not wrap, outside points cannot enter the rectangle. -/
theorem seamLeftRectangle_isEmpty_of_row_nonwrap {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0)
    (hv : r.bottom.val < r.top.val) (he : r.IsEmpty) :
    (seamLeftRectangle r z hz).IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo] at he ⊢
  intro c hc
  rcases seam_cases_succ c with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have ha : a ∈ Grid.cIoo r.left r.right := by
      simpa only [seamLeftRectangle_left, seamLeftRectangle_right,
        seamLeft_mem_cIoo_iff] using hc
    simpa only [seamLeftRectangle_bottom, seamLeftRectangle_top,
      seamState_left _ _ hz, seamLeft_mem_cIoo_iff] using he a ha
  · have hb : z b.succ ≠ 0 := fun h =>
      Fin.succ_ne_zero b (z.toPerm.injective (h.trans hz.symm))
    obtain ⟨d, hd⟩ := Fin.exists_succ_eq_of_ne_zero hb
    rw [seamLeftRectangle_bottom, seamLeftRectangle_top,
      seamState_right_of_ne_zero _ _ _ hb, ← hd]
    exact seamRight_succ_not_mem_left_cIoo r.bottom r.top hv d

/-- Complete emptiness criterion: exactly the two-wrap rectangles acquire outside points. -/
theorem seamLeftRectangle_isEmpty_iff_nonwrap {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1)) (hz : z 0 = 0)
    (hm : 0 < m) :
    (seamLeftRectangle r z hz).IsEmpty ↔
      r.IsEmpty ∧ (r.left.val < r.right.val ∨ r.bottom.val < r.top.val) := by
  constructor
  · intro he
    refine ⟨seamLeftRectangle_factor_isEmpty r z hz he, ?_⟩
    by_contra h
    have hcolne : r.left.val ≠ r.right.val := fun h => r.left_ne_right (Fin.ext h)
    have hrowne : r.bottom.val ≠ r.top.val := fun h => r.bottom_ne_top (Fin.ext h)
    have hc : r.right.val < r.left.val := by omega
    have hv : r.top.val < r.bottom.val := by omega
    exact seamLeftRectangle_not_isEmpty_of_two_wraps r z hz hm hc hv he
  · rintro ⟨he, hc | hv⟩
    · exact (seamLeftRectangle_isEmpty_iff r z hz hc).mpr he
    · exact seamLeftRectangle_isEmpty_of_row_nonwrap r z hz hv he

/-- In the two-wrap case the old rectangle crosses the factor's final corner square. -/
theorem last_corner_mem_of_two_wraps {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y)
    (hc : r.right.val < r.left.val) (hv : r.top.val < r.bottom.val) :
    (Fin.last n, Fin.last n) ∈ r.toGridRectangle.coveredSquares := by
  rw [mem_toGridRectangle_coveredSquares]
  constructor
  · rw [Grid.mem_cIco_iff_of_right_lt_left hc]
    exact Or.inl (Nat.le_of_lt_succ r.left.isLt)
  · change Fin.last n ∈ Grid.cIco r.bottom r.top
    rw [Grid.mem_cIco_iff_of_right_lt_left hv]
    exact Or.inl (Nat.le_of_lt_succ r.bottom.isLt)

/-- The shared corner is still an X marking of the seam grid. -/
theorem connectedSumSeamGrid_X_corner
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) :
    (connectedSumSeamGrid G H hG hH).X (seamLeft n m (Fin.last n)) =
      seamLeft n m (Fin.last n) := by
  change seamState G.X H.X _ = _
  rw [seamState_left _ _ hH, hG]

/-- Blocking the shared X removes every two-wrap embedded rectangle. -/
theorem connectedSumSeamGrid_two_wraps_blocked_weight
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (z : GridState (m + 1)) (hz : z 0 = 0)
    (hc : r.right.val < r.left.val) (hv : r.top.val < r.bottom.val)
    (R : Type*) [CommSemiring R] :
    squareWeight (xBlockedSquareWeight (connectedSumSeamGrid G H hG hH) R
      {seamLeft n m (Fin.last n)}) (seamLeftRectangle r z hz).toGridRectangle = 0 := by
  classical
  rw [squareWeight_xBlockedSquareWeight, if_pos]
  refine ⟨seamLeft n m (Fin.last n), Finset.mem_singleton_self _, ?_⟩
  rw [connectedSumSeamGrid_X_corner, mem_toGridRectangle_coveredSquares]
  simp only [seamLeftRectangle_left, seamLeftRectangle_right, seamState_left _ _ hz,
    seamLeft_mem_cIco_iff]
  exact (mem_toGridRectangle_coveredSquares r).mp (last_corner_mem_of_two_wraps r hc hv)

end OnLeConjecture.KnotFloer.GridFull
