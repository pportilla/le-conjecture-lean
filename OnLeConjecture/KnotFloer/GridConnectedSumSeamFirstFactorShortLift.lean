/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFactorLift
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnweightedPaths
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamInternalBirth

/-!
# Short corrections for obstructed first-factor rectangles

A last-column endpoint permits a pivot at an extreme column of the
second block. The entry and exit at this pivot have only first-block
points in their column interiors. The factor rectangle's emptiness
therefore controls both rectangles of the correction.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A retained state has exactly one southwest column, the second state's preimage of zero. -/
theorem seamState_southwest_singleton (x : GridState (n + 1)) (z : GridState (m + 1)) :
    seamSouthwestColumns (seamState x z) = {seamRight n m (z.toPerm.symm 0)} := by
  ext c
  rw [Finset.mem_singleton]
  constructor
  · intro hc
    obtain ⟨hcol, hrow⟩ := (mem_seamSouthwestColumns _ _).mp hc
    have hh := seamFirstFactorColumn_index_of_row_le x z c hrow
    rw [seamFirstFactorIndex, dif_neg (by omega), seamFirstFactorColumn_last] at hh
    exact hh.symm
  · rintro rfl
    apply (mem_seamSouthwestColumns _ _).mpr
    refine ⟨by simp only [seamRight_val]; omega, ?_⟩
    rw [seamState_right_of_zero x z _ (z.toPerm.apply_symm_apply 0), seamLeft_val]
    exact Nat.le_of_lt_succ (x (Fin.last n)).isLt

theorem seamShortLift_first_of_pair (v : SeamComplement n m) (P Q : Fin (n + m + 1))
    (hs : seamSouthwestColumns v.val = {P, Q}) (hPQ : P < Q) : seamComplementFirst v = P := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  rw [hs]
  refine ⟨by simp, ?_⟩
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact le_rfl
  · exact hPQ.le

theorem seamShortLift_second_of_pair (v : SeamComplement n m) (P Q : Fin (n + m + 1))
    (hs : seamSouthwestColumns v.val = {P, Q}) (hPQ : P < Q) : seamComplementSecond v = Q := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  rw [seamShortLift_first_of_pair v P Q hs hPQ, hs]
  refine ⟨Finset.mem_erase.mpr ⟨hPQ.ne.symm, by simp⟩, ?_⟩
  intro b hb
  obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hh | rfl
  · exact False.elim (hne hh)
  · exact le_rfl

def seamShortLift_matchingSourceOfPair (w : GridState (n + m + 1)) (P Q : Fin (n + m + 1))
    (hs : seamSouthwestColumns w = {P, Q}) (hPQ : P < Q)
    (hrows : (w P).val < (w Q).val) : SeamMatchingSource n m := by
  have hcomp : ¬ SeamPairSector w := not_pairSector_of_two_le_southwest_card w (by
    rw [hs, Finset.card_pair hPQ.ne])
  let v : SeamComplement n m := ⟨w, hcomp⟩
  refine ⟨v, ?_⟩
  change (w (seamComplementFirst v)).val < (w (seamComplementSecond v)).val
  rw [seamShortLift_first_of_pair v P Q hs hPQ, seamShortLift_second_of_pair v P Q hs hPQ]
  exact hrows

theorem seamShortLift_matchingSourceOfPair_partner (w : GridState (n + m + 1))
    (P Q : Fin (n + m + 1)) (hs : seamSouthwestColumns w = {P, Q}) (hPQ : P < Q)
    (hrows : (w P).val < (w Q).val) :
    (seamComplementPartner (seamShortLift_matchingSourceOfPair w P Q hs hPQ hrows).val).val =
      w.swapColumns P Q := by
  change w.swapColumns (seamComplementFirst _) (seamComplementSecond _) = _
  rw [seamShortLift_first_of_pair _ P Q hs hPQ, seamShortLift_second_of_pair _ P Q hs hPQ]

def seamShortLift_correctionOfPair (p q : SeamRetainedIndex n m)
    (w : GridState (n + m + 1)) (P Q : Fin (n + m + 1))
    (hs : seamSouthwestColumns w = {P, Q}) (hPQ : P < Q)
    (hrows : (w P).val < (w Q).val)
    (entry : GridRectangleBetween (seamState p.1 p.2) (w.swapColumns P Q))
    (he : entry.IsEmpty) (exit : GridRectangleBetween w (seamState q.1 q.2))
    (hx : exit.IsEmpty) : SeamCorrectionPath 0 p q := by
  let v := seamShortLift_matchingSourceOfPair w P Q hs hPQ hrows
  have hp : (seamComplementPartner v.val).val = w.swapColumns P Q :=
    seamShortLift_matchingSourceOfPair_partner w P Q hs hPQ hrows
  let e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner v.val).val := {
    left := entry.left
    right := entry.right
    left_ne_right := entry.left_ne_right
    map_left := by rw [hp]; exact entry.map_left
    map_right := by rw [hp]; exact entry.map_right
    map_of_ne := by intro c hl hr; rw [hp]; exact entry.map_of_ne c hl hr }
  have he' : e.IsEmpty := (isEmpty_iff_forall_notMem_cIoo e).mpr
    ((isEmpty_iff_forall_notMem_cIoo entry).mp he)
  exact ⟨v, v, ⟨e, he'⟩, ⟨(), rfl⟩, ⟨exit, hx⟩⟩

theorem seamShortLift_swap_triangle (w : GridState (n + m + 1))
    (A C D : Fin (n + m + 1)) (hDA : D ≠ A) (hDC : D ≠ C) :
    ((w.swapColumns A D).swapColumns A C).swapColumns C D = w.swapColumns A C := by
  rw [GridState.swapColumns_swapColumns_conj w A D A C]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hDA hDC,
    GridState.swapColumns_swapColumns]

/-- An obstructed last-right-endpoint rectangle has a nonzero second preimage of zero. -/
theorem seamFirstFactorRectangle_blocked_right_last {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hr : r.right = Fin.last n) : r.top.val < r.bottom.val ∧ 0 < (z.toPerm.symm 0).val := by
  obtain ⟨hwrap, d, hd, hc⟩ := (seamFirstFactorRectangle_not_isEmpty_iff r z he).mp hb
  have hl : r.left ≠ Fin.last n := fun hh => r.left_ne_right (hh.trans hr.symm)
  rw [hr, seamFirstFactorColumn_last, seamFirstFactorColumn, if_neg hl, Grid.mem_cIoo] at hc
  have hln : r.left.val < n := by
    have := r.left.isLt
    have hh : r.left.val ≠ n := fun h => hl (Fin.ext h)
    omega
  have hcol : (seamLeft n m r.left).val < (seamRight n m (z.toPerm.symm 0)).val := by
    simp only [seamLeft_val, seamRight_val]
    omega
  rw [if_pos hcol] at hc
  have hdd := hc.2.2
  simp only [seamRight_val] at hdd
  exact ⟨hwrap, by omega⟩

/-- An obstructed last-left-endpoint rectangle leaves a later second-block pivot. -/
theorem seamFirstFactorRectangle_blocked_left_last {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left = Fin.last n) : r.top.val < r.bottom.val ∧ (z.toPerm.symm 0).val < m := by
  obtain ⟨hwrap, d, hd, hc⟩ := (seamFirstFactorRectangle_not_isEmpty_iff r z he).mp hb
  have hr : r.right ≠ Fin.last n := fun hh => r.left_ne_right (hl.trans hh.symm)
  rw [hl, seamFirstFactorColumn_last, seamFirstFactorColumn, if_neg hr, Grid.mem_cIoo] at hc
  have hrn : r.right.val < n := by
    have := r.right.isLt
    have hh : r.right.val ≠ n := fun h => hr (Fin.ext h)
    omega
  have hcol : ¬ (seamRight n m (z.toPerm.symm 0)).val < (seamLeft n m r.right).val := by
    simp only [seamLeft_val, seamRight_val]
    omega
  rw [if_neg hcol] at hc
  have hdd := hc.2
  simp only [seamRight_val, seamLeft_val] at hdd
  have hv := d.isLt
  exact ⟨hwrap, by omega⟩

theorem seamShortLift_seamState_left_ne_last (x : GridState (n + 1)) (z : GridState (m + 1))
    (a : Fin (n + 1)) (ha : a ≠ Fin.last n) :
    seamState x z (seamLeft n m a) = seamLeft n m (x a) := by
  have hh := seamState_firstFactorColumn x z a
  simpa only [seamFirstFactorColumn, if_neg ha] using hh

theorem seamShortLift_target_empty {k : ℕ} {v w : GridState k}
    (r : GridRectangleBetween v w) (he : r.IsEmpty) :
    ∀ c ∈ Grid.cIoo r.left r.right, w c ∉ Grid.cIoo r.bottom r.top := by
  simpa only [r.map_right, r.map_left, bottom_def, top_def] using
    (isEmpty_iff_forall_notMem_cIoo_target r).mp he

set_option backward.isDefEq.respectTransparency false in
/-- The last-right-endpoint obstruction has a correction with no internal transition. -/
def seamFirstFactorShortLift_right_last {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hr : r.right = Fin.last n) : SeamCorrectionPath 0 (x, z) (y, z) := by
  classical
  have hwrap := (seamFirstFactorRectangle_blocked_right_last r z he hb hr).1
  have hdpos := (seamFirstFactorRectangle_blocked_right_last r z he hb hr).2
  let A := seamLeft n m r.left
  let C := seamRight n m 0
  let D := seamRight n m (z.toPerm.symm 0)
  let w := (seamState y z).swapColumns A C
  have hl : r.left ≠ Fin.last n := fun hh => r.left_ne_right (hh.trans hr.symm)
  have hln : r.left.val < n := by
    have h := r.left.isLt
    have hne : r.left.val ≠ n := fun hh => hl (Fin.ext hh)
    omega
  have hA : A.val < n := hln
  have hC : C.val = n := by simp [C]
  have hCD : C < D := by change n + 0 < n + (z.toPerm.symm 0).val; omega
  have hAC : A ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hDA : D ≠ A := fun h => by have hh := congrArg Fin.val h; have hh' := hCD; omega
  have hz0 : z 0 ≠ 0 := by
    intro hh
    have hd : z.toPerm.symm 0 = 0 := z.toPerm.symm_apply_eq.mpr hh.symm
    rw [hd] at hdpos
    exact Nat.lt_irrefl 0 hdpos
  have hhigh : n < (seamRight n m (z 0)).val := by
    have hzv : (z 0).val ≠ 0 := fun hh => hz0 (Fin.ext hh)
    simp only [seamRight_val]
    omega
  have hpA : seamState x z A = seamLeft n m r.bottom :=
    seamShortLift_seamState_left_ne_last x z _ hl
  have hqA : seamState y z A = seamLeft n m r.top := by
    rw [seamShortLift_seamState_left_ne_last y z _ hl, r.map_left, top_def]
  have hpC : seamState x z C = seamRight n m (z 0) :=
    seamState_right_of_ne_zero x z _ hz0
  have hqC : seamState y z C = seamRight n m (z 0) :=
    seamState_right_of_ne_zero y z _ hz0
  have hqD : seamState y z D = seamLeft n m r.bottom := by
    rw [seamState_right_of_zero y z _ (z.toPerm.apply_symm_apply 0), ← hr, r.map_right,
      bottom_def]
  have hswap : seamState y z = (seamState x z).swapColumns A D := by
    have hh := (seamFirstFactorRectangle r z).target_eq_swapColumns
    simpa only [seamFirstFactorRectangle_left, seamFirstFactorRectangle_right, hr,
      seamFirstFactorColumn, if_neg hl, ite_true] using hh
  have hwC : w C = seamLeft n m r.top := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_right, hqA]
  have hwD : w D = seamLeft n m r.bottom := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hDA hCD.ne.symm, hqD]
  have hsw : seamSouthwestColumns w = {C, D} := by
    let a := ofSwapColumns (seamState y z) w A C hAC rfl
    have hh := seamRectangle_birth_southwest_insert_right a
      (by simpa only [a, ofSwapColumns_left] using hA)
      (by simp only [a, ofSwapColumns_right]; omega)
      (by simpa only [a, ofSwapColumns_bottom, hqA, seamLeft_val]
        using Nat.le_of_lt_succ r.top.isLt)
      (by simpa only [a, ofSwapColumns_top, hqC] using hhigh)
    simpa only [a, ofSwapColumns_right, seamState_southwest_singleton] using hh
  have hrows : (w C).val < (w D).val := by
    rw [hwC, hwD, seamLeft_val, seamLeft_val]
    exact hwrap
  have hentry : w.swapColumns C D = (seamState x z).swapColumns A C := by
    change ((seamState y z).swapColumns A C).swapColumns C D = _
    rw [hswap, seamShortLift_swap_triangle _ A C D hDA hCD.ne.symm]
  let entry := ofSwapColumns (seamState x z) (w.swapColumns C D) A C hAC hentry
  let exit := ofSwapColumns w (seamState y z) A C hAC
    (GridState.swapColumns_swapColumns A C (seamState y z)).symm
  have hcol (c : Fin (n + m + 1)) (hc : c ∈ Grid.cIoo A C) :
      ∃ d : Fin n, c = seamLeft n m d.castSucc ∧ d.castSucc ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_pos (show A.val < C.val by omega)] at hc
    let d : Fin n := ⟨c.val, by omega⟩
    refine ⟨d, Fin.ext rfl, ?_⟩
    rw [hr, Grid.mem_cIoo, if_pos (show r.left.val < (Fin.last n).val from hln)]
    exact ⟨hl, by change r.left.val < c.val ∧ c.val < n; exact hc.2⟩
  have heEntry : entry.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo entry).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo A C := by
      simpa only [entry, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcol c hc'
    have hv' : seamLeft n m (x d.castSucc) ∈
        Grid.cIoo (seamLeft n m r.bottom) (seamRight n m (z 0)) := by
      simpa only [entry, ofSwapColumns_bottom, ofSwapColumns_top,
        seamState_left_castSucc, hpA, hpC] using hv
    rw [Grid.mem_cIoo, if_pos (by have := r.bottom.isLt; change r.bottom.val < _; omega)] at hv'
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inl hv'.2.1⟩
  have heExit : exit.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo_target exit).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo A C := by
      simpa only [exit, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcol c hc'
    have hv' : seamLeft n m (y d.castSucc) ∈
        Grid.cIoo (seamRight n m (z 0)) (seamLeft n m r.top) := by
      simpa only [exit, ofSwapColumns_right, ofSwapColumns_left,
        seamState_left_castSucc, hqA, hqC] using hv
    rw [Grid.mem_cIoo, if_neg (by have := r.top.isLt; change ¬ _ < r.top.val; omega)] at hv'
    have hlow : (y d.castSucc).val < r.top.val := by
      have hstate := (y d.castSucc).isLt
      have hh := hv'.2
      change (seamRight n m (z 0)).val < (y d.castSucc).val ∨
        (y d.castSucc).val < r.top.val at hh
      omega
    apply seamShortLift_target_empty r he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inr hlow⟩
  exact seamShortLift_correctionOfPair (x, z) (y, z) w C D hsw hCD hrows entry heEntry exit heExit

set_option backward.isDefEq.respectTransparency false in
/-- The last-left-endpoint obstruction has a correction with no internal transition. -/
def seamFirstFactorShortLift_left_last {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left = Fin.last n) : SeamCorrectionPath 0 (x, z) (y, z) := by
  classical
  have hwrap := (seamFirstFactorRectangle_blocked_left_last r z he hb hl).1
  have hdlt := (seamFirstFactorRectangle_blocked_left_last r z he hb hl).2
  let A := seamLeft n m r.right
  let C := seamRight n m (Fin.last m)
  let D := seamRight n m (z.toPerm.symm 0)
  let w := (seamState y z).swapColumns A C
  have hr : r.right ≠ Fin.last n := fun hh => r.left_ne_right (hl.trans hh.symm)
  have hrn : r.right.val < n := by
    have h := r.right.isLt
    have hne : r.right.val ≠ n := fun hh => hr (Fin.ext hh)
    omega
  have hA : A.val < n := hrn
  have hC : C.val = n + m := by simp [C]
  have hD : n ≤ D.val := by change n ≤ n + (z.toPerm.symm 0).val; omega
  have hDC : D < C := by change n + (z.toPerm.symm 0).val < n + m; omega
  have hAC : A ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hDA : D ≠ A := fun h => by have hh := congrArg Fin.val h; omega
  have hzlast : z (Fin.last m) ≠ 0 := by
    intro hh
    have hd : z.toPerm.symm 0 = Fin.last m := z.toPerm.symm_apply_eq.mpr hh.symm
    rw [hd] at hdlt
    exact Nat.lt_irrefl m hdlt
  have hhigh : n < (seamRight n m (z (Fin.last m))).val := by
    have hzv : (z (Fin.last m)).val ≠ 0 := fun hh => hzlast (Fin.ext hh)
    simp only [seamRight_val]
    omega
  have hpA : seamState x z A = seamLeft n m r.top :=
    seamShortLift_seamState_left_ne_last x z _ hr
  have hqA : seamState y z A = seamLeft n m r.bottom := by
    rw [seamShortLift_seamState_left_ne_last y z _ hr, r.map_right, bottom_def]
  have hpC : seamState x z C = seamRight n m (z (Fin.last m)) :=
    seamState_right_of_ne_zero x z _ hzlast
  have hqC : seamState y z C = seamRight n m (z (Fin.last m)) :=
    seamState_right_of_ne_zero y z _ hzlast
  have hqD : seamState y z D = seamLeft n m r.top := by
    rw [seamState_right_of_zero y z _ (z.toPerm.apply_symm_apply 0), ← hl, r.map_left,
      top_def]
  have hswap : seamState y z = (seamState x z).swapColumns A D := by
    have hh := (seamFirstFactorRectangle r z).target_eq_swapColumns
    simp only [seamFirstFactorRectangle_left, seamFirstFactorRectangle_right, hl,
      seamFirstFactorColumn, if_neg hr, ite_true] at hh
    rw [GridState.swapColumns_comm] at hh
    exact hh
  have hwC : w C = seamLeft n m r.bottom := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_right, hqA]
  have hwD : w D = seamLeft n m r.top := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hDA hDC.ne, hqD]
  have hsw : seamSouthwestColumns w = {D, C} := by
    let a := ofSwapColumns (seamState y z) w A C hAC rfl
    have hh := seamRectangle_birth_southwest_insert_right a
      (by simpa only [a, ofSwapColumns_left] using hA)
      (by simp only [a, ofSwapColumns_right]; omega)
      (by simpa only [a, ofSwapColumns_bottom, hqA, seamLeft_val]
        using Nat.le_of_lt_succ r.bottom.isLt)
      (by simpa only [a, ofSwapColumns_top, hqC] using hhigh)
    simpa only [a, ofSwapColumns_right, seamState_southwest_singleton, Finset.pair_comm] using hh
  have hrows : (w D).val < (w C).val := by
    rw [hwD, hwC, seamLeft_val, seamLeft_val]
    exact hwrap
  have hentry : w.swapColumns D C = (seamState x z).swapColumns C A := by
    change ((seamState y z).swapColumns A C).swapColumns D C = _
    rw [GridState.swapColumns_comm D C, hswap,
      seamShortLift_swap_triangle _ A C D hDA hDC.ne, GridState.swapColumns_comm A C]
  have hexit : seamState y z = w.swapColumns C A := by
    change seamState y z = ((seamState y z).swapColumns A C).swapColumns C A
    rw [GridState.swapColumns_comm C A, GridState.swapColumns_swapColumns]
  let entry := ofSwapColumns (seamState x z) (w.swapColumns D C) C A hAC.symm hentry
  let exit := ofSwapColumns w (seamState y z) C A hAC.symm hexit
  have hcol (c : Fin (n + m + 1)) (hc : c ∈ Grid.cIoo C A) :
      ∃ d : Fin n, c = seamLeft n m d.castSucc ∧ d.castSucc ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_neg (show ¬ C.val < A.val by omega)] at hc
    have hcv := c.isLt
    have hcA : c.val < A.val := by omega
    let d : Fin n := ⟨c.val, by omega⟩
    refine ⟨d, Fin.ext rfl, ?_⟩
    rw [hl, Grid.mem_cIoo, if_neg (show ¬ (Fin.last n).val < r.right.val by
      change ¬ n < r.right.val; omega)]
    exact ⟨hr.symm, Or.inr hcA⟩
  have heEntry : entry.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo entry).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo C A := by
      simpa only [entry, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcol c hc'
    have hv' : seamLeft n m (x d.castSucc) ∈
        Grid.cIoo (seamRight n m (z (Fin.last m))) (seamLeft n m r.top) := by
      simpa only [entry, ofSwapColumns_bottom, ofSwapColumns_top,
        seamState_left_castSucc, hpA, hpC] using hv
    rw [Grid.mem_cIoo, if_neg (by have := r.top.isLt; change ¬ _ < r.top.val; omega)] at hv'
    have hlow : (x d.castSucc).val < r.top.val := by
      have hstate := (x d.castSucc).isLt
      have hh := hv'.2
      change (seamRight n m (z (Fin.last m))).val < (x d.castSucc).val ∨
        (x d.castSucc).val < r.top.val at hh
      omega
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inr hlow⟩
  have heExit : exit.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo_target exit).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo C A := by
      simpa only [exit, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcol c hc'
    have hv' : seamLeft n m (y d.castSucc) ∈
        Grid.cIoo (seamLeft n m r.bottom) (seamRight n m (z (Fin.last m))) := by
      simpa only [exit, ofSwapColumns_right, ofSwapColumns_left,
        seamState_left_castSucc, hqA, hqC] using hv
    rw [Grid.mem_cIoo, if_pos (by have := r.bottom.isLt; change r.bottom.val < _; omega)] at hv'
    apply seamShortLift_target_empty r he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inl hv'.2.1⟩
  exact seamShortLift_correctionOfPair (x, z) (y, z) w D C hsw hDC hrows entry heEntry exit heExit

/-- Every obstructed empty first-factor rectangle with a last-column side has a short correction. -/
def seamFirstFactorShortLift {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hlast : r.left = Fin.last n ∨ r.right = Fin.last n) :
    SeamCorrectionPath 0 (x, z) (y, z) := by
  classical
  by_cases hl : r.left = Fin.last n
  · exact seamFirstFactorShortLift_left_last r z he hb hl
  · exact seamFirstFactorShortLift_right_last r z he hb (hlast.resolve_left hl)

/-- The shared-column construction uses the specified swap of the retained target. -/
theorem seamFirstFactorShortLift_right_last_node {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hr : r.right = Fin.last n) :
    (seamFirstFactorShortLift_right_last r z he hb hr).1.val.val =
      (seamState y z).swapColumns (seamLeft n m r.left) (seamRight n m 0) := rfl

/-- The final-column construction uses the specified swap of the retained target. -/
theorem seamFirstFactorShortLift_left_last_node {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left = Fin.last n) :
    (seamFirstFactorShortLift_left_last r z he hb hl).1.val.val =
      (seamState y z).swapColumns (seamLeft n m r.right)
        (seamRight n m (Fin.last m)) := rfl

/-- Both rectangles in the shared-column correction have the displayed endpoints. -/
theorem seamFirstFactorShortLift_right_last_sides {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hr : r.right = Fin.last n) :
    let p := seamFirstFactorShortLift_right_last r z he hb hr
    p.2.1 = p.1 ∧
      p.2.2.1.val.left = seamLeft n m r.left ∧
      p.2.2.1.val.right = seamRight n m 0 ∧
      p.2.2.2.2.val.left = seamLeft n m r.left ∧
      p.2.2.2.2.val.right = seamRight n m 0 := by
  simp only [seamFirstFactorShortLift_right_last, seamShortLift_correctionOfPair,
    ofSwapColumns_left, ofSwapColumns_right, and_self]

/-- Both rectangles in the final-column correction have the displayed endpoints. -/
theorem seamFirstFactorShortLift_left_last_sides {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left = Fin.last n) :
    let p := seamFirstFactorShortLift_left_last r z he hb hl
    p.2.1 = p.1 ∧
      p.2.2.1.val.left = seamRight n m (Fin.last m) ∧
      p.2.2.1.val.right = seamLeft n m r.right ∧
      p.2.2.2.2.val.left = seamRight n m (Fin.last m) ∧
      p.2.2.2.2.val.right = seamLeft n m r.right := by
  simp only [seamFirstFactorShortLift_left_last, seamShortLift_correctionOfPair,
    ofSwapColumns_left, ofSwapColumns_right, and_self]

/-- The shared-column correction belongs to the orientation with both left sides below the cut. -/
theorem seamFirstFactorShortLift_right_last_small_sides {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hr : r.right = Fin.last n) :
    let p := seamFirstFactorShortLift_right_last r z he hb hr
    p.2.2.1.val.left.val < n ∧ p.2.2.2.2.val.left.val < n := by
  have hs := seamFirstFactorShortLift_right_last_sides r z he hb hr
  dsimp only
  rw [hs.2.1, hs.2.2.2.1, seamLeft_val]
  have hne : r.left ≠ Fin.last n := fun hh => r.left_ne_right (hh.trans hr.symm)
  have hv : r.left.val ≠ n := fun hh => hne (Fin.ext hh)
  have hh := r.left.isLt
  exact ⟨by omega, by omega⟩

/-- The final-column correction belongs to the orientation with both right sides below the cut. -/
theorem seamFirstFactorShortLift_left_last_small_sides {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left = Fin.last n) :
    let p := seamFirstFactorShortLift_left_last r z he hb hl
    p.2.2.1.val.right.val < n ∧ p.2.2.2.2.val.right.val < n := by
  have hs := seamFirstFactorShortLift_left_last_sides r z he hb hl
  dsimp only
  rw [hs.2.2.1, hs.2.2.2.2, seamLeft_val]
  have hne : r.right ≠ Fin.last n := fun hh => r.left_ne_right (hl.trans hh.symm)
  have hv : r.right.val ≠ n := fun hh => hne (Fin.ext hh)
  have hh := r.right.isLt
  exact ⟨by omega, by omega⟩

/-- The first-factor index of the shared-column entry's left side is the original left side. -/
theorem seamFirstFactorShortLift_right_last_index {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hr : r.right = Fin.last n) :
    seamFirstFactorIndex
      (seamFirstFactorShortLift_right_last r z he hb hr).2.2.1.val.left = r.left := by
  rw [(seamFirstFactorShortLift_right_last_sides r z he hb hr).2.1]
  have hsmall := (seamFirstFactorShortLift_right_last_small_sides r z he hb hr).1
  rw [(seamFirstFactorShortLift_right_last_sides r z he hb hr).2.1] at hsmall
  simp only [seamFirstFactorIndex, dif_pos hsmall]
  exact Fin.ext rfl

/-- The first-factor index of the final-column entry's right side is the original right side. -/
theorem seamFirstFactorShortLift_left_last_index {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left = Fin.last n) :
    seamFirstFactorIndex
      (seamFirstFactorShortLift_left_last r z he hb hl).2.2.1.val.right = r.right := by
  rw [(seamFirstFactorShortLift_left_last_sides r z he hb hl).2.2.1]
  have hsmall := (seamFirstFactorShortLift_left_last_small_sides r z he hb hl).1
  rw [(seamFirstFactorShortLift_left_last_sides r z he hb hl).2.2.1] at hsmall
  simp only [seamFirstFactorIndex, dif_pos hsmall]
  exact Fin.ext rfl

end OnLeConjecture.KnotFloer.GridFull
