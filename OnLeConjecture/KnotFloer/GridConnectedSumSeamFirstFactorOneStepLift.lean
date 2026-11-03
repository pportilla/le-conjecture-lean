/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorShortLift

/-! # One-step corrections with a boundary zero preimage

For an obstructed first-factor rectangle with neither endpoint at the last
column, the factor point at the last column lies strictly between its rows.
When the second factor's zero row occurs in its first or last column, the
extreme second columns give a correction with exactly one internal empty rectangle.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The last factor point separates the endpoint rows of an obstructed rectangle
whose two column endpoints precede the last column. -/
theorem seamFirstFactor_blocked_nonlast_ranges {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n) :
    0 < m ∧ r.right.val < r.left.val ∧ r.left.val < n ∧ r.right.val < n ∧
      r.top.val < (x (Fin.last n)).val ∧ (x (Fin.last n)).val < r.bottom.val := by
  obtain ⟨hwrap, d, hd, hc⟩ := (seamFirstFactorRectangle_not_isEmpty_iff r z he).mp hb
  have hln : r.left.val < n := by
    have h := r.left.isLt
    have hn : r.left.val ≠ n := fun hh => hl (Fin.ext hh)
    omega
  have hrn : r.right.val < n := by
    have h := r.right.isLt
    have hn : r.right.val ≠ n := fun hh => hr (Fin.ext hh)
    omega
  have hm : 0 < m := by
    have hz := (z d).isLt
    have hz0 : (z d).val ≠ 0 := fun hh => hd (Fin.ext hh)
    omega
  have hcols : r.right.val < r.left.val := by
    simp only [seamFirstFactorColumn, if_neg hl, if_neg hr, Grid.mem_cIoo,
      seamLeft_val, seamRight_val] at hc
    have hne : r.left.val ≠ r.right.val := fun h => r.left_ne_right (Fin.ext h)
    by_contra hnot
    have hlt : r.left.val < r.right.val := by omega
    rw [if_pos hlt] at hc
    have hbad := hc.2.2
    omega
  have hlast : Fin.last n ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.left_ne_right, Or.inl hln⟩
  have hempty := (isEmpty_iff_forall_notMem_cIoo r).mp he (Fin.last n) hlast
  have hnb : (x (Fin.last n)).val ≠ r.bottom.val := by
    intro hh
    have hh' : x (Fin.last n) = x r.left := Fin.ext hh
    exact hl (x.toPerm.injective hh').symm
  have hnt : (x (Fin.last n)).val ≠ r.top.val := by
    intro hh
    have hh' : x (Fin.last n) = x r.right := Fin.ext hh
    exact hr (x.toPerm.injective hh').symm
  rw [Grid.mem_cIoo, if_neg (by omega)] at hempty
  have hne := r.bottom_ne_top
  exact ⟨hm, hcols, hln, hrn, by omega, by omega⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the second factor's zero row is in column zero, a blocked rectangle
with neither endpoint last has a correction with one internal transition. -/
def seamFirstFactorOneStepLift_zero {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n)
    (hz : z 0 = 0) : SeamCorrectionPath 1 (x, z) (y, z) := by
  classical
  obtain ⟨hm, hcols, hln, hrn, hlo, hhi⟩ :=
    seamFirstFactor_blocked_nonlast_ranges r z he hb hl hr
  let A := seamLeft n m r.left
  let B := seamLeft n m r.right
  let C := seamRight n m 0
  let D := seamRight n m (Fin.last m)
  let V := seamState x z
  let W := seamState y z
  let X := (V.swapColumns D B).swapColumns C D
  let Y := W.swapColumns D B
  have hA : A.val < n := hln
  have hB : B.val < n := hrn
  have hBA : B.val < A.val := hcols
  have hC : C.val = n := by simp [C]
  have hD : D.val = n + m := by simp [D]
  have hCD : C < D := by change n + 0 < n + m; omega
  have hAB : A ≠ B := fun h => by have := congrArg Fin.val h; omega
  have hAC : A ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hAD : A ≠ D := fun h => by have := congrArg Fin.val h; omega
  have hBC : B ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hBD : B ≠ D := fun h => by have := congrArg Fin.val h; omega
  have hzpre : z.toPerm.symm 0 = 0 := z.toPerm.symm_apply_eq.mpr hz.symm
  have hzlast : z (Fin.last m) ≠ 0 := by
    intro h
    have hh := z.toPerm.injective (h.trans hz.symm)
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_last, Fin.val_zero] at hh'
    omega
  have hhigh : n < (seamRight n m (z (Fin.last m))).val := by
    have hh : (z (Fin.last m)).val ≠ 0 := fun h => hzlast (Fin.ext h)
    simp only [seamRight_val]
    omega
  have hvA : V A = seamLeft n m r.bottom :=
    seamShortLift_seamState_left_ne_last x z _ hl
  have hvB : V B = seamLeft n m r.top :=
    seamShortLift_seamState_left_ne_last x z _ hr
  have hvC : V C = seamLeft n m (x (Fin.last n)) := seamState_right_of_zero x z _ hz
  have hvD : V D = seamRight n m (z (Fin.last m)) := seamState_right_of_ne_zero x z _ hzlast
  have hwA : W A = seamLeft n m r.top := by
    rw [seamShortLift_seamState_left_ne_last y z _ hl, r.map_left, top_def]
  have hwB : W B = seamLeft n m r.bottom := by
    rw [seamShortLift_seamState_left_ne_last y z _ hr, r.map_right, bottom_def]
  have hwC : W C = seamLeft n m (x (Fin.last n)) := by
    rw [seamState_right_of_zero y z _ hz, r.map_of_ne _ hl.symm hr.symm]
  have hwD : W D = seamRight n m (z (Fin.last m)) := seamState_right_of_ne_zero y z _ hzlast
  have hW : W = V.swapColumns A B := by
    have hh := (seamFirstFactorRectangle r z).target_eq_swapColumns
    simpa only [seamFirstFactorRectangle_left, seamFirstFactorRectangle_right,
      seamFirstFactorColumn, if_neg hl, if_neg hr] using hh
  have hXC : X C = seamLeft n m r.top := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_left, hvB]
  have hXD : X D = seamLeft n m (x (Fin.last n)) := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hCD.ne hBC.symm, hvC]
  have hXA : X A = seamLeft n m r.bottom := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hAC hAD,
      Equiv.swap_apply_of_ne_of_ne hAD hAB, hvA]
  have hYC : Y C = seamLeft n m (x (Fin.last n)) := by
    simp only [Y, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCD.ne hBC.symm, hwC]
  have hYD : Y D = seamLeft n m r.bottom := by
    simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_left, hwB]
  have hYB : Y B = seamRight n m (z (Fin.last m)) := by
    simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_right, hwD]
  have hsV : seamSouthwestColumns V = {C} := by
    simpa only [V, C, hzpre] using
      (seamState_southwest_singleton x z)
  have hsX : seamSouthwestColumns X = {C, D} := by
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hcC : c = C
    · subst c
      simp only [true_or, iff_true, mem_seamSouthwestColumns, hXC, seamLeft_val]
      exact ⟨by omega, Nat.le_of_lt_succ r.top.isLt⟩
    by_cases hcD : c = D
    · subst c
      simp only [or_true, iff_true, mem_seamSouthwestColumns, hXD, seamLeft_val]
      exact ⟨by omega, Nat.le_of_lt_succ (x (Fin.last n)).isLt⟩
    simp only [hcC, hcD, or_self, iff_false]
    intro hc
    obtain ⟨hcn, hcr⟩ := (mem_seamSouthwestColumns _ _).mp hc
    have hcB : c ≠ B := fun h => by have := congrArg Fin.val h; omega
    have hv : X c = V c := by
      simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcC hcD,
        Equiv.swap_apply_of_ne_of_ne hcD hcB]
    have hh := (mem_seamSouthwestColumns V c).mpr ⟨hcn, by rwa [← hv]⟩
    rw [hsV, Finset.mem_singleton] at hh
    exact hcC hh
  have hsY : seamSouthwestColumns Y = {C, D} := by
    let a := ofSwapColumns W Y D B hBD.symm rfl
    have hh := seamRectangle_birth_southwest_insert_left a
      (by simpa only [a, ofSwapColumns_right] using hB)
      (by simp only [a, ofSwapColumns_left]; omega)
      (by simpa only [a, ofSwapColumns_top, hwB, seamLeft_val] using
        Nat.le_of_lt_succ r.bottom.isLt)
      (by simpa only [a, ofSwapColumns_bottom, hwD] using hhigh)
    simpa only [a, ofSwapColumns_left, W, seamState_southwest_singleton, hzpre,
      Finset.pair_comm] using hh
  have hXrows : (X C).val < (X D).val := by rw [hXC, hXD, seamLeft_val, seamLeft_val]; exact hlo
  have hYrows : (Y C).val < (Y D).val := by rw [hYC, hYD, seamLeft_val, seamLeft_val]; exact hhi
  let sx := seamShortLift_matchingSourceOfPair X C D hsX hCD hXrows
  let sy := seamShortLift_matchingSourceOfPair Y C D hsY hCD hYrows
  have hpX : (seamComplementPartner sx.val).val = X.swapColumns C D :=
    seamShortLift_matchingSourceOfPair_partner X C D hsX hCD hXrows
  have hpY : (seamComplementPartner sy.val).val = Y.swapColumns C D :=
    seamShortLift_matchingSourceOfPair_partner Y C D hsY hCD hYrows
  have hentry : (seamComplementPartner sx.val).val = V.swapColumns D B := by
    rw [hpX]
    exact GridState.swapColumns_swapColumns C D (V.swapColumns D B)
  have hinternal : (seamComplementPartner sy.val).val = X.swapColumns A C := by
    rw [hpY]
    change (W.swapColumns D B).swapColumns C D =
      (((V.swapColumns D B).swapColumns C D).swapColumns A C)
    rw [hW]
    apply GridState.ext
    intro c
    by_cases hca : c = A
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, hAB, hAC, hAD]
    by_cases hcb : c = B
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, 
        hBC, hBD, hAB.symm, hAD.symm, hBD.symm]
    by_cases hcc : c = C
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, hAB, hAC, hAD]
    by_cases hcd : c = D
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, 
        hCD.ne, hAC.symm, hAD.symm, hBC.symm, hCD.ne.symm]
    simp [GridState.swapColumns_apply, Equiv.swap_apply_def, hca, hcb, hcc, hcd]
  let entry := ofSwapColumns V (seamComplementPartner sx.val).val D B hBD.symm hentry
  let inner := ofSwapColumns X (seamComplementPartner sy.val).val A C hAC hinternal
  let exit := ofSwapColumns Y W D B hBD.symm
    (GridState.swapColumns_swapColumns D B W).symm
  have hsne : sx ≠ sy := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => s.val.val C) h
    change X C = Y C at hh
    rw [hXC, hYC] at hh
    have hv := congrArg Fin.val hh
    simp only [seamLeft_val] at hv
    omega
  have hcolOuter (c : Fin (n + m + 1)) (hc : c ∈ Grid.cIoo D B) :
      ∃ d : Fin n, c = seamLeft n m d.castSucc ∧
        d.castSucc ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc
    have hcv := c.isLt
    have hcb : c.val < B.val := by omega
    let d : Fin n := ⟨c.val, by omega⟩
    refine ⟨d, Fin.ext rfl, ?_⟩
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.left_ne_right, Or.inr hcb⟩
  have hcolInner (c : Fin (n + m + 1)) (hc : c ∈ Grid.cIoo A C) :
      ∃ d : Fin n, c = seamLeft n m d.castSucc ∧
        d.castSucc ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_pos (by omega)] at hc
    let d : Fin n := ⟨c.val, by omega⟩
    refine ⟨d, Fin.ext rfl, ?_⟩
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.left_ne_right, Or.inl hc.2.1⟩
  have heEntry : entry.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo entry).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo D B := by
      simpa only [entry, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcolOuter c hc'
    have hv' : seamLeft n m (x d.castSucc) ∈
        Grid.cIoo (seamRight n m (z (Fin.last m))) (seamLeft n m r.top) := by
      simpa only [entry, ofSwapColumns_bottom, ofSwapColumns_top,
        V, seamState_left_castSucc, hvD, hvB] using hv
    rw [Grid.mem_cIoo, if_neg (by have := r.top.isLt; change ¬ _ < r.top.val; omega)] at hv'
    have hxd := (x d.castSucc).isLt
    simp only [seamLeft_val] at hv'
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inr (by omega)⟩
  have heInner : inner.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo inner).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo A C := by
      simpa only [inner, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, hdc, hd⟩ := hcolInner c hc'
    have hcv : c.val < n := by rw [hdc]; exact d.isLt
    have hcb : c ≠ B := by
      intro h
      have hv := (Grid.mem_cIoo _ _ _).mp hc'
      rw [if_pos (by omega)] at hv
      have := congrArg Fin.val h
      omega
    have hcc : c ≠ C := fun h => by have := congrArg Fin.val h; omega
    have hcd : c ≠ D := fun h => by have := congrArg Fin.val h; omega
    have hxc : X c = seamLeft n m (x d.castSucc) := by
      simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcc hcd,
        Equiv.swap_apply_of_ne_of_ne hcd hcb]
      rw [hdc, seamState_left_castSucc]
    have hv' : x d.castSucc ∈ Grid.cIoo r.bottom r.top := by
      have hh : seamLeft n m (x d.castSucc) ∈
          Grid.cIoo (seamLeft n m r.bottom) (seamLeft n m r.top) := by
        simpa only [inner, ofSwapColumns_bottom, ofSwapColumns_top, hxc, hXA, hXC] using hv
      exact (seamLeft_mem_cIoo_iff _ _ _).mp hh
    exact (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd hv'
  have heExit : exit.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo_target exit).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo D B := by
      simpa only [exit, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcolOuter c hc'
    have hv' : seamLeft n m (y d.castSucc) ∈
        Grid.cIoo (seamLeft n m r.bottom) (seamRight n m (z (Fin.last m))) := by
      simpa only [exit, ofSwapColumns_right, ofSwapColumns_left,
        W, seamState_left_castSucc, hwB, hwD] using hv
    rw [Grid.mem_cIoo, if_pos (by have := r.bottom.isLt; change r.bottom.val < _; omega)] at hv'
    apply seamShortLift_target_empty r he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inl hv'.2.1⟩
  exact ⟨sx, sy, ⟨entry, heEntry⟩, ⟨sy, ⟨inner, hsne, heInner⟩, ⟨(), rfl⟩⟩, ⟨exit, heExit⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the second factor's zero row is in its last column, a blocked rectangle
with neither endpoint last has a correction with one internal transition. -/
def seamFirstFactorOneStepLift_last {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n)
    (hz : z (Fin.last m) = 0) : SeamCorrectionPath 1 (x, z) (y, z) := by
  classical
  obtain ⟨hm, hcols, hln, hrn, hlo, hhi⟩ :=
    seamFirstFactor_blocked_nonlast_ranges r z he hb hl hr
  let A := seamLeft n m r.left
  let B := seamLeft n m r.right
  let C := seamRight n m 0
  let D := seamRight n m (Fin.last m)
  let V := seamState x z
  let W := seamState y z
  let X := (V.swapColumns A C).swapColumns C D
  let Y := W.swapColumns A C
  have hA : A.val < n := hln
  have hB : B.val < n := hrn
  have hBA : B.val < A.val := hcols
  have hC : C.val = n := by simp [C]
  have hD : D.val = n + m := by simp [D]
  have hCD : C < D := by change n + 0 < n + m; omega
  have hAB : A ≠ B := fun h => by have := congrArg Fin.val h; omega
  have hAC : A ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hAD : A ≠ D := fun h => by have := congrArg Fin.val h; omega
  have hBC : B ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hBD : B ≠ D := fun h => by have := congrArg Fin.val h; omega
  have hzpre : z.toPerm.symm 0 = Fin.last m := z.toPerm.symm_apply_eq.mpr hz.symm
  have hz0 : z 0 ≠ 0 := by
    intro h
    have hh := z.toPerm.injective (h.trans hz.symm)
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_last, Fin.val_zero] at hh'
    omega
  have hhigh : n < (seamRight n m (z 0)).val := by
    have hh : (z 0).val ≠ 0 := fun h => hz0 (Fin.ext h)
    simp only [seamRight_val]
    omega
  have hvA : V A = seamLeft n m r.bottom :=
    seamShortLift_seamState_left_ne_last x z _ hl
  have hvB : V B = seamLeft n m r.top :=
    seamShortLift_seamState_left_ne_last x z _ hr
  have hvC : V C = seamRight n m (z 0) := seamState_right_of_ne_zero x z _ hz0
  have hvD : V D = seamLeft n m (x (Fin.last n)) := seamState_right_of_zero x z _ hz
  have hwA : W A = seamLeft n m r.top := by
    rw [seamShortLift_seamState_left_ne_last y z _ hl, r.map_left, top_def]
  have hwB : W B = seamLeft n m r.bottom := by
    rw [seamShortLift_seamState_left_ne_last y z _ hr, r.map_right, bottom_def]
  have hwC : W C = seamRight n m (z 0) := seamState_right_of_ne_zero y z _ hz0
  have hwD : W D = seamLeft n m (x (Fin.last n)) := by
    rw [seamState_right_of_zero y z _ hz, r.map_of_ne _ hl.symm hr.symm]
  have hW : W = V.swapColumns A B := by
    have hh := (seamFirstFactorRectangle r z).target_eq_swapColumns
    simpa only [seamFirstFactorRectangle_left, seamFirstFactorRectangle_right,
      seamFirstFactorColumn, if_neg hl, if_neg hr] using hh
  have hXC : X C = seamLeft n m (x (Fin.last n)) := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hAD.symm hCD.ne.symm, hvD]
  have hXD : X D = seamLeft n m r.bottom := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_right, hvA]
  have hXB : X B = seamLeft n m r.top := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hBC hBD,
      Equiv.swap_apply_of_ne_of_ne hAB.symm hBC, hvB]
  have hYC : Y C = seamLeft n m r.top := by
    simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_right, hwA]
  have hYD : Y D = seamLeft n m (x (Fin.last n)) := by
    simp only [Y, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hAD.symm hCD.ne.symm, hwD]
  have hsV : seamSouthwestColumns V = {D} := by
    simpa only [V, D, hzpre] using (seamState_southwest_singleton x z)
  have hsX : seamSouthwestColumns X = {C, D} := by
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hcC : c = C
    · subst c
      simp only [true_or, iff_true, mem_seamSouthwestColumns, hXC, seamLeft_val]
      exact ⟨by omega, Nat.le_of_lt_succ (x (Fin.last n)).isLt⟩
    by_cases hcD : c = D
    · subst c
      simp only [or_true, iff_true, mem_seamSouthwestColumns, hXD, seamLeft_val]
      exact ⟨by omega, Nat.le_of_lt_succ r.bottom.isLt⟩
    simp only [hcC, hcD, or_self, iff_false]
    intro hc
    obtain ⟨hcn, hcr⟩ := (mem_seamSouthwestColumns _ _).mp hc
    have hcA : c ≠ A := fun h => by have := congrArg Fin.val h; omega
    have hv : X c = V c := by
      simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcC hcD,
        Equiv.swap_apply_of_ne_of_ne hcA hcC]
    have hh := (mem_seamSouthwestColumns V c).mpr ⟨hcn, by rwa [← hv]⟩
    rw [hsV, Finset.mem_singleton] at hh
    exact hcD hh
  have hsY : seamSouthwestColumns Y = {C, D} := by
    let a := ofSwapColumns W Y A C hAC rfl
    have hh := seamRectangle_birth_southwest_insert_right a
      (by simpa only [a, ofSwapColumns_left] using hA)
      (by simp only [a, ofSwapColumns_right]; omega)
      (by simpa only [a, ofSwapColumns_bottom, hwA, seamLeft_val] using
        Nat.le_of_lt_succ r.top.isLt)
      (by simpa only [a, ofSwapColumns_top, hwC] using hhigh)
    simpa only [a, ofSwapColumns_right, W, seamState_southwest_singleton, hzpre] using hh
  have hXrows : (X C).val < (X D).val := by rw [hXC, hXD, seamLeft_val, seamLeft_val]; exact hhi
  have hYrows : (Y C).val < (Y D).val := by rw [hYC, hYD, seamLeft_val, seamLeft_val]; exact hlo
  let sx := seamShortLift_matchingSourceOfPair X C D hsX hCD hXrows
  let sy := seamShortLift_matchingSourceOfPair Y C D hsY hCD hYrows
  have hpX : (seamComplementPartner sx.val).val = X.swapColumns C D :=
    seamShortLift_matchingSourceOfPair_partner X C D hsX hCD hXrows
  have hpY : (seamComplementPartner sy.val).val = Y.swapColumns C D :=
    seamShortLift_matchingSourceOfPair_partner Y C D hsY hCD hYrows
  have hentry : (seamComplementPartner sx.val).val = V.swapColumns A C := by
    rw [hpX]
    exact GridState.swapColumns_swapColumns C D (V.swapColumns A C)
  have hinternal : (seamComplementPartner sy.val).val = X.swapColumns D B := by
    rw [hpY]
    change (W.swapColumns A C).swapColumns C D =
      (((V.swapColumns A C).swapColumns C D).swapColumns D B)
    rw [hW]
    apply GridState.ext
    intro c
    by_cases hca : c = A
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, hAB, hAC, hAD,
        hAC.symm, hBC.symm]
    by_cases hcb : c = B
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, 
        hBC, hBD, hAB.symm]
    by_cases hcc : c = C
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, 
        hCD.ne, hAD.symm, hBC.symm, hBD.symm, hCD.ne.symm]
    by_cases hcd : c = D
    · subst c
      simp [GridState.swapColumns_apply, Equiv.swap_apply_def, 
        hBC, hBD, hAB.symm]
    simp [GridState.swapColumns_apply, Equiv.swap_apply_def, hca, hcb, hcc, hcd]
  let entry := ofSwapColumns V (seamComplementPartner sx.val).val A C hAC hentry
  let inner := ofSwapColumns X (seamComplementPartner sy.val).val D B hBD.symm hinternal
  let exit := ofSwapColumns Y W A C hAC
    (GridState.swapColumns_swapColumns A C W).symm
  have hsne : sx ≠ sy := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => s.val.val C) h
    change X C = Y C at hh
    rw [hXC, hYC] at hh
    have hv := congrArg Fin.val hh
    simp only [seamLeft_val] at hv
    omega
  have hcolOuter (c : Fin (n + m + 1)) (hc : c ∈ Grid.cIoo D B) :
      ∃ d : Fin n, c = seamLeft n m d.castSucc ∧
        d.castSucc ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc
    have hcv := c.isLt
    have hcb : c.val < B.val := by omega
    let d : Fin n := ⟨c.val, by omega⟩
    refine ⟨d, Fin.ext rfl, ?_⟩
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.left_ne_right, Or.inr hcb⟩
  have hcolInner (c : Fin (n + m + 1)) (hc : c ∈ Grid.cIoo A C) :
      ∃ d : Fin n, c = seamLeft n m d.castSucc ∧
        d.castSucc ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_pos (by omega)] at hc
    let d : Fin n := ⟨c.val, by omega⟩
    refine ⟨d, Fin.ext rfl, ?_⟩
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.left_ne_right, Or.inl hc.2.1⟩
  have heEntry : entry.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo entry).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo A C := by
      simpa only [entry, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcolInner c hc'
    have hv' : seamLeft n m (x d.castSucc) ∈
        Grid.cIoo (seamLeft n m r.bottom) (seamRight n m (z 0)) := by
      simpa only [entry, ofSwapColumns_bottom, ofSwapColumns_top,
        V, seamState_left_castSucc, hvA, hvC] using hv
    rw [Grid.mem_cIoo, if_pos (by have := r.bottom.isLt; change r.bottom.val < _; omega)] at hv'
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inl hv'.2.1⟩
  have heInner : inner.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo inner).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo D B := by
      simpa only [inner, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, hdc, hd⟩ := hcolOuter c hc'
    have hcv : c.val < n := by rw [hdc]; exact d.isLt
    have hca : c ≠ A := by
      intro h
      have hv := (Grid.mem_cIoo _ _ _).mp hc'
      rw [if_neg (by omega)] at hv
      have hv' := c.isLt
      have := congrArg Fin.val h
      omega
    have hcc : c ≠ C := fun h => by have := congrArg Fin.val h; omega
    have hcd : c ≠ D := fun h => by have := congrArg Fin.val h; omega
    have hxc : X c = seamLeft n m (x d.castSucc) := by
      simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcc hcd,
        Equiv.swap_apply_of_ne_of_ne hca hcc]
      rw [hdc, seamState_left_castSucc]
    have hv' : x d.castSucc ∈ Grid.cIoo r.bottom r.top := by
      have hh : seamLeft n m (x d.castSucc) ∈
          Grid.cIoo (seamLeft n m r.bottom) (seamLeft n m r.top) := by
        simpa only [inner, ofSwapColumns_bottom, ofSwapColumns_top, hxc, hXD, hXB] using hv
      exact (seamLeft_mem_cIoo_iff _ _ _).mp hh
    exact (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd hv'
  have heExit : exit.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo_target exit).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo A C := by
      simpa only [exit, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcolInner c hc'
    have hv' : seamLeft n m (y d.castSucc) ∈
        Grid.cIoo (seamRight n m (z 0)) (seamLeft n m r.top) := by
      simpa only [exit, ofSwapColumns_right, ofSwapColumns_left,
        W, seamState_left_castSucc, hwA, hwC] using hv
    rw [Grid.mem_cIoo, if_neg (by have := r.top.isLt; change ¬ _ < r.top.val; omega)] at hv'
    have hyd := (y d.castSucc).isLt
    simp only [seamLeft_val] at hv'
    apply seamShortLift_target_empty r he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inr (by omega)⟩
  exact ⟨sx, sy, ⟨entry, heEntry⟩, ⟨sy, ⟨inner, hsne, heInner⟩, ⟨(), rfl⟩⟩, ⟨exit, heExit⟩⟩

/-- Either boundary position of the second factor's zero row supplies an actual
one-internal-step correction for a blocked rectangle with nonlast endpoints. -/
def seamFirstFactorOneStepLift_boundary {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n)
    (hz : z 0 = 0 ∨ z (Fin.last m) = 0) : SeamCorrectionPath 1 (x, z) (y, z) :=
  if h : z 0 = 0 then seamFirstFactorOneStepLift_zero r z he hb hl hr h
  else seamFirstFactorOneStepLift_last r z he hb hl hr (hz.resolve_left h)

end OnLeConjecture.KnotFloer.GridFull
