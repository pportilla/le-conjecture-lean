/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepLift

/-! # Two-step corrections with an interior zero preimage

An obstructed first-factor rectangle with nonlast endpoints has a two-step
correction when the second factor's zero row occurs strictly between its
first and last columns. The three matching states have respectively two,
three and two southwest columns. Every empty rectangle is constructed
from the given factor rectangle and the two extreme second-block columns.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- An interior second-factor zero preimage supplies two actual internal
rectangles for every obstructed first-factor rectangle with nonlast endpoints. -/
def seamFirstFactorTwoStepLift_interior {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n)
    (hd0 : 0 < (z.toPerm.symm 0).val) (hdm : (z.toPerm.symm 0).val < m) :
    SeamCorrectionPath 2 (x, z) (y, z) := by
  classical
  obtain ⟨hm, hcols, hln, hrn, hlo, hhi⟩ :=
    seamFirstFactor_blocked_nonlast_ranges r z he hb hl hr
  let A := seamLeft n m r.left
  let B := seamLeft n m r.right
  let C := seamRight n m 0
  let D := seamRight n m (z.toPerm.symm 0)
  let E := seamRight n m (Fin.last m)
  let V := seamState x z
  let W := seamState y z
  let X := (V.swapColumns E B).swapColumns D E
  let Y := (X.swapColumns A C).swapColumns C D
  let Z := W.swapColumns E B
  have hA : A.val < n := hln
  have hB : B.val < n := hrn
  have hBA : B.val < A.val := hcols
  have hC : C.val = n := by simp [C]
  have hD : D.val = n + (z.toPerm.symm 0).val := rfl
  have hE : E.val = n + m := by simp [E]
  have hCD : C < D := by change n + 0 < n + (z.toPerm.symm 0).val; omega
  have hDE : D < E := by change n + (z.toPerm.symm 0).val < n + m; omega
  have hCE : C < E := hCD.trans hDE
  have hAB : A ≠ B := fun h => by have := congrArg Fin.val h; omega
  have hAC : A ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hAD : A ≠ D := fun h => by have := congrArg Fin.val h; omega
  have hAE : A ≠ E := fun h => by have := congrArg Fin.val h; omega
  have hBC : B ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hBD : B ≠ D := fun h => by have := congrArg Fin.val h; omega
  have hBE : B ≠ E := fun h => by have := congrArg Fin.val h; omega
  have hz0 : z 0 ≠ 0 := by
    intro h
    have hh : z.toPerm.symm 0 = 0 := z.toPerm.symm_apply_eq.mpr h.symm
    rw [hh] at hd0
    exact Nat.lt_irrefl 0 hd0
  have hzlast : z (Fin.last m) ≠ 0 := by
    intro h
    have hh : z.toPerm.symm 0 = Fin.last m := z.toPerm.symm_apply_eq.mpr h.symm
    rw [hh] at hdm
    exact Nat.lt_irrefl m hdm
  have hhighC : n < (seamRight n m (z 0)).val := by
    have hh : (z 0).val ≠ 0 := fun h => hz0 (Fin.ext h)
    simp only [seamRight_val]
    omega
  have hhighE : n < (seamRight n m (z (Fin.last m))).val := by
    have hh : (z (Fin.last m)).val ≠ 0 := fun h => hzlast (Fin.ext h)
    simp only [seamRight_val]
    omega
  have hvA : V A = seamLeft n m r.bottom :=
    seamShortLift_seamState_left_ne_last x z _ hl
  have hvB : V B = seamLeft n m r.top :=
    seamShortLift_seamState_left_ne_last x z _ hr
  have hvC : V C = seamRight n m (z 0) := seamState_right_of_ne_zero x z _ hz0
  have hvD : V D = seamLeft n m (x (Fin.last n)) :=
    seamState_right_of_zero x z _ (z.toPerm.apply_symm_apply 0)
  have hvE : V E = seamRight n m (z (Fin.last m)) := seamState_right_of_ne_zero x z _ hzlast
  have hwB : W B = seamLeft n m r.bottom := by
    rw [seamShortLift_seamState_left_ne_last y z _ hr, r.map_right, bottom_def]
  have hwC : W C = seamRight n m (z 0) := seamState_right_of_ne_zero y z _ hz0
  have hwD : W D = seamLeft n m (x (Fin.last n)) := by
    rw [seamState_right_of_zero y z _ (z.toPerm.apply_symm_apply 0),
      r.map_of_ne _ hl.symm hr.symm]
  have hwE : W E = seamRight n m (z (Fin.last m)) := seamState_right_of_ne_zero y z _ hzlast
  have hW : W = V.swapColumns A B := by
    have hh := (seamFirstFactorRectangle r z).target_eq_swapColumns
    simpa only [seamFirstFactorRectangle_left, seamFirstFactorRectangle_right,
      seamFirstFactorColumn, if_neg hl, if_neg hr] using hh
  have hXA : X A = seamLeft n m r.bottom := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hAD hAE,
      Equiv.swap_apply_of_ne_of_ne hAE hAB, hvA]
  have hXC : X C = seamRight n m (z 0) := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hCD.ne hCE.ne,
      Equiv.swap_apply_of_ne_of_ne hCE.ne hBC.symm, hvC]
  have hXD : X D = seamLeft n m r.top := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_left, hvB]
  have hXE : X E = seamLeft n m (x (Fin.last n)) := by
    simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hDE.ne hBD.symm, hvD]
  have hYA : Y A = seamRight n m (z 0) := by
    simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hAC hAD,
      Equiv.swap_apply_left, hXC]
  have hYC : Y C = seamLeft n m r.top := by
    simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hAD.symm hCD.ne.symm, hXD]
  have hYD : Y D = seamLeft n m r.bottom := by
    simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_right, hXA]
  have hYE : Y E = seamLeft n m (x (Fin.last n)) := by
    simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hCE.ne.symm hDE.ne.symm,
      Equiv.swap_apply_of_ne_of_ne hAE.symm hCE.ne.symm, hXE]
  have hZC : Z C = seamRight n m (z 0) := by
    simp only [Z, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCE.ne hBC.symm, hwC]
  have hZD : Z D = seamLeft n m (x (Fin.last n)) := by
    simp only [Z, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hDE.ne hBD.symm, hwD]
  have hZE : Z E = seamLeft n m r.bottom := by
    simp only [Z, GridState.swapColumns_apply, Equiv.swap_apply_left, hwB]
  have hsV : seamSouthwestColumns V = {D} := seamState_southwest_singleton x z
  have hsX : seamSouthwestColumns X = {D, E} := by
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hcD : c = D
    · subst c
      simp only [true_or, iff_true, mem_seamSouthwestColumns, hXD, seamLeft_val]
      exact ⟨by omega, Nat.le_of_lt_succ r.top.isLt⟩
    by_cases hcE : c = E
    · subst c
      simp only [or_true, iff_true, mem_seamSouthwestColumns, hXE, seamLeft_val]
      exact ⟨by omega, Nat.le_of_lt_succ (x (Fin.last n)).isLt⟩
    simp only [hcD, hcE, or_self, iff_false]
    intro hc
    obtain ⟨hcn, hcr⟩ := (mem_seamSouthwestColumns _ _).mp hc
    have hcB : c ≠ B := fun h => by have := congrArg Fin.val h; omega
    have hv : X c = V c := by
      simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcD hcE,
        Equiv.swap_apply_of_ne_of_ne hcE hcB]
    have hh := (mem_seamSouthwestColumns V c).mpr ⟨hcn, by rwa [← hv]⟩
    rw [hsV, Finset.mem_singleton] at hh
    exact hcD hh
  have hsY : seamSouthwestColumns Y = {C, D, E} := by
    let T := X.swapColumns A C
    have htC : (T C).val ≤ n := by
      simp only [T, GridState.swapColumns_apply, Equiv.swap_apply_right, hXA, seamLeft_val]
      exact Nat.le_of_lt_succ r.bottom.isLt
    have htD : (T D).val ≤ n := by
      simp only [T, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hAD.symm hCD.ne.symm, hXD, seamLeft_val]
      exact Nat.le_of_lt_succ r.top.isLt
    have hswap : seamSouthwestColumns Y = seamSouthwestColumns T := by
      ext c
      change c ∈ seamSouthwestColumns (T.swapColumns C D) ↔ _
      simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply]
      by_cases hcC : c = C
      · subst c; simp only [Equiv.swap_apply_left]; omega
      by_cases hcD : c = D
      · subst c; simp only [Equiv.swap_apply_right]; omega
      rw [Equiv.swap_apply_of_ne_of_ne hcC hcD]
    rw [hswap]
    let a := ofSwapColumns X T A C hAC rfl
    have hh := seamRectangle_birth_southwest_insert_right a
      (by simpa only [a, ofSwapColumns_left] using hA)
      (by simp only [a, ofSwapColumns_right]; omega)
      (by simpa only [a, ofSwapColumns_bottom, hXA, seamLeft_val] using
        Nat.le_of_lt_succ r.bottom.isLt)
      (by simpa only [a, ofSwapColumns_top, hXC] using hhighC)
    simpa only [a, ofSwapColumns_right, hsX] using hh
  have hsZ : seamSouthwestColumns Z = {D, E} := by
    let a := ofSwapColumns W Z E B hBE.symm rfl
    have hh := seamRectangle_birth_southwest_insert_left a
      (by simpa only [a, ofSwapColumns_right] using hB)
      (by simp only [a, ofSwapColumns_left]; omega)
      (by simpa only [a, ofSwapColumns_top, hwB, seamLeft_val] using
        Nat.le_of_lt_succ r.bottom.isLt)
      (by simpa only [a, ofSwapColumns_bottom, hwE] using hhighE)
    simpa only [a, ofSwapColumns_left, W, seamState_southwest_singleton,
      Finset.pair_comm] using hh
  have hXrows : (X D).val < (X E).val := by rw [hXD, hXE, seamLeft_val, seamLeft_val]; exact hlo
  have hZrows : (Z D).val < (Z E).val := by rw [hZD, hZE, seamLeft_val, seamLeft_val]; exact hhi
  let sx := seamShortLift_matchingSourceOfPair X D E hsX hDE hXrows
  let sz := seamShortLift_matchingSourceOfPair Z D E hsZ hDE hZrows
  have hycomp : ¬ SeamPairSector Y := not_pairSector_of_two_le_southwest_card Y (by
    rw [hsY]
    simp [hCD.ne, hCE.ne, hDE.ne])
  let cy : SeamComplement n m := ⟨Y, hycomp⟩
  have hfirst : seamComplementFirst cy = C := by
    apply (Finset.min'_eq_iff _ _ _).mpr
    change C ∈ seamSouthwestColumns Y ∧ ∀ b ∈ seamSouthwestColumns Y, C ≤ b
    rw [hsY]
    refine ⟨by simp, ?_⟩
    intro b hb'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact le_rfl
    · exact hCD.le
    · exact hCE.le
  have hsecond : seamComplementSecond cy = D := by
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hfirst]
    change D ∈ (seamSouthwestColumns Y).erase C ∧
      ∀ b ∈ (seamSouthwestColumns Y).erase C, D ≤ b
    rw [hsY]
    refine ⟨Finset.mem_erase.mpr ⟨hCD.ne.symm, by simp⟩, ?_⟩
    intro b hb'
    obtain ⟨hne, hb'⟩ := Finset.mem_erase.mp hb'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with h | rfl | rfl
    · exact False.elim (hne h)
    · exact le_rfl
    · exact hDE.le
  let sy : SeamMatchingSource n m := ⟨cy, by
    change (Y (seamComplementFirst cy)).val < (Y (seamComplementSecond cy)).val
    rw [hfirst, hsecond, hYC, hYD, seamLeft_val, seamLeft_val]
    omega⟩
  have hpX : (seamComplementPartner sx.val).val = X.swapColumns D E :=
    seamShortLift_matchingSourceOfPair_partner X D E hsX hDE hXrows
  have hpY : (seamComplementPartner sy.val).val = Y.swapColumns C D := by
    change Y.swapColumns (seamComplementFirst cy) (seamComplementSecond cy) = _
    rw [hfirst, hsecond]
  have hpZ : (seamComplementPartner sz.val).val = Z.swapColumns D E :=
    seamShortLift_matchingSourceOfPair_partner Z D E hsZ hDE hZrows
  have hentry : (seamComplementPartner sx.val).val = V.swapColumns E B := by
    rw [hpX]
    exact GridState.swapColumns_swapColumns D E (V.swapColumns E B)
  have hinternal1 : (seamComplementPartner sy.val).val = X.swapColumns A C := by
    rw [hpY]
    exact GridState.swapColumns_swapColumns C D (X.swapColumns A C)
  have hinternal2 : (seamComplementPartner sz.val).val = Y.swapColumns A C := by
    rw [hpZ]
    have hright : Y.swapColumns A C = X.swapColumns A D := by
      change ((X.swapColumns A C).swapColumns C D).swapColumns A C = _
      rw [GridState.swapColumns_swapColumns_conj (X.swapColumns A C) C D A C,
        GridState.swapColumns_swapColumns, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hAD.symm hCD.ne.symm]
    rw [hright]
    change (W.swapColumns E B).swapColumns D E = _
    rw [hW, GridState.swapColumns_swapColumns_conj V A B E B,
      Equiv.swap_apply_of_ne_of_ne hAE hAB, Equiv.swap_apply_right,
      GridState.swapColumns_swapColumns_conj (V.swapColumns E B) A E D E,
      Equiv.swap_apply_of_ne_of_ne hAD hAE, Equiv.swap_apply_right]
  let entry := ofSwapColumns V (seamComplementPartner sx.val).val E B hBE.symm hentry
  let inner1 := ofSwapColumns X (seamComplementPartner sy.val).val A C hAC hinternal1
  let inner2 := ofSwapColumns Y (seamComplementPartner sz.val).val A C hAC hinternal2
  let exit := ofSwapColumns Z W E B hBE.symm
    (GridState.swapColumns_swapColumns E B W).symm
  have hneXY : sx ≠ sy := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => s.val.val C) h
    change X C = Y C at hh
    rw [hXC, hYC] at hh
    have hv := congrArg Fin.val hh
    simp only [seamLeft_val] at hv
    have ht := r.top.isLt
    omega
  have hneYZ : sy ≠ sz := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => s.val.val C) h
    change Y C = Z C at hh
    rw [hYC, hZC] at hh
    have hv := congrArg Fin.val hh
    simp only [seamLeft_val] at hv
    have ht := r.top.isLt
    omega
  have hcolOuter (c : Fin (n + m + 1)) (hc : c ∈ Grid.cIoo E B) :
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
        d.castSucc ∈ Grid.cIoo r.left r.right ∧
        X c = seamLeft n m (x d.castSucc) ∧ Y c = seamLeft n m (x d.castSucc) := by
    have hc' := (Grid.mem_cIoo _ _ _).mp hc
    rw [if_pos (by omega)] at hc'
    let d : Fin n := ⟨c.val, by omega⟩
    have hdc : c = seamLeft n m d.castSucc := Fin.ext rfl
    have hca : c ≠ A := fun h => by have := congrArg Fin.val h; omega
    have hcb : c ≠ B := fun h => by have := congrArg Fin.val h; omega
    have hcc : c ≠ C := fun h => by have := congrArg Fin.val h; omega
    have hcd : c ≠ D := fun h => by have := congrArg Fin.val h; omega
    have hce : c ≠ E := fun h => by have := congrArg Fin.val h; omega
    have hx : X c = seamLeft n m (x d.castSucc) := by
      simp only [X, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcd hce,
        Equiv.swap_apply_of_ne_of_ne hce hcb]
      rw [hdc, seamState_left_castSucc]
    refine ⟨d, hdc, ?_, hx, ?_⟩
    · rw [Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨r.left_ne_right, Or.inl hc'.2.1⟩
    · simp only [Y, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcc hcd,
        Equiv.swap_apply_of_ne_of_ne hca hcc, hx]
  have heEntry : entry.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo entry).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo E B := by
      simpa only [entry, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcolOuter c hc'
    have hv' : seamLeft n m (x d.castSucc) ∈
        Grid.cIoo (seamRight n m (z (Fin.last m))) (seamLeft n m r.top) := by
      simpa only [entry, ofSwapColumns_bottom, ofSwapColumns_top,
        V, seamState_left_castSucc, hvE, hvB] using hv
    rw [Grid.mem_cIoo, if_neg (by have := r.top.isLt; change ¬ _ < r.top.val; omega)] at hv'
    have hxd := (x d.castSucc).isLt
    simp only [seamLeft_val] at hv'
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inr (by omega)⟩
  have heInner1 : inner1.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo inner1).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo A C := by
      simpa only [inner1, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, _, hd, hx, _⟩ := hcolInner c hc'
    have hv' : seamLeft n m (x d.castSucc) ∈
        Grid.cIoo (seamLeft n m r.bottom) (seamRight n m (z 0)) := by
      simpa only [inner1, ofSwapColumns_bottom, ofSwapColumns_top, hx, hXA, hXC] using hv
    rw [Grid.mem_cIoo, if_pos (by have := r.bottom.isLt; change r.bottom.val < _; omega)] at hv'
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inl hv'.2.1⟩
  have heInner2 : inner2.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo inner2).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo A C := by
      simpa only [inner2, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, _, hd, _, hy⟩ := hcolInner c hc'
    have hv' : seamLeft n m (x d.castSucc) ∈
        Grid.cIoo (seamRight n m (z 0)) (seamLeft n m r.top) := by
      simpa only [inner2, ofSwapColumns_bottom, ofSwapColumns_top, hy, hYA, hYC] using hv
    rw [Grid.mem_cIoo, if_neg (by have := r.top.isLt; change ¬ _ < r.top.val; omega)] at hv'
    have hxd := (x d.castSucc).isLt
    simp only [seamLeft_val] at hv'
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inr (by omega)⟩
  have heExit : exit.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo_target exit).mpr
    intro c hc hv
    have hc' : c ∈ Grid.cIoo E B := by
      simpa only [exit, ofSwapColumns_left, ofSwapColumns_right] using hc
    obtain ⟨d, rfl, hd⟩ := hcolOuter c hc'
    have hv' : seamLeft n m (y d.castSucc) ∈
        Grid.cIoo (seamLeft n m r.bottom) (seamRight n m (z (Fin.last m))) := by
      simpa only [exit, ofSwapColumns_right, ofSwapColumns_left,
        W, seamState_left_castSucc, hwB, hwE] using hv
    rw [Grid.mem_cIoo, if_pos (by have := r.bottom.isLt; change r.bottom.val < _; omega)] at hv'
    apply seamShortLift_target_empty r he d.castSucc hd
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨r.bottom_ne_top, Or.inl hv'.2.1⟩
  exact ⟨sx, sz, ⟨entry, heEntry⟩,
    ⟨sy, ⟨inner1, hneXY, heInner1⟩, ⟨sz, ⟨inner2, hneYZ, heInner2⟩, ⟨(), rfl⟩⟩⟩,
    ⟨exit, heExit⟩⟩

/-- Every blocked first-factor rectangle with nonlast endpoints has a
correction with one or two internal transitions, selected by the zero preimage. -/
def seamFirstFactorBlockedNonlastCorrection {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n) :
    SeamCorrectionPath 1 (x, z) (y, z) ⊕ SeamCorrectionPath 2 (x, z) (y, z) := by
  classical
  by_cases hz0 : z 0 = 0
  · exact Sum.inl (seamFirstFactorOneStepLift_zero r z he hb hl hr hz0)
  by_cases hzm : z (Fin.last m) = 0
  · exact Sum.inl (seamFirstFactorOneStepLift_last r z he hb hl hr hzm)
  have hd0 : 0 < (z.toPerm.symm 0).val := by
    have hne : (z.toPerm.symm 0).val ≠ 0 := by
      intro h
      have hh : z.toPerm.symm 0 = 0 := Fin.ext h
      have happly := z.toPerm.apply_symm_apply 0
      rw [hh] at happly
      exact hz0 happly
    omega
  have hdm : (z.toPerm.symm 0).val < m := by
    have hbound := (z.toPerm.symm 0).isLt
    have hne : (z.toPerm.symm 0).val ≠ m := by
      intro h
      have hh : z.toPerm.symm 0 = Fin.last m := Fin.ext h
      have happly := z.toPerm.apply_symm_apply 0
      rw [hh] at happly
      exact hzm happly
    omega
  exact Sum.inr (seamFirstFactorTwoStepLift_interior r z he hb hl hr hd0 hdm)

/-- The constructed short correction belongs to the existing finite transfer-path type. -/
def seamFirstFactorBlockedNonlastTransferPath {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (z : GridState (m + 1))
    (he : r.IsEmpty) (hb : ¬ (seamFirstFactorRectangle r z).IsEmpty)
    (hl : r.left ≠ Fin.last n) (hr : r.right ≠ Fin.last n) :
    SeamTransferPath (x, z) (y, z) := by
  rcases seamFirstFactorBlockedNonlastCorrection r z he hb hl hr with p | p
  · exact Sum.inr ⟨⟨1, seamInternalPath_length_lt p.2.2.2.1⟩, p⟩
  · exact Sum.inr ⟨⟨2, seamInternalPath_length_lt p.2.2.2.1⟩, p⟩

end OnLeConjecture.KnotFloer.GridFull
