/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondFactorOneStepExtrema

/-! # Projecting high one-step corrections to second-factor rectangles -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem secondOne_projection_empty (x : GridState (n + 1))
    (z w : GridState (m + 1))
    (R : GridRectangleBetween (seamState x z) (seamState x w))
    (hl : n ≤ R.left.val) (hr : n ≤ R.right.val)
    (he : ∀ c, n ≤ c.val → c ∈ Grid.cIoo R.left R.right →
      seamState x z c ∉ Grid.cIoo R.bottom R.top) :
    (seamRetainedSecondRectangle (x, z) (x, w) R hl hr).IsEmpty := by
  apply (isEmpty_iff_forall_notMem_cIoo _).mpr
  intro c hc hv
  have hcol : seamRight n m c ∈ Grid.cIoo R.left R.right := by
    rw [← seamRight_secondFactorIndex R.left hl, ← seamRight_secondFactorIndex R.right hr,
      seamRight_mem_cIoo_iff]
    exact hc
  have hrow : seamState x z (seamRight n m c) ∈ Grid.cIoo R.bottom R.top := by
    rw [seamState_secondFactorRow,
      ← seamRetainedSecondRectangle_bottom_recovery (x, z) (x, w) R hl hr,
      ← seamRetainedSecondRectangle_top_recovery (x, z) (x, w) R hl hr,
      seamSecondFactorRow_mem_cIoo_iff]
    exact hv
  exact he _ (by simp only [seamRight_val]; omega) hcol hrow

private theorem secondOne_projection_nonzero (x : GridState (n + 1))
    (z w : GridState (m + 1))
    (R : GridRectangleBetween (seamState x z) (seamState x w))
    (hl : n ≤ R.left.val) (hr : n ≤ R.right.val)
    (hb : n < R.bottom.val) (ht : n < R.top.val) :
    (seamRetainedSecondRectangle (x, z) (x, w) R hl hr).bottom ≠ 0 ∧
      (seamRetainedSecondRectangle (x, z) (x, w) R hl hr).top ≠ 0 := by
  have hn := (x (Fin.last n)).isLt
  constructor
  · intro h
    have hh := seamRetainedSecondRectangle_bottom_recovery (x, z) (x, w) R hl hr
    rw [h, seamSecondFactorRow_zero] at hh
    have hv := congrArg Fin.val hh
    simp only [seamLeft_val] at hv
    omega
  · intro h
    have hh := seamRetainedSecondRectangle_top_recovery (x, z) (x, w) R hl hr
    rw [h, seamSecondFactorRow_zero] at hh
    have hv := congrArg Fin.val hh
    simp only [seamLeft_val] at hv
    omega

section HighFirst
variable (x : GridState (n + 1)) (z w : GridState (m + 1))
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState x z) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState x w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) (heL : e.left.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementFirst a.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = C))
    (hfL : f.left = C) (hfR : f.right = e.left)
include he hr heL hCn hCv hsides hfL hfR

/-- The retained endpoint transposition is oriented from the high outside
column to the first southwest column. -/
theorem seamSecondOneStepHighFirst_target :
    seamState x w = (seamState x z).swapColumns C (seamComplementFirst a.val) := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨hrL, hrR, hQC, hbP, hbQ, _, _⟩ := seamOneStep_high_first r hr hcard C hCn hCv hsides
  have heR := seamMatchingEntry_right_eq_first_of_left_lt (x, z) a e he heL
  have hAv := (seamImmediateSecond_bottom_entry_rows (x, z) a e he heL).2.2
  have hh := seamSecondOneStep_target_eq_swap (x, z) (x, w) a b e r f .highFirst C e.left
    heL hAv (show flatRange .highFirst n a.val.val _ _ C from ⟨hCn, hCv, hQC⟩)
    hrL hrR hbP hbQ
    (by simp only [seamOneStepEntryLeft, if_true])
    (by simpa only [seamOneStepEntryLeft, if_true] using heR)
    (by simp only [seamOneStepExitLeft, Bool.false_eq_true, if_false]; rw [hfL, hbQ])
    (by simpa only [seamOneStepExitLeft, Bool.false_eq_true, if_false] using hfR)
  simpa only [seamOneStepNetLeft, seamOneStepNetRight, GridState.swapColumns_comm] using hh

/-- The full retained rectangle whose second-factor projection is required. -/
def seamSecondOneStepHighFirstFullRectangle :
    GridRectangleBetween (seamState x z) (seamState x w) :=
  ofSwapColumns _ _ C (seamComplementFirst a.val)
    (by
      have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
      intro h
      rw [h] at hCv
      omega)
    (seamSecondOneStepHighFirst_target x z w a b e r f he hr heL C hCn hCv hsides hfL hfR)

/-- The projected second-factor rectangle keeps the wrapping column orientation. -/
def seamSecondOneStepHighFirstRectangle : GridRectangleBetween z w :=
  seamRetainedSecondRectangle (x, z) (x, w)
    (seamSecondOneStepHighFirstFullRectangle x z w a b e r f he hr heL C hCn hCv hsides hfL hfR)
    (by simpa only [seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_left] using hCn)
    (by simpa only [seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_right] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)).1)

/-- Source values at the two projected columns, the zero column, and the pivot. -/
theorem seamSecondOneStepHighFirst_source_values :
    seamState x z C = a.val.val C ∧
      seamState x z (seamComplementFirst a.val) = a.val.val e.left ∧
      seamState x z (seamComplementSecond a.val) = a.val.val (seamComplementFirst a.val) ∧
      seamState x z e.left = a.val.val (seamComplementSecond a.val) := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨_, _, hQC, _, _, _, _⟩ := seamOneStep_high_first r hr hcard C hCn hCv hsides
  have hpq := seamComplementFirst_lt_second a.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have heR := seamMatchingEntry_right_eq_first_of_left_lt (x, z) a e he heL
  have hCA : C ≠ e.left := by intro h; have := congrArg Fin.val h; omega
  have hvC : seamState x z C = a.val.val C := by
    have hh := e.map_of_ne C hCA (by rw [heR]; exact (hpq.trans hQC).ne.symm)
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) C = _ at hh
    rw [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (hpq.trans hQC).ne.symm hQC.ne.symm] at hh
    exact hh.symm
  have hvP : seamState x z (seamComplementFirst a.val) = a.val.val e.left := by
    have hh := e.map_left
    rw [heR, seamComplementPartner_firstBlock_apply a.val e.left heL] at hh
    exact hh.symm
  have hvQ : seamState x z (seamComplementSecond a.val) =
      a.val.val (seamComplementFirst a.val) := by
    have hh := e.map_of_ne (seamComplementSecond a.val)
      (by intro h; have := congrArg Fin.val h; omega) (by rw [heR]; exact hpq.ne.symm)
    rw [seamComplementPartner_apply_second] at hh
    exact hh.symm
  have hvA : seamState x z e.left = a.val.val (seamComplementSecond a.val) := by
    have hh := e.map_right
    rw [heR, seamComplementPartner_apply_first] at hh
    exact hh.symm
  exact ⟨hvC, hvP, hvQ, hvA⟩

/-- Both endpoint rows of the full rectangle are high and occur in wrapping order. -/
theorem seamSecondOneStepHighFirst_rows :
    n < (a.val.val e.left).val ∧ (a.val.val e.left).val < (a.val.val C).val := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨hrL, hrR, hQC, _, _, _, _⟩ := seamOneStep_high_first r hr hcard C hCn hCv hsides
  have hpq := seamComplementFirst_lt_second a.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hAv := (seamImmediateSecond_bottom_entry_rows (x, z) a e he heL).2.2
  refine ⟨hAv, ?_⟩
  have hAC : e.left ≠ C := by intro h; have := congrArg Fin.val h; omega
  have hne : (a.val.val e.left).val ≠ (a.val.val C).val :=
    fun h => hAC (a.val.val.toPerm.injective (Fin.ext h))
  by_contra hn
  have hlt : (a.val.val C).val < (a.val.val e.left).val := by omega
  apply (isEmpty_iff_forall_notMem_cIoo r).mp hr e.left
  · rw [Grid.mem_cIoo, hrL, hrR, if_neg (by omega)]
    exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr (by omega)⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, if_neg (by omega)]
    exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hlt⟩

include hf in
/-- The retained rectangle is empty on every second-block column. -/
theorem seamSecondOneStepHighFirst_secondBlock_empty
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val)
    (hD : D ∈ Grid.cIoo C (seamComplementFirst a.val)) :
    seamState x z D ∉ Grid.cIoo (seamState x z C)
      (seamState x z (seamComplementFirst a.val)) := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨hrL, hrR, hQC, hbP, hbQ, _, hbC⟩ := seamOneStep_high_first r hr hcard C hCn hCv hsides
  have hPQ := seamComplementFirst_lt_second a.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hcols : C.val < D.val ∨ D.val < (seamComplementFirst a.val).val := by
    have hh := (Grid.mem_cIoo _ _ _).mp hD
    simpa only [if_neg (by omega : ¬ C.val < (seamComplementFirst a.val).val)] using hh.2
  have hDP : D ≠ seamComplementFirst a.val := by intro h; have := congrArg Fin.val h; omega
  have hDQ : D ≠ seamComplementSecond a.val := by intro h; have := congrArg Fin.val h; omega
  have hDC : D ≠ C := by intro h; have := congrArg Fin.val h; omega
  have hDA : D ≠ e.left := by intro h; have := congrArg Fin.val h; omega
  have hhigh : n < (a.val.val D).val := by
    by_contra hh
    have hm : D ∈ seamSouthwestColumns a.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨hDn, by omega⟩
    rw [seamComplement_southwest_eq_pair_of_card_two a.val hcard] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton, hDP, hDQ, or_self] at hm
  have heR := seamMatchingEntry_right_eq_first_of_left_lt (x, z) a e he heL
  obtain ⟨heB, heT, hAH⟩ := seamImmediateSecond_bottom_entry_rows (x, z) a e he heL
  have hvD : seamState x z D = a.val.val D := by
    have hh := e.map_of_ne D hDA (by rwa [heR])
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) D = _ at hh
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hDP hDQ] at hh
    exact hh.symm
  have hbD : b.val.val D = a.val.val D := by
    have hh := r.map_of_ne D (by rwa [hrL]) (by rwa [hrR])
    change b.val.val.swapColumns (seamComplementFirst b.val)
      (seamComplementSecond b.val) D = _ at hh
    simpa only [hbP, hbQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hDQ hDC] using hh
  have hbA : b.val.val e.left = a.val.val e.left :=
    seamSecondOneStep_firstBlock_apply r (by rwa [hrL]) (by simpa only [hrR] using hp.1) _ heL
  obtain ⟨hvC, hvP, _, _⟩ :=
    seamSecondOneStepHighFirst_source_values x z w a b e r f he hr heL C hCn hCv hsides hfL hfR
  have hrows := seamSecondOneStepHighFirst_rows x z w a b e r f he hr heL C hCn hCv hsides hfL hfR
  intro hrow
  rw [hvD, hvC, hvP, Grid.mem_cIoo, if_neg (by omega)] at hrow
  rcases hrow.2 with hlarge | hsmall
  · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr D
    · simpa only [hrL, hrR] using hD
    · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hlarge⟩
  · rcases hcols with hright | hleft
    · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf D
      · rw [Grid.mem_cIoo, hfL, hfR, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hright⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hfL, hfR, hbC, hbA, hbD, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hsmall⟩
    · apply (isEmpty_iff_forall_notMem_cIoo e).mp he D
      · rw [Grid.mem_cIoo, heR, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hleft⟩
      · rw [Grid.mem_cIoo, heB, heT, hvD, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hsmall⟩

include hf in
/-- The wrapping second-factor rectangle recovered from a high-first path is empty. -/
theorem seamSecondOneStepHighFirstRectangle_isEmpty :
    (seamSecondOneStepHighFirstRectangle x z w a b e r f he hr heL
      C hCn hCv hsides hfL hfR).IsEmpty := by
  apply secondOne_projection_empty
  intro D hDn hD
  simp only [seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_left,
    ofSwapColumns_right, ofSwapColumns_bottom, ofSwapColumns_top] at hD ⊢
  exact seamSecondOneStepHighFirst_secondBlock_empty x z w a b e r f he hr hf heL
    C hCn hCv hsides hfL hfR D hDn hD

/-- The projected rectangle has two nonzero endpoint rows and its direct lift
contains the first-block pivot. -/
theorem seamSecondOneStepHighFirstRectangle_obstructed_nonzero :
    let R := seamSecondOneStepHighFirstRectangle x z w a b e r f he hr heL C hCn hCv hsides hfL hfR
    ¬ (seamSecondFactorRectangle x R).IsEmpty ∧ R.bottom ≠ 0 ∧ R.top ≠ 0 := by
  obtain ⟨hvC, hvP, _, hvA⟩ :=
    seamSecondOneStepHighFirst_source_values x z w a b e r f he hr heL C hCn hCv hsides hfL hfR
  have hrows := seamSecondOneStepHighFirst_rows x z w a b e r f he hr heL C hCn hCv hsides hfL hfR
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  have hQC := (seamOneStep_high_first r hr hcard C hCn hCv hsides).2.2.1
  have hpq := seamComplementFirst_lt_second a.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  dsimp only
  refine ⟨?_, ?_⟩
  · change ¬ (seamSecondFactorRectangle x
      (seamRetainedSecondRectangle (x, z) (x, w)
        (seamSecondOneStepHighFirstFullRectangle x z w a b e r f he hr heL
          C hCn hCv hsides hfL hfR) _ _)).IsEmpty
    rw [seamSecondFactorRectangle_lift_project]
    intro hh
    apply (isEmpty_iff_forall_notMem_cIoo _).mp hh e.left
    · simp only [seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_left, ofSwapColumns_right]
      rw [Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr (by omega)⟩
    · simp only [seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_bottom, ofSwapColumns_top]
      rw [hvC, hvP, hvA, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr (by omega)⟩
  · apply secondOne_projection_nonzero
    · simpa only [seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_bottom, hvC] using hCv
    · simpa only [seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_top, hvP] using hrows.1

include hf in
/-- A high-first correction supplies an actual remaining second-factor rectangle. -/
def seamSecondOneStepHighFirstRemaining : SeamSecondRemainingRectangle x z w :=
  ⟨seamSecondOneStepHighFirstRectangle x z w a b e r f he hr heL C hCn hCv hsides hfL hfR,
    seamSecondOneStepHighFirstRectangle_isEmpty x z w a b e r f he hr hf heL
      C hCn hCv hsides hfL hfR,
    seamSecondOneStepHighFirstRectangle_obstructed_nonzero x z w a b e r f he hr heL
      C hCn hCv hsides hfL hfR⟩

end HighFirst
section HighSecond
variable (x : GridState (n + 1)) (z w : GridState (m + 1))
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState x z) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState x w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) (heR : e.right.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementSecond a.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = C))
    (hfL : f.left = e.right) (hfR : f.right = C)
include he hr heR hCn hCv hsides hfL hfR

/-- The high-second retained transposition uses the second-to-outside orientation. -/
theorem seamSecondOneStepHighSecond_target :
    seamState x w = (seamState x z).swapColumns (seamComplementSecond a.val) C := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨hrL, hrR, hCP, hbP, hbQ, _, _⟩ := seamOneStep_high_second r hr hcard C hCn hCv hsides
  have heL := seamMatchingEntry_left_eq_second_of_right_lt (x, z) a e he heR
  have hAv := (seamImmediateSecond_top_entry_rows (x, z) a e he heR).2.2
  have hh := seamSecondOneStep_target_eq_swap (x, z) (x, w) a b e r f .highSecond C e.right
    heR hAv (show flatRange .highSecond n a.val.val _ _ C from ⟨hCn, hCv, hCP⟩)
    hrL hrR hbP hbQ
    (by simpa only [seamOneStepEntryLeft, Bool.false_eq_true, if_false] using heL)
    (by simp only [seamOneStepEntryLeft, Bool.false_eq_true, if_false])
    (by simpa only [seamOneStepExitLeft, if_true] using hfL)
    (by simp only [seamOneStepExitLeft, if_true]; rw [hfR, hbP])
  exact hh

/-- The high-second full retained rectangle. -/
def seamSecondOneStepHighSecondFullRectangle :
    GridRectangleBetween (seamState x z) (seamState x w) :=
  ofSwapColumns _ _ (seamComplementSecond a.val) C
    (by
      have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
      intro h
      rw [← h] at hCv
      omega)
    (seamSecondOneStepHighSecond_target x z w a b e r f he hr heR C hCn hCv hsides hfL hfR)

/-- Its second-factor projection preserves that wrapping column orientation. -/
def seamSecondOneStepHighSecondRectangle : GridRectangleBetween z w :=
  seamRetainedSecondRectangle (x, z) (x, w)
    (seamSecondOneStepHighSecondFullRectangle x z w a b e r f he hr heR C hCn hCv hsides hfL hfR)
    (by simpa only [seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_left] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)).1)
    (by simpa only [seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_right] using hCn)

/-- The exact source values in the high-second case. -/
theorem seamSecondOneStepHighSecond_source_values :
    seamState x z C = a.val.val C ∧
      seamState x z (seamComplementSecond a.val) = a.val.val e.right ∧
      seamState x z (seamComplementFirst a.val) = a.val.val (seamComplementSecond a.val) ∧
      seamState x z e.right = a.val.val (seamComplementFirst a.val) := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨_, _, hCP, _, _, _, _⟩ := seamOneStep_high_second r hr hcard C hCn hCv hsides
  have hpq := seamComplementFirst_lt_second a.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have heL := seamMatchingEntry_left_eq_second_of_right_lt (x, z) a e he heR
  have hCA : C ≠ e.right := by intro h; have := congrArg Fin.val h; omega
  have hvC : seamState x z C = a.val.val C := by
    have hh := e.map_of_ne C (by rw [heL]; exact (hCP.trans hpq).ne) hCA
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) C = _ at hh
    rw [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCP.ne (hCP.trans hpq).ne] at hh
    exact hh.symm
  have hvQ : seamState x z (seamComplementSecond a.val) = a.val.val e.right := by
    have hh := e.map_right
    rw [heL, seamComplementPartner_firstBlock_apply a.val e.right heR] at hh
    exact hh.symm
  have hvP : seamState x z (seamComplementFirst a.val) =
      a.val.val (seamComplementSecond a.val) := by
    have hh := e.map_of_ne (seamComplementFirst a.val)
      (by rw [heL]; exact hpq.ne) (by intro h; have := congrArg Fin.val h; omega)
    rw [seamComplementPartner_apply_first] at hh
    exact hh.symm
  have hvA : seamState x z e.right = a.val.val (seamComplementFirst a.val) := by
    have hh := e.map_left
    rw [heL, seamComplementPartner_apply_second] at hh
    exact hh.symm
  exact ⟨hvC, hvQ, hvP, hvA⟩

/-- Both endpoint rows are nonzero high rows, in wrapping order. -/
theorem seamSecondOneStepHighSecond_rows :
    n < (a.val.val C).val ∧ (a.val.val C).val < (a.val.val e.right).val := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨hrL, hrR, hCP, _, _, _, _⟩ := seamOneStep_high_second r hr hcard C hCn hCv hsides
  have hpq := seamComplementFirst_lt_second a.val
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hAv := (seamImmediateSecond_top_entry_rows (x, z) a e he heR).2.2
  refine ⟨hCv, ?_⟩
  have hAC : e.right ≠ C := by intro h; have := congrArg Fin.val h; omega
  have hne : (a.val.val e.right).val ≠ (a.val.val C).val :=
    fun h => hAC (a.val.val.toPerm.injective (Fin.ext h))
  by_contra hn
  have hlt : (a.val.val e.right).val < (a.val.val C).val := by omega
  apply (isEmpty_iff_forall_notMem_cIoo r).mp hr e.right
  · rw [Grid.mem_cIoo, hrL, hrR, if_neg (by omega)]
    exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr (by omega)⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, if_pos (by omega)]
    exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hlt⟩

include hf in
/-- The high-second retained rectangle is empty on all second-block columns. -/
theorem seamSecondOneStepHighSecond_secondBlock_empty
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val)
    (hD : D ∈ Grid.cIoo (seamComplementSecond a.val) C) :
    seamState x z D ∉ Grid.cIoo (seamState x z (seamComplementSecond a.val))
      (seamState x z C) := by
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  obtain ⟨hrL, hrR, hCP, hbP, hbQ, hbC, _⟩ := seamOneStep_high_second r hr hcard C hCn hCv hsides
  have hPQ := seamComplementFirst_lt_second a.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hcols : (seamComplementSecond a.val).val < D.val ∨ D.val < C.val := by
    have hh := (Grid.mem_cIoo _ _ _).mp hD
    simpa only [if_neg (by omega : ¬ (seamComplementSecond a.val).val < C.val)] using hh.2
  have hDP : D ≠ seamComplementFirst a.val := by intro h; have := congrArg Fin.val h; omega
  have hDQ : D ≠ seamComplementSecond a.val := by intro h; have := congrArg Fin.val h; omega
  have hDC : D ≠ C := by intro h; have := congrArg Fin.val h; omega
  have hDA : D ≠ e.right := by intro h; have := congrArg Fin.val h; omega
  have hhigh : n < (a.val.val D).val := by
    by_contra hh
    have hm : D ∈ seamSouthwestColumns a.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨hDn, by omega⟩
    rw [seamComplement_southwest_eq_pair_of_card_two a.val hcard] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton, hDP, hDQ, or_self] at hm
  have heL := seamMatchingEntry_left_eq_second_of_right_lt (x, z) a e he heR
  obtain ⟨heT, heB, hAH⟩ := seamImmediateSecond_top_entry_rows (x, z) a e he heR
  have hvD : seamState x z D = a.val.val D := by
    have hh := e.map_of_ne D (by rwa [heL]) hDA
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) D = _ at hh
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hDP hDQ] at hh
    exact hh.symm
  have hbD : b.val.val D = a.val.val D := by
    have hh := r.map_of_ne D (by rwa [hrL]) (by rwa [hrR])
    change b.val.val.swapColumns (seamComplementFirst b.val)
      (seamComplementSecond b.val) D = _ at hh
    simpa only [hbP, hbQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hDC hDP] using hh
  have hbA : b.val.val e.right = a.val.val e.right :=
    seamSecondOneStep_firstBlock_apply r (by simpa only [hrL] using hq.1) (by rwa [hrR]) _ heR
  obtain ⟨hvC, hvQ, _, _⟩ :=
    seamSecondOneStepHighSecond_source_values x z w a b e r f he hr heR C hCn hCv hsides hfL hfR
  have hrows := seamSecondOneStepHighSecond_rows x z w a b e r f he hr heR C hCn hCv hsides hfL hfR
  intro hrow
  rw [hvD, hvQ, hvC, Grid.mem_cIoo, if_neg (by omega)] at hrow
  rcases hrow.2 with hlarge | hsmall
  · rcases hcols with hright | hleft
    · apply (isEmpty_iff_forall_notMem_cIoo e).mp he D
      · rw [Grid.mem_cIoo, heL, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hright⟩
      · rw [Grid.mem_cIoo, heB, heT, hvD, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hlarge⟩
    · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf D
      · rw [Grid.mem_cIoo, hfL, hfR, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hleft⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hfL, hfR, hbC, hbA, hbD, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hlarge⟩
  · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr D
    · simpa only [hrL, hrR] using hD
    · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hsmall⟩

include hf in
/-- The projected high-second factor rectangle is empty. -/
theorem seamSecondOneStepHighSecondRectangle_isEmpty :
    (seamSecondOneStepHighSecondRectangle x z w a b e r f he hr heR
      C hCn hCv hsides hfL hfR).IsEmpty := by
  apply secondOne_projection_empty
  intro D hDn hD
  simp only [seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_left,
    ofSwapColumns_right, ofSwapColumns_bottom, ofSwapColumns_top] at hD ⊢
  exact seamSecondOneStepHighSecond_secondBlock_empty x z w a b e r f he hr hf heR
    C hCn hCv hsides hfL hfR D hDn hD

/-- The high-second factor rectangle has nonzero rows and an obstructed full lift. -/
theorem seamSecondOneStepHighSecondRectangle_obstructed_nonzero :
    let R := seamSecondOneStepHighSecondRectangle x z w a b e r f he hr heR C hCn hCv hsides hfL hfR
    ¬ (seamSecondFactorRectangle x R).IsEmpty ∧ R.bottom ≠ 0 ∧ R.top ≠ 0 := by
  obtain ⟨hvC, hvQ, _, hvA⟩ :=
    seamSecondOneStepHighSecond_source_values x z w a b e r f he hr heR C hCn hCv hsides hfL hfR
  have hrows := seamSecondOneStepHighSecond_rows x z w a b e r f he hr heR C hCn hCv hsides hfL hfR
  have hcard := seamMatchingEntry_southwest_card (x, z) a e
  have hCP := (seamOneStep_high_second r hr hcard C hCn hCv hsides).2.2.1
  have hpq := seamComplementFirst_lt_second a.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hAv := (seamImmediateSecond_top_entry_rows (x, z) a e he heR).2.2
  dsimp only
  refine ⟨?_, ?_⟩
  · change ¬ (seamSecondFactorRectangle x
      (seamRetainedSecondRectangle (x, z) (x, w)
        (seamSecondOneStepHighSecondFullRectangle x z w a b e r f he hr heR
          C hCn hCv hsides hfL hfR) _ _)).IsEmpty
    rw [seamSecondFactorRectangle_lift_project]
    intro hh
    apply (isEmpty_iff_forall_notMem_cIoo _).mp hh e.right
    · simp only [seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_left, ofSwapColumns_right]
      rw [Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr (by omega)⟩
    · simp only [seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_bottom, ofSwapColumns_top]
      rw [hvQ, hvC, hvA, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr (by omega)⟩
  · apply secondOne_projection_nonzero
    · simpa only [seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_bottom, hvQ] using hAv
    · simpa only [seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_top, hvC] using hCv

include hf in
/-- A high-second correction supplies an actual remaining second-factor rectangle. -/
def seamSecondOneStepHighSecondRemaining : SeamSecondRemainingRectangle x z w :=
  ⟨seamSecondOneStepHighSecondRectangle x z w a b e r f he hr heR C hCn hCv hsides hfL hfR,
    seamSecondOneStepHighSecondRectangle_isEmpty x z w a b e r f he hr hf heR
      C hCn hCv hsides hfL hfR,
    seamSecondOneStepHighSecondRectangle_obstructed_nonzero x z w a b e r f he hr heR
      C hCn hCv hsides hfL hfR⟩

end HighSecond
end OnLeConjecture.KnotFloer.GridFull
