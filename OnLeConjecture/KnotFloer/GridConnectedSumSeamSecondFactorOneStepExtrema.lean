/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondFactorOneStepBoundary

/-! # The outer low rows and first-block pivots of high one-step corrections -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A rectangle exchanging two second-block columns preserves every first-block point. -/
theorem seamSecondOneStep_firstBlock_apply {a b : SeamMatchingSource n m}
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (hl : n ≤ r.left.val) (hr : n ≤ r.right.val)
    (D : Fin (n + m + 1)) (hDn : D.val < n) : b.val.val D = a.val.val D := by
  have hh := r.map_of_ne D
    (by intro h; have := congrArg Fin.val h; omega)
    (by intro h; have := congrArg Fin.val h; omega)
  rwa [seamComplementPartner_firstBlock_apply b.val D hDn] at hh

/-- The outer rectangles of a high-first correction force its other low row to n. -/
theorem seamSecondOneStep_high_first_row_last (p q : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) (heL : e.left.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementFirst a.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = C))
    (hfL : f.left = C) (hfR : f.right = e.left) :
    a.val.val (seamComplementSecond a.val) = seamLeft n m (Fin.last n) := by
  have hcard := seamMatchingEntry_southwest_card p a e
  obtain ⟨hrL, hrR, _, _, _, _, hbC⟩ := seamOneStep_high_first r hr hcard C hCn hCv hsides
  have heR := seamMatchingEntry_right_eq_first_of_left_lt p a e he heL
  obtain ⟨heB, heT, hhigh⟩ := seamImmediateSecond_bottom_entry_rows p a e he heL
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hbPoint (D : Fin (n + m + 1)) (hDn : D.val < n) : b.val.val D = a.val.val D :=
    seamSecondOneStep_firstBlock_apply r (by rwa [hrL]) (by simpa only [hrR] using hp.1) D hDn
  have hrows : (a.val.val (seamComplementFirst a.val)).val <
      (a.val.val (seamComplementSecond a.val)).val := a.property
  apply Fin.ext
  change (a.val.val (seamComplementSecond a.val)).val = n
  by_contra hn
  have hbn : (a.val.val (seamComplementSecond a.val)).val < n := by omega
  let D := a.val.val.toPerm.symm (seamLeft n m (Fin.last n))
  have hD : a.val.val D = seamLeft n m (Fin.last n) := a.val.val.toPerm.apply_symm_apply _
  have hDP : D ≠ seamComplementFirst a.val := by
    intro h
    have hv := congrArg Fin.val hD
    rw [h] at hv
    change (a.val.val (seamComplementFirst a.val)).val = n at hv
    omega
  have hDQ : D ≠ seamComplementSecond a.val := by
    intro h
    have hv := congrArg Fin.val hD
    rw [h] at hv
    change (a.val.val (seamComplementSecond a.val)).val = n at hv
    omega
  have hDn : D.val < n := by
    by_contra hh
    have hm : D ∈ seamSouthwestColumns a.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by rw [hD]; exact le_rfl⟩
    rw [seamComplement_southwest_eq_pair_of_card_two a.val hcard] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton, hDP, hDQ, or_self] at hm
  have hDA : D ≠ e.left := by
    intro h
    have hv := congrArg Fin.val hD
    rw [h] at hv
    change (a.val.val e.left).val = n at hv
    omega
  have hvSource : seamState p.1 p.2 D = a.val.val D := by
    have hh := e.map_of_ne D hDA (by rwa [heR])
    rw [seamComplementPartner_firstBlock_apply a.val D hDn] at hh
    exact hh.symm
  by_cases hAD : e.left.val < D.val
  · apply (isEmpty_iff_forall_notMem_cIoo e).mp he D
    · rw [Grid.mem_cIoo, heR, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, hAD, by omega⟩
    · rw [hvSource, hD, heB, heT, Grid.mem_cIoo, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, hbn, hhigh⟩
  · have hDA' : D.val < e.left.val := by
      have hh : D.val ≠ e.left.val := fun h => hDA (Fin.ext h)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo f).mp hf D
    · rw [Grid.mem_cIoo, hfL, hfR, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr hDA'⟩
    · rw [bottom_def, top_def, hfL, hfR, hbC, hbPoint D hDn, hbPoint e.left heL,
        hD, Grid.mem_cIoo, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, hbn, hhigh⟩

/-- The outer rectangles of a high-second correction force its other low row to zero. -/
theorem seamSecondOneStep_high_second_row_zero (p q : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) (heR : e.right.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementSecond a.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = C))
    (hfL : f.left = e.right) (hfR : f.right = C) :
    a.val.val (seamComplementFirst a.val) = seamLeft n m 0 := by
  have hcard := seamMatchingEntry_southwest_card p a e
  obtain ⟨hrL, hrR, _, _, _, hbC, _⟩ := seamOneStep_high_second r hr hcard C hCn hCv hsides
  have heL := seamMatchingEntry_left_eq_second_of_right_lt p a e he heR
  obtain ⟨heT, heB, hhigh⟩ := seamImmediateSecond_top_entry_rows p a e he heR
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hbPoint (D : Fin (n + m + 1)) (hDn : D.val < n) : b.val.val D = a.val.val D :=
    seamSecondOneStep_firstBlock_apply r (by simpa only [hrL] using hq.1) (by rwa [hrR]) D hDn
  have hrows : (a.val.val (seamComplementFirst a.val)).val <
      (a.val.val (seamComplementSecond a.val)).val := a.property
  apply Fin.ext
  change (a.val.val (seamComplementFirst a.val)).val = 0
  by_contra hn
  have hap : 0 < (a.val.val (seamComplementFirst a.val)).val := by omega
  let D := a.val.val.toPerm.symm (seamLeft n m 0)
  have hD : a.val.val D = seamLeft n m 0 := a.val.val.toPerm.apply_symm_apply _
  have hDP : D ≠ seamComplementFirst a.val := by
    intro h
    have hv := congrArg Fin.val hD
    rw [h] at hv
    change (a.val.val (seamComplementFirst a.val)).val = 0 at hv
    omega
  have hDQ : D ≠ seamComplementSecond a.val := by
    intro h
    have hv := congrArg Fin.val hD
    rw [h] at hv
    change (a.val.val (seamComplementSecond a.val)).val = 0 at hv
    omega
  have hDn : D.val < n := by
    by_contra hh
    have hm : D ∈ seamSouthwestColumns a.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by rw [hD]; exact Nat.zero_le n⟩
    rw [seamComplement_southwest_eq_pair_of_card_two a.val hcard] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton, hDP, hDQ, or_self] at hm
  have hDA : D ≠ e.right := by
    intro h
    have hv := congrArg Fin.val hD
    rw [h] at hv
    change (a.val.val e.right).val = 0 at hv
    omega
  have hvSource : seamState p.1 p.2 D = a.val.val D := by
    have hh := e.map_of_ne D (by rwa [heL]) hDA
    rw [seamComplementPartner_firstBlock_apply a.val D hDn] at hh
    exact hh.symm
  by_cases hDA' : D.val < e.right.val
  · apply (isEmpty_iff_forall_notMem_cIoo e).mp he D
    · rw [Grid.mem_cIoo, heL, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr hDA'⟩
    · rw [hvSource, hD, heB, heT, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr hap⟩
  · have hAD : e.right.val < D.val := by
      have hh : D.val ≠ e.right.val := fun h => hDA (Fin.ext h)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo f).mp hf D
    · rw [Grid.mem_cIoo, hfL, hfR, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, hAD, by omega⟩
    · rw [bottom_def, top_def, hfL, hfR, hbC, hbPoint D hDn, hbPoint e.right heR,
        hD, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr hap⟩

/-- A low second-block point of a retained state is at the zero preimage of
its second factor. -/
theorem seamSecondOneStep_retained_zero_column (x : GridState (n + 1))
    (z : GridState (m + 1)) (C : Fin (n + m + 1)) (hCn : n ≤ C.val)
    (hCv : (seamState x z C).val ≤ n) : C = seamRight n m (z.toPerm.symm 0) := by
  let c := seamSecondFactorIndex C hCn
  have hC : seamRight n m c = C := seamRight_secondFactorIndex C hCn
  rw [← hC, seamState_secondFactorRow] at hCv
  have hz := seamSecondFactorRow_eq_zero_of_le x (z c) hCv
  have hc : c = z.toPerm.symm 0 := z.toPerm.eq_symm_apply.mpr hz
  rw [← hC, hc]

/-- The high-first entry pivot is the preimage of the maximal first-state row. -/
theorem seamSecondOneStep_high_first_pivot (p q : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) (heL : e.left.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementFirst a.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = C))
    (hfL : f.left = C) (hfR : f.right = e.left) :
    e.left = seamLeft n m (p.1.toPerm.symm (Fin.last n)) := by
  apply seamImmediateSecond_pivot_of_value p.1 p.2 e.left heL (Fin.last n)
  change e.bottom = _
  rw [(seamImmediateSecond_bottom_entry_rows p a e he heL).1,
    seamSecondOneStep_high_first_row_last p q a b e r f he hr hf heL C hCn hCv hsides hfL hfR]

/-- The high-second entry pivot is the preimage of the zero first-state row. -/
theorem seamSecondOneStep_high_second_pivot (p q : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) (heR : e.right.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementSecond a.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = C))
    (hfL : f.left = e.right) (hfR : f.right = C) :
    e.right = seamLeft n m (p.1.toPerm.symm 0) := by
  apply seamImmediateSecond_pivot_of_value p.1 p.2 e.right heR 0
  change e.top = _
  rw [(seamImmediateSecond_top_entry_rows p a e he heR).1,
    seamSecondOneStep_high_second_row_zero p q a b e r f he hr hf heR C hCn hCv hsides hfL hfR]

end OnLeConjecture.KnotFloer.GridFull
