/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepProjection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamRetainedSecondProjection

/-! # Fixed second factors in one-step seam corrections

The retained second factor fixes its zero-column position and every high
second-block row. These literal state values exclude exchanges with high
second-block points in a complete one-step correction.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem oneStep_retained_southwest_of_mem (p : SeamRetainedIndex n m)
    (c : Fin (n + m + 1)) (hc : c ∈ seamSouthwestColumns (seamState p.1 p.2)) :
    seamSouthwestColumns (seamState p.1 p.2) = {c} := by
  rw [seamState_southwest_singleton, Finset.mem_singleton] at hc
  rw [seamState_southwest_singleton, hc]

/-- The untouched southwest column is exactly the retained entry's zero-row column. -/
theorem seamOneStep_entry_zero_column (p : SeamRetainedIndex n m)
    (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : e.IsEmpty) :
    seamSouthwestColumns (seamState p.1 p.2) =
      {if e.left.val < n then seamComplementSecond x.val else seamComplementFirst x.val} := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  rcases seamMatchingEntry_endpoints p x e he with h | h
  · rw [if_pos h.1]
    apply oneStep_retained_southwest_of_mem
    apply (mem_seamSouthwestColumns _ _).mpr
    refine ⟨hq.1, ?_⟩
    have hh := e.map_of_ne (seamComplementSecond x.val)
      (by intro h'; have := congrArg Fin.val h'; omega)
      (by rw [h.2.1]; exact (seamComplementFirst_ne_second x.val).symm)
    rw [seamComplementPartner_apply_second] at hh
    rw [← hh]
    exact hp.2
  · have hnot : ¬ e.left.val < n := by rw [h.2.1]; omega
    rw [if_neg hnot]
    apply oneStep_retained_southwest_of_mem
    apply (mem_seamSouthwestColumns _ _).mpr
    refine ⟨hp.1, ?_⟩
    have hh := e.map_of_ne (seamComplementFirst x.val)
      (by rw [h.2.1]; exact seamComplementFirst_ne_second x.val)
      (by intro h'; have := congrArg Fin.val h'; omega)
    rw [seamComplementPartner_apply_first] at hh
    rw [← hh]
    exact hq.2

/-- The untouched southwest column is exactly the retained exit's zero-row column. -/
theorem seamOneStep_exit_zero_column (q : SeamRetainedIndex n m)
    (y : SeamMatchingSource n m)
    (f : GridRectangleBetween y.val.val (seamState q.1 q.2)) (hf : f.IsEmpty) :
    seamSouthwestColumns (seamState q.1 q.2) =
      {if f.left.val < n then seamComplementSecond y.val else seamComplementFirst y.val} := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem y.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem y.val)
  rcases seamMatchingExit_endpoints q y f hf with h | h
  · rw [if_pos h.1]
    apply oneStep_retained_southwest_of_mem
    apply (mem_seamSouthwestColumns _ _).mpr
    refine ⟨hq.1, ?_⟩
    rw [f.map_of_ne (seamComplementSecond y.val)
      (by intro h'; have := congrArg Fin.val h'; omega)
      (by rw [h.2.1]; exact (seamComplementFirst_ne_second y.val).symm)]
    exact hq.2
  · have hnot : ¬ f.left.val < n := by rw [h.2.1]; omega
    rw [if_neg hnot]
    apply oneStep_retained_southwest_of_mem
    apply (mem_seamSouthwestColumns _ _).mpr
    refine ⟨hp.1, ?_⟩
    rw [f.map_of_ne (seamComplementFirst y.val)
      (by rw [h.2.1]; exact seamComplementFirst_ne_second y.val)
      (by intro h'; have := congrArg Fin.val h'; omega)]
    exact hp.2

/-- Fixed second factor makes the two retained zero-column positions equal. -/
theorem seamOneStep_same_second_zero_column (u v : GridState (n + 1)) (z : GridState (m + 1))
    (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z)) (he : e.IsEmpty) (hf : f.IsEmpty) :
    (if e.left.val < n then seamComplementSecond x.val else seamComplementFirst x.val) =
      (if f.left.val < n then seamComplementSecond y.val else seamComplementFirst y.val) := by
  apply Finset.singleton_injective
  rw [← seamOneStep_entry_zero_column (u, z) x e he,
    ← seamOneStep_exit_zero_column (v, z) y f hf, seamState_southwest_singleton,
    seamState_southwest_singleton]

/-- A high second-block row is fixed literally when the second factor is fixed. -/
theorem seamOneStep_same_second_high_value (u v : GridState (n + 1))
    (z : GridState (m + 1)) (c : Fin (n + m + 1))
    (hcn : n ≤ c.val) (hcv : n < (seamState u z c).val) :
    seamState u z c = seamState v z c := by
  let d := seamSecondFactorIndex c hcn
  have hd : seamRight n m d = c := seamRight_secondFactorIndex c hcn
  have hz : z d ≠ 0 := by
    intro h
    have hh := (seamState_right_row_le_iff u z d).mpr h
    rw [hd] at hh
    omega
  rw [← hd, seamState_right_of_ne_zero u z d hz, seamState_right_of_ne_zero v z d hz]

/-- In a complete correction with fixed second factor, the first southwest
point cannot exchange with a high second-block point. -/
theorem seamOneStep_same_second_not_high_first
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (x.val.val C).val)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C)) : False := by
  obtain ⟨hL, hR, hQC, hYfirst, hYsecond, _, _⟩ :=
    seamOneStep_high_first r hr (seamMatchingEntry_southwest_card (u, z) x e) C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hPC : seamComplementFirst x.val < C := hpq.trans hQC
  have hmatch := seamOneStep_same_second_zero_column u v z x y e f he hf
  have heL : e.left.val < n := by
    by_contra hnot
    rw [if_neg hnot, hYfirst, hYsecond] at hmatch
    split_ifs at hmatch
    · have hh := congrArg Fin.val hmatch; omega
    · exact (seamComplementFirst_ne_second x.val) hmatch
  have hfL : ¬ f.left.val < n := by
    intro h
    rw [if_pos heL, if_pos h, hYsecond] at hmatch
    exact hQC.ne hmatch
  obtain ⟨heP, heTop, heHigh⟩ : e.right = seamComplementFirst x.val ∧
      e.top = x.val.val e.left ∧ n < e.top.val := by
    rcases seamMatchingEntry_endpoints (u, z) x e he with h | h
    · exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · have hh := congrArg Fin.val h.2.1
      omega
  obtain ⟨hfR, hfC⟩ : f.right.val < n ∧ f.left = C := by
    rcases seamMatchingExit_endpoints (v, z) y f hf with h | h
    · exact False.elim (hfL h.1)
    · exact ⟨h.1, h.2.1.trans hYsecond⟩
  have hvP : seamState u z (seamComplementFirst x.val) = x.val.val e.left := by
    calc
      _ = e.top := by rw [← heP]; rfl
      _ = _ := heTop
  have hpY : (seamComplementPartner y.val).val (seamComplementFirst x.val) =
      y.val.val (seamComplementFirst x.val) := by
    change y.val.val.swapColumns (seamComplementFirst y.val)
      (seamComplementSecond y.val) (seamComplementFirst x.val) = _
    rw [hYfirst, hYsecond, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hpq.ne hPC.ne]
  have hyP : y.val.val (seamComplementFirst x.val) = x.val.val C := by
    rw [← hpY, ← hR, r.map_right, hL]
  have hwP : seamState v z (seamComplementFirst x.val) = x.val.val C := by
    rw [f.map_of_ne (seamComplementFirst x.val)
      (by rw [hfC]; exact hPC.ne)
      (by intro h; have := congrArg Fin.val h; omega), hyP]
  have hfixed := seamOneStep_same_second_high_value u v z (seamComplementFirst x.val) hp.1
    (by rw [← heP]; exact heHigh)
  have hh : x.val.val e.left = x.val.val C := hvP.symm.trans (hfixed.trans hwP)
  have hc := congrArg Fin.val (x.val.val.toPerm.injective hh)
  omega

/-- In a complete correction with fixed second factor, the second southwest
point cannot exchange with a high second-block point. -/
theorem seamOneStep_same_second_not_high_second
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (x.val.val C).val)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C)) : False := by
  obtain ⟨hL, hR, hCP, hYfirst, hYsecond, _, _⟩ :=
    seamOneStep_high_second r hr (seamMatchingEntry_southwest_card (u, z) x e) C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hCQ : C < seamComplementSecond x.val := hCP.trans hpq
  have hmatch := seamOneStep_same_second_zero_column u v z x y e f he hf
  have heL : ¬ e.left.val < n := by
    intro h
    rw [if_pos h, hYfirst, hYsecond] at hmatch
    split_ifs at hmatch
    · exact (seamComplementFirst_ne_second x.val).symm hmatch
    · have hh := congrArg Fin.val hmatch; omega
  have hfL : f.left.val < n := by
    by_contra h
    rw [if_neg heL, if_neg h, hYfirst] at hmatch
    exact hCP.ne hmatch.symm
  obtain ⟨heR, heQ, heBot, heHigh⟩ : e.right.val < n ∧
      e.left = seamComplementSecond x.val ∧
      e.bottom = x.val.val e.right ∧ n < e.bottom.val := by
    rcases seamMatchingEntry_endpoints (u, z) x e he with h | h
    · exact False.elim (heL h.1)
    · exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hfC : f.right = C :=
    (seamMatchingExit_right_eq_first_of_left_lt (v, z) y f hf hfL).trans hYfirst
  have hvQ : seamState u z (seamComplementSecond x.val) = x.val.val e.right := by
    calc
      _ = e.bottom := by rw [← heQ]; rfl
      _ = _ := heBot
  have hpY : (seamComplementPartner y.val).val (seamComplementSecond x.val) =
      y.val.val (seamComplementSecond x.val) := by
    change y.val.val.swapColumns (seamComplementFirst y.val)
      (seamComplementSecond y.val) (seamComplementSecond x.val) = _
    rw [hYfirst, hYsecond, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCQ.ne.symm hpq.ne.symm]
  have hyQ : y.val.val (seamComplementSecond x.val) = x.val.val C := by
    rw [← hpY, ← hL, r.map_left, hR]
  have hwQ : seamState v z (seamComplementSecond x.val) = x.val.val C := by
    rw [f.map_of_ne (seamComplementSecond x.val)
      (by intro h; have := congrArg Fin.val h; omega)
      (by rw [hfC]; exact hCQ.ne.symm), hyQ]
  have hfixed := seamOneStep_same_second_high_value u v z (seamComplementSecond x.val) hq.1
    (by rw [← heQ]; exact heHigh)
  have hh : x.val.val e.right = x.val.val C := hvQ.symm.trans (hfixed.trans hwQ)
  have hc := congrArg Fin.val (x.val.val.toPerm.injective hh)
  omega

/-- Every one-step correction with fixed second factor exchanges a low first-block point. -/
theorem seamFirstFactorOneStep_internal_low
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (hne : x ≠ y) (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) :
    ∃ C : Fin (n + m + 1), C.val < n ∧ (x.val.val C).val ≤ n ∧
      ((r.left = C ∧ r.right = seamComplementFirst x.val) ∨
        (r.left = seamComplementSecond x.val ∧ r.right = C)) := by
  obtain ⟨S, C, hS, hsides, hC⟩ :=
    seamFirstFactorOneStep_internal_sides (u, z) (v, z) x y e r f hne
  rcases hC with ⟨hCn, hCv⟩ | ⟨hCn, hCv⟩
  · refine ⟨C, hCn, hCv, ?_⟩
    rcases hS with rfl | rfl
    · have hh := seamOneStep_low_first r hr C hCn hCv hsides
      exact Or.inl ⟨hh.1, hh.2.1⟩
    · have hh := seamOneStep_low_second r hr C hCn hCv hsides
      exact Or.inr ⟨hh.1, hh.2.1⟩
  · exfalso
    rcases hS with rfl | rfl
    · exact seamOneStep_same_second_not_high_first u v z x y e r f he hr hf C hCn hCv hsides
    · exact seamOneStep_same_second_not_high_second u v z x y e r f he hr hf C hCn hCv hsides

private theorem oneStep_northeast_eq_of_low_rows {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hb : r.bottom.val ≤ n) (ht : r.top.val ≤ n) :
    seamNortheastColumns x.val.val = seamNortheastColumns y.val.val := by
  rw [← seamComplementPartner_northeastColumns y.val, r.target_eq_swapColumns]
  ext c
  simp only [mem_seamNortheastColumns, GridState.swapColumns_apply]
  by_cases hcl : c = r.left
  · subst c
    simp only [Equiv.swap_apply_left]
    change (_ ∧ n < r.bottom.val) ↔ (_ ∧ n < r.top.val)
    omega
  by_cases hcr : c = r.right
  · subst c
    simp only [Equiv.swap_apply_right]
    change (_ ∧ n < r.top.val) ↔ (_ ∧ n < r.bottom.val)
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hcl hcr]

/-- Low-row internal exchanges retain the unique northeast entry/exit column. -/
theorem seamOneStep_low_entry_exit_column (p q : SeamRetainedIndex n m)
    (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState q.1 q.2))
    (hb : r.bottom.val ≤ n) (ht : r.top.val ≤ n) :
    (if e.left.val < n then e.left else e.right) =
      (if f.left.val < n then f.left else f.right) := by
  have hh := (seamMatchingEntry_northeast_eq_singleton p x e).symm.trans
    ((oneStep_northeast_eq_of_low_rows r hb ht).trans
      (seamMatchingExit_northeast_eq_singleton q y f))
  exact Finset.singleton_injective hh

/-- A high first-block point is unchanged by a low-row internal rectangle. -/
theorem seamOneStep_low_high_point {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hb : r.bottom.val ≤ n) (ht : r.top.val ≤ n)
    (A : Fin (n + m + 1)) (hAn : A.val < n) (hAv : n < (x.val.val A).val) :
    y.val.val A = x.val.val A := by
  have hAl : A ≠ r.left := by intro h; rw [h] at hAv; change n < r.bottom.val at hAv; omega
  have hAr : A ≠ r.right := by intro h; rw [h] at hAv; change n < r.top.val at hAv; omega
  have hh := r.map_of_ne A hAl hAr
  rwa [seamComplementPartner_firstBlock_apply y.val A hAn] at hh

/-- The first-southwest low exchange can occur in a complete fixed-second
correction only with both entry and exit wrapping toward the same earlier column. -/
theorem seamOneStep_same_second_low_first_orientations
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C)) :
    e.right.val < n ∧ f.right.val < n ∧ e.right = f.right ∧ e.right < C := by
  obtain ⟨hrL, hrR, hrow, hYfirst, hYsecond, hyP, hyQ, hyC⟩ :=
    seamOneStep_low_first r hr C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hbot : r.bottom.val ≤ n := by simpa only [bottom_def, hrL] using hCv
  have htop : r.top.val ≤ n := by simpa only [top_def, hrR] using hp.2
  let A := if e.left.val < n then e.left else e.right
  have hAm : A ∈ seamNortheastColumns x.val.val := by
    rw [seamMatchingEntry_northeast_eq_singleton (u, z) x e]
    exact Finset.mem_singleton_self _
  obtain ⟨hAn, hAv⟩ := (mem_seamNortheastColumns _ _).mp hAm
  have hyA := seamOneStep_low_high_point r hbot htop A hAn hAv
  have hAeq := seamOneStep_low_entry_exit_column (u, z) (v, z) x y e r f hbot htop
  change A = _ at hAeq
  have hAC : A < C := by
    by_contra h
    have hne : A ≠ C := by intro hh; rw [hh] at hAv; omega
    have hCA : C.val < A.val := by
      have hn : A.val ≠ C.val := fun hh => hne (Fin.ext hh)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo r).mp hr A
    · rw [Grid.mem_cIoo, hrL, hrR, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hCA, by omega⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩
  have hzero := seamOneStep_same_second_zero_column u v z x y e f he hf
  rw [hYfirst, hYsecond] at hzero
  have heNot : ¬ e.left.val < n := by
    intro heL
    have hfL : f.left.val < n := by
      by_contra h
      rw [if_pos heL, if_neg h] at hzero
      exact (seamComplementFirst_ne_second x.val).symm hzero
    have hfA : f.left = A := by rw [if_pos hfL] at hAeq; exact hAeq.symm
    have hfP : f.right = seamComplementFirst x.val :=
      (seamMatchingExit_right_eq_first_of_left_lt (v, z) y f hf hfL).trans hYfirst
    apply (isEmpty_iff_forall_notMem_cIoo f).mp hf C
    · rw [Grid.mem_cIoo, hfA, hfP, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hAC, by omega⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hfA, hfP, hyA, hyP, hyC, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hsource⟩
  have hfNot : ¬ f.left.val < n := by
    intro h
    rw [if_neg heNot, if_pos h] at hzero
    exact (seamComplementFirst_ne_second x.val) hzero
  have heR : e.right.val < n := by
    rcases seamMatchingEntry_endpoints (u, z) x e he with h | h
    · exact False.elim (heNot h.1)
    · exact h.1
  have hfR : f.right.val < n := by
    rcases seamMatchingExit_endpoints (v, z) y f hf with h | h
    · exact False.elim (hfNot h.1)
    · exact h.1
  have hAe : A = e.right := by simp only [A, if_neg heNot]
  rw [if_neg hfNot] at hAeq
  exact ⟨heR, hfR, hAe.symm.trans hAeq, hAe ▸ hAC⟩

/-- The second-southwest low exchange can occur in a complete fixed-second
correction only with both entry and exit starting at the same later column. -/
theorem seamOneStep_same_second_low_second_orientations
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C)) :
    e.left.val < n ∧ f.left.val < n ∧ e.left = f.left ∧ C < e.left := by
  obtain ⟨hrL, hrR, hrow, hYfirst, hYsecond, hyP, hyQ, hyC⟩ :=
    seamOneStep_low_second r hr C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hbot : r.bottom.val ≤ n := by simpa only [bottom_def, hrL] using hq.2
  have htop : r.top.val ≤ n := by simpa only [top_def, hrR] using hCv
  let A := if e.left.val < n then e.left else e.right
  have hAm : A ∈ seamNortheastColumns x.val.val := by
    rw [seamMatchingEntry_northeast_eq_singleton (u, z) x e]
    exact Finset.mem_singleton_self _
  obtain ⟨hAn, hAv⟩ := (mem_seamNortheastColumns _ _).mp hAm
  have hyA := seamOneStep_low_high_point r hbot htop A hAn hAv
  have hAeq := seamOneStep_low_entry_exit_column (u, z) (v, z) x y e r f hbot htop
  change A = _ at hAeq
  have hCA : C < A := by
    by_contra h
    have hne : A ≠ C := by intro hh; rw [hh] at hAv; omega
    have hAC : A.val < C.val := by
      have hn : A.val ≠ C.val := fun hh => hne (Fin.ext hh)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo r).mp hr A
    · rw [Grid.mem_cIoo, hrL, hrR, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hAC⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩
  have hzero := seamOneStep_same_second_zero_column u v z x y e f he hf
  rw [hYfirst, hYsecond] at hzero
  have heL : e.left.val < n := by
    by_contra heNot
    have hfNot : ¬ f.left.val < n := by
      intro h
      rw [if_neg heNot, if_pos h] at hzero
      exact (seamComplementFirst_ne_second x.val) hzero
    have hfA : f.right = A := by rw [if_neg hfNot] at hAeq; exact hAeq.symm
    have hfR : f.right.val < n := by
      rcases seamMatchingExit_endpoints (v, z) y f hf with h | h
      · exact False.elim (hfNot h.1)
      · exact h.1
    have hfQ : f.left = seamComplementSecond x.val :=
      (seamMatchingExit_left_eq_second_of_right_lt (v, z) y f hf hfR).trans hYsecond
    apply (isEmpty_iff_forall_notMem_cIoo f).mp hf C
    · rw [Grid.mem_cIoo, hfQ, hfA, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hCA⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hfQ, hfA, hyA, hyQ, hyC, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hsource, by omega⟩
  have hfL : f.left.val < n := by
    by_contra h
    rw [if_pos heL, if_neg h] at hzero
    exact (seamComplementFirst_ne_second x.val).symm hzero
  have hAe : A = e.left := by simp only [A, if_pos heL]
  rw [if_pos hfL] at hAeq
  exact ⟨heL, hfL, hAe.symm.trans hAeq, hAe ▸ hCA⟩

/-- The two surviving orientation and order alternatives are derived from
an actual complete one-step correction with fixed second factor. -/
theorem seamFirstFactorOneStep_orientations
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (hne : x ≠ y) (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) :
    ∃ C : Fin (n + m + 1), C.val < n ∧ (x.val.val C).val ≤ n ∧
      ((r.left = C ∧ r.right = seamComplementFirst x.val ∧
          e.right.val < n ∧ f.right.val < n ∧ e.right = f.right ∧ e.right < C) ∨
        (r.left = seamComplementSecond x.val ∧ r.right = C ∧
          e.left.val < n ∧ f.left.val < n ∧ e.left = f.left ∧ C < e.left)) := by
  obtain ⟨C, hCn, hCv, hsides⟩ :=
    seamFirstFactorOneStep_internal_low u v z x y e r f hne he hr hf
  refine ⟨C, hCn, hCv, ?_⟩
  rcases hsides with h | h
  · exact Or.inl ⟨h.1, h.2,
      seamOneStep_same_second_low_first_orientations u v z x y e r f he hr hf
        C hCn hCv (Or.inr ⟨h.2, h.1⟩)⟩
  · exact Or.inr ⟨h.1, h.2,
      seamOneStep_same_second_low_second_orientations u v z x y e r f he hr hf
        C hCn hCv (Or.inl h)⟩

end OnLeConjecture.KnotFloer.GridFull
