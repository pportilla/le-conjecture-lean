/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamBirthDeathGeneral
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepProjection

/-! # Restrictions on a birth followed by a neutral step and a death

The middle states have three southwest points. The first row created by a
birth lies below the third row. This order is used with actual rectangle maps
and the necessary row order for the subsequent death.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- Immediately after a birth, the first southwest row is below the third one. -/
theorem seamMatchingBirth_first_lt_third (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hthree : 3 ≤ (seamSouthwestColumns y.val.val).card) :
    (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementThird y.val hthree)).val := by
  rw [seamMatchingBirth_third_row x y r he hb hthree]
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  rcases seamMatchingBirth_endpoints x y r he hb with h | h
  · rw [h.2.2.2.2.2.2.1]
    exact hsource
  · have hrow := h.2.2.2.2.2.2.2.2.1
    omega

/-- The three selected columns exhaust a southwest set of cardinality three. -/
theorem seamComplement_southwest_eq_triple_of_card_three (x : SeamComplement n m)
    (hcard : (seamSouthwestColumns x.val).card = 3) :
    seamSouthwestColumns x.val =
      {seamComplementFirst x, seamComplementSecond x, seamComplementThird x (by omega)} := by
  classical
  have hpq := seamComplementFirst_lt_second x
  have hqr := seamComplementSecond_lt_third x (by omega)
  have hpr := hpq.trans hqr
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact seamComplementFirst_mem x
    · exact seamComplementSecond_mem x
    · exact seamComplementThird_mem x _
  · simp only [hcard, Finset.card_insert_of_notMem,
      Finset.mem_insert, Finset.mem_singleton, hpq.ne, hpr.ne, hqr.ne,
      or_self, not_false_eq_true, Finset.card_singleton]
    omega

/-- A rectangle exchanging two low rows preserves the whole southwest column set. -/
theorem seamPlateau_low_southwest_eq {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hb : r.bottom.val ≤ n) (ht : r.top.val ≤ n) :
    seamSouthwestColumns y.val.val = seamSouthwestColumns x.val.val := by
  rw [← seamComplementPartner_southwestColumns y.val, r.target_eq_swapColumns]
  ext c
  simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply]
  by_cases hcl : c = r.left
  · subst c
    simp only [Equiv.swap_apply_left]
    change (_ ∧ r.top.val ≤ n) ↔ (_ ∧ r.bottom.val ≤ n)
    omega
  by_cases hcr : c = r.right
  · subst c
    simp only [Equiv.swap_apply_right]
    change (_ ∧ r.bottom.val ≤ n) ↔ (_ ∧ r.top.val ≤ n)
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hcl hcr]

/-- A low exchange at the second southwest column cannot occur between a birth and a death. -/
theorem seamPeakPlateau_low_second_impossible (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (b.val.val C).val ≤ n)
    (hsides : (t.left = seamComplementSecond b.val ∧ t.right = C) ∨
      (t.right = seamComplementSecond b.val ∧ t.left = C)) : False := by
  obtain ⟨htL, htR, hlow, hP, hQ, hyP, hyQ, _⟩ := seamOneStep_low_second t ht C hCn hCv hsides
  have hbp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  have hbq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem b.val)
  have hSW := seamPlateau_low_southwest_eq t
    (by simpa only [bottom_def, htL] using hbq.2)
    (by simpa only [top_def, htR] using hCv)
  let h3c := seamMatchingDeath_three_le_southwest c d hd
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by rwa [hSW] at h3c
  have hR : seamComplementThird c.val h3c = seamComplementThird b.val h3b := by
    unfold seamComplementThird
    congr 1
    rw [hSW, hP, hQ]
  have hRy : c.val.val (seamComplementThird c.val h3c) =
      b.val.val (seamComplementThird b.val h3b) := by
    rw [hR]
    have hRp := (seamComplementFirst_lt_third b.val h3b).ne.symm
    have hRq := (seamComplementSecond_lt_third b.val h3b).ne.symm
    have hRn := ((mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem b.val h3b)).1
    have hh := t.map_of_ne (seamComplementThird b.val h3b)
      (by rwa [htL]) (by rw [htR]; intro h; have := congrArg Fin.val h; omega)
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) _ = _ at hh
    simpa only [hP, hQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hRp hRq] using hh
  have hbirth := seamMatchingBirth_first_lt_third a b r hr hb h3b
  rcases seamMatchingDeath_endpoints c d u hu hd with h | h
  · have hdeath := h.2.2.2.2.2.2.2.2.2
    rw [hRy, hQ, hyQ] at hdeath
    omega
  · have hdeath := h.2.2.2.2.2.2.2.2.2
    rw [hRy, hP, hyP] at hdeath
    omega


private theorem plateau_first_congr (x y : SeamComplement n m)
    (h : seamSouthwestColumns x.val = seamSouthwestColumns y.val) :
    seamComplementFirst x = seamComplementFirst y := by
  unfold seamComplementFirst
  congr 1

private theorem plateau_second_congr (x y : SeamComplement n m)
    (h : seamSouthwestColumns x.val = seamSouthwestColumns y.val) :
    seamComplementSecond x = seamComplementSecond y := by
  unfold seamComplementSecond
  congr 1
  rw [h, plateau_first_congr x y h]

/-- A neutral internal rectangle has at least one southwest endpoint, at any southwest count. -/
theorem seamPlateau_neutral_touches_southwest {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hcard : (seamSouthwestColumns x.val.val).card = (seamSouthwestColumns y.val.val).card) :
    r.left ∈ seamSouthwestColumns x.val.val ∨ r.right ∈ seamSouthwestColumns x.val.val := by
  classical
  by_contra h
  obtain ⟨hl, hr⟩ := not_or.mp h
  have hsub : seamSouthwestColumns x.val.val ⊆ seamSouthwestColumns y.val.val := by
    intro c hc
    have hcL : c ≠ r.left := fun hh => hl (hh ▸ hc)
    have hcR : c ≠ r.right := fun hh => hr (hh ▸ hc)
    obtain ⟨hcn, hcv⟩ := (mem_seamSouthwestColumns _ _).mp hc
    rw [← seamComplementPartner_southwestColumns]
    exact (mem_seamSouthwestColumns _ _).mpr ⟨hcn, by rwa [r.map_of_ne c hcL hcR]⟩
  have hsets := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hP := plateau_first_congr x.val y.val hsets
  have hQ := plateau_second_congr x.val y.val hsets
  have hp := r.map_of_ne (seamComplementFirst x.val)
    (fun hh => hl (hh ▸ seamComplementFirst_mem x.val))
    (fun hh => hr (hh ▸ seamComplementFirst_mem x.val))
  have hq := r.map_of_ne (seamComplementSecond x.val)
    (fun hh => hl (hh ▸ seamComplementSecond_mem x.val))
    (fun hh => hr (hh ▸ seamComplementSecond_mem x.val))
  rw [hP, seamComplementPartner_apply_first] at hp
  rw [hQ, seamComplementPartner_apply_second] at hq
  have hx : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hy : (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementSecond y.val)).val := y.property
  rw [hP, hQ] at hx
  have hpv := congrArg Fin.val hp
  have hqv := congrArg Fin.val hq
  omega

/-- With three southwest points and the first row below the third row, an empty
nonmatching internal rectangle cannot exchange two southwest points. -/
theorem seamPlateau_not_both_southwest {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hne : x ≠ y) (he : r.IsEmpty)
    (hcard : (seamSouthwestColumns x.val.val).card = 3)
    (hrow : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementThird x.val (by omega))).val) :
    ¬ (r.left ∈ seamSouthwestColumns x.val.val ∧ r.right ∈ seamSouthwestColumns x.val.val) := by
  classical
  rintro ⟨hl, hr⟩
  have hlrow := ((mem_seamSouthwestColumns _ _).mp hl).2
  have hrrow := ((mem_seamSouthwestColumns _ _).mp hr).2
  have hsets := seamPlateau_low_southwest_eq r hlrow hrrow
  have hP := plateau_first_congr y.val x.val hsets
  have hQ := plateau_second_congr y.val x.val hsets
  have hy := seamMatchingTarget_first_gt_second y
  rw [hP, hQ] at hy
  have hpq := seamComplementFirst_lt_second x.val
  have hqr := seamComplementSecond_lt_third x.val (by omega)
  have hpr := hpq.trans hqr
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hnot := seamOneStep_internal_not_matching_sides hne r
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hR := (mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem x.val (by omega))
  rw [seamComplement_southwest_eq_triple_of_card_three x.val hcard] at hl hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl hr
  rcases hl with hLP | hLQ | hLR <;> rcases hr with hRP | hRQ | hRR
  · exact r.left_ne_right (hLP.trans hRP.symm)
  · exact hnot (Or.inl ⟨hLP, hRQ⟩)
  · have hmapP := r.map_left
    have hmapQ := r.map_of_ne (seamComplementSecond x.val)
      (by rw [hLP]; exact hpq.ne.symm) (by rw [hRR]; exact hqr.ne)
    rw [hLP, hRR] at hmapP
    rw [hmapP, hmapQ] at hy
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he (seamComplementSecond x.val)
    · rw [Grid.mem_cIoo, hLP, hRR, if_pos (show (seamComplementFirst x.val).val <
        (seamComplementThird x.val (by omega)).val from hpr)]
      exact ⟨hpr.ne, hpq, hqr⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hLP, hRR, if_pos hrow]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hsource, hy⟩
  · exact hnot (Or.inr ⟨hRP, hLQ⟩)
  · exact r.left_ne_right (hLQ.trans hRQ.symm)
  · have hmapP := r.map_of_ne (seamComplementFirst x.val)
      (by rw [hLQ]; exact hpq.ne) (by rw [hRR]; exact hpr.ne)
    have hmapQ := r.map_left
    rw [hLQ, hRR] at hmapQ
    rw [hmapP, hmapQ] at hy
    omega
  · obtain ⟨A, hA⟩ := (seamNortheastColumns_nonempty_iff x.val.val).mpr x.val.property
    obtain ⟨hAn, hAv⟩ := (mem_seamNortheastColumns _ _).mp hA
    apply (isEmpty_iff_forall_notMem_cIoo r).mp he A
    · rw [Grid.mem_cIoo, hLR, hRP, if_neg (by omega)]
      exact ⟨hpr.ne.symm, Or.inr (by omega)⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hLR, hRP, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩
  · have hmapP := r.map_of_ne (seamComplementFirst x.val)
      (by rw [hLR]; exact hpr.ne) (by rw [hRQ]; exact hpq.ne)
    have hmapQ := r.map_right
    rw [hLR, hRQ] at hmapQ
    rw [hmapP, hmapQ] at hy
    omega
  · exact r.left_ne_right (hLR.trans hRR.symm)

/-- A low exchange at the first southwest column cannot follow a nonwrapping birth. -/
theorem seamPeakPlateau_low_first_after_nonwrap_birth_false
    (a b c : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hrL : r.left.val < n)
    (D : Fin (n + m + 1)) (hDn : D.val < n) (hDv : (b.val.val D).val ≤ n)
    (hsides : (t.left = seamComplementFirst b.val ∧ t.right = D) ∨
      (t.right = seamComplementFirst b.val ∧ t.left = D)) : False := by
  obtain ⟨htL, htR, hlow, hP, hQ, hyP, hyQ, hyD⟩ :=
    seamOneStep_low_first t ht D hDn hDv hsides
  rcases seamMatchingBirth_endpoints a b r hr hb with hh | hh
  swap
  · have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)).1
    have hc := hh.2.1
    omega
  obtain ⟨_, hrR, hcp, hs, hf, hsecond, hbP, hbQ, hhigh⟩ := hh
  have hE : b.val.val r.left = r.top := by
    have hh := r.map_left
    rwa [seamComplementPartner_firstBlock_apply b.val r.left hrL] at hh
  have hDE : D ≠ r.left := by intro hh; rw [hh, hE] at hDv; omega
  have hDP : D ≠ r.right := by intro hh; have := congrArg Fin.val hh; omega
  have haD : a.val.val D = b.val.val D := by
    have hh := r.map_of_ne D hDE hDP
    rw [seamComplementPartner_firstBlock_apply b.val D hDn] at hh
    exact hh.symm
  have hED : r.left.val < D.val := by
    by_contra hn
    have hdE : D.val < r.left.val := by
      have hne : D.val ≠ r.left.val := fun hh => hDE (Fin.ext hh)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo t).mp ht r.left
    · rw [Grid.mem_cIoo, htL, htR, hf, if_pos (by omega)]
      exact ⟨hDP, hdE, by omega⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, htL, htR, if_neg (by
        have hh : (b.val.val (seamComplementFirst b.val)).val <
          (b.val.val (seamComplementSecond b.val)).val := b.property
        omega)]
      refine ⟨?_, Or.inl ?_⟩
      · intro hh; have := congrArg Fin.val hh
        have hh' : (b.val.val (seamComplementFirst b.val)).val <
          (b.val.val (seamComplementSecond b.val)).val := b.property
        omega
      · rw [hE]; omega
  apply (isEmpty_iff_forall_notMem_cIoo r).mp hr D
  · rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨r.left_ne_right, hED, by omega⟩
  · rw [Grid.mem_cIoo, if_pos (by rw [← hbQ]; omega)]
    rw [haD]
    exact ⟨r.bottom_ne_top, by rwa [← hbQ], by omega⟩

/-- A low exchange at the first southwest column cannot precede a nonwrapping death. -/
theorem seamPeakPlateau_low_first_before_nonwrap_death_false
    (b c d : SeamMatchingSource n m)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (ht : t.IsEmpty) (hu : u.IsEmpty)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (huL : u.left.val < n)
    (D : Fin (n + m + 1)) (hDn : D.val < n) (hDv : (b.val.val D).val ≤ n)
    (hsides : (t.left = seamComplementFirst b.val ∧ t.right = D) ∨
      (t.right = seamComplementFirst b.val ∧ t.left = D)) : False := by
  obtain ⟨htL, htR, hlow, hP, hQ, hyP, hyQ, hyD⟩ :=
    seamOneStep_low_first t ht D hDn hDv hsides
  obtain ⟨huR, _, _, _, _, _, _⟩ := seamMatchingDeath_nonwrap c d u hu hd huL
  have hcP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem c.val)
  have hbP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  have hbQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem b.val)
  have hhigh : n < (c.val.val u.left).val := by
    rcases seamMatchingDeath_ranges u hd with hh | hh
    · exact hh.2.2.2
    · omega
  have hDE : D ≠ u.left := by intro hh; rw [← hh, hyD] at hhigh; omega
  have hEP : u.left ≠ seamComplementFirst b.val := by
    intro hh; have := congrArg Fin.val hh; omega
  have hE : b.val.val u.left = c.val.val u.left := by
    have hh := t.map_of_ne u.left (by rw [htL]; exact hDE.symm) (by rwa [htR])
    rw [seamComplementPartner_firstBlock_apply c.val u.left huL] at hh
    exact hh.symm
  have hsource : (b.val.val (seamComplementFirst b.val)).val <
      (b.val.val (seamComplementSecond b.val)).val := b.property
  have hED : u.left.val < D.val := by
    by_contra hn
    have hdE : D.val < u.left.val := by
      have hne : D.val ≠ u.left.val := fun hh => hDE (Fin.ext hh)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo t).mp ht u.left
    · rw [Grid.mem_cIoo, htL, htR, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hdE, by omega⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, htL, htR, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by rw [hE]; omega)⟩
  apply (isEmpty_iff_forall_notMem_cIoo u).mp hu D
  · rw [Grid.mem_cIoo, huR, if_pos (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hED, by omega⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, huR, hP, hyP, hyD, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hsource⟩

/-- A low exchange at the first southwest column cannot occur between a birth and a death. -/
theorem seamPeakPlateau_low_first_impossible (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (D : Fin (n + m + 1)) (hDn : D.val < n) (hDv : (b.val.val D).val ≤ n)
    (hsides : (t.left = seamComplementFirst b.val ∧ t.right = D) ∨
      (t.right = seamComplementFirst b.val ∧ t.left = D)) : False := by
  rcases seamMatchingBirth_endpoints a b r hr hb with hB | hB
  · exact seamPeakPlateau_low_first_after_nonwrap_birth_false a b c r t hr ht hb
      hB.1 D hDn hDv hsides
  rcases seamMatchingDeath_endpoints c d u hu hd with hD | hD
  · exact seamPeakPlateau_low_first_before_nonwrap_death_false b c d t u ht hu hd
      hD.1 D hDn hDv hsides
  obtain ⟨htL, htR, _, hP, hQ, hyP, _, _⟩ := seamOneStep_low_first t ht D hDn hDv hsides
  have hbp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  have hSW := seamPlateau_low_southwest_eq t
    (by simpa only [bottom_def, htL] using hDv)
    (by simpa only [top_def, htR] using hbp.2)
  let h3c := seamMatchingDeath_three_le_southwest c d hd
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by rwa [hSW] at h3c
  have hR : seamComplementThird c.val h3c = seamComplementThird b.val h3b := by
    unfold seamComplementThird
    congr 1
    rw [hSW, hP, hQ]
  have hRy : c.val.val (seamComplementThird c.val h3c) =
      b.val.val (seamComplementThird b.val h3b) := by
    rw [hR]
    have hRp := (seamComplementFirst_lt_third b.val h3b).ne.symm
    have hRq := (seamComplementSecond_lt_third b.val h3b).ne.symm
    have hRn := ((mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem b.val h3b)).1
    have hh := t.map_of_ne (seamComplementThird b.val h3b)
      (by rw [htL]; intro h; have := congrArg Fin.val h; omega) (by rwa [htR])
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) _ = _ at hh
    simpa only [hP, hQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hRp hRq] using hh
  have hdeath := hD.2.2.2.2.2.2.2.2.2
  rw [hRy, seamMatchingBirth_third_row a b r hr hb h3b, hP, hyP,
    hB.2.2.2.2.2.2.2.1] at hdeath
  have ha : (a.val.val (seamComplementFirst a.val)).val <
      (a.val.val (seamComplementSecond a.val)).val := a.property
  omega

/-- An endpoint outside the southwest set of a neutral rectangle is low in the
first block or high in the second block. No southwest cardinality is prescribed. -/
theorem seamPlateau_internal_other_ranges {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hcard : (seamSouthwestColumns x.val.val).card = (seamSouthwestColumns y.val.val).card)
    (S D : Fin (n + m + 1)) (hS : S ∈ seamSouthwestColumns x.val.val)
    (hD : D ∉ seamSouthwestColumns x.val.val)
    (hsides : (r.left = S ∧ r.right = D) ∨ (r.right = S ∧ r.left = D)) :
    (D.val < n ∧ (x.val.val D).val ≤ n) ∨
      (n ≤ D.val ∧ n < (x.val.val D).val) := by
  obtain ⟨hSn, hSv⟩ := (mem_seamSouthwestColumns _ _).mp hS
  by_cases hdn : D.val < n
  · left
    refine ⟨hdn, ?_⟩
    by_contra hv
    have hdv : n < (x.val.val D).val := by omega
    have heq : seamSouthwestColumns (seamComplementPartner y.val).val =
        (seamSouthwestColumns x.val.val).erase S := by
      rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · have hh := seamRectangle_death_southwest_erase_left r
          (by rw [hr]; exact hdn) (by rw [hl]; exact hSn)
          (by change n < (x.val.val r.right).val; rwa [hr])
          (by change (x.val.val r.left).val ≤ n; rwa [hl])
        simpa only [hl] using hh
      · have hh := seamRectangle_death_southwest_erase_right r
          (by rw [hl]; exact hdn) (by rw [hr]; exact hSn)
          (by change n < (x.val.val r.left).val; rwa [hl])
          (by change (x.val.val r.right).val ≤ n; rwa [hr])
        simpa only [hr] using hh
    have hh := congrArg Finset.card heq
    rw [seamComplementPartner_southwestColumns, Finset.card_erase_of_mem hS, hcard] at hh
    have hpos := two_le_seamSouthwestColumns_card y.val.val y.val.property
    omega
  · right
    refine ⟨by omega, ?_⟩
    simp only [mem_seamSouthwestColumns, not_and_or] at hD
    omega

/-- A low exchange at the third southwest point cannot give a matching source. -/
theorem seamPlateau_low_third_false {b c : SeamMatchingSource n m}
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (hthree : 3 ≤ (seamSouthwestColumns b.val.val).card)
    (D : Fin (n + m + 1)) (hDn : D.val < n) (hDv : (b.val.val D).val ≤ n)
    (hsides : (t.left = seamComplementThird b.val hthree ∧ t.right = D) ∨
      (t.right = seamComplementThird b.val hthree ∧ t.left = D)) : False := by
  have hR := (mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem b.val hthree)
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem b.val)
  have hPR := seamComplementFirst_lt_third b.val hthree
  have hQR := seamComplementSecond_lt_third b.val hthree
  have hPD : seamComplementFirst b.val ≠ D := by intro h; have := congrArg Fin.val h; omega
  have hQD : seamComplementSecond b.val ≠ D := by intro h; have := congrArg Fin.val h; omega
  have hrows : t.bottom.val ≤ n ∧ t.top.val ≤ n := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩ <;>
      simp only [bottom_def, top_def, hl, hr] <;> omega
  have hSW := seamPlateau_low_southwest_eq t hrows.1 hrows.2
  have hfirst := plateau_first_congr c.val b.val hSW
  have hsecond := plateau_second_congr c.val b.val hSW
  have hmapP := t.map_of_ne (seamComplementFirst b.val)
    (by
      rcases hsides with ⟨hl, _⟩ | ⟨_, hl⟩
      · rw [hl]; exact hPR.ne
      · rw [hl]; exact hPD)
    (by
      rcases hsides with ⟨_, hr⟩ | ⟨hr, _⟩
      · rw [hr]; exact hPD
      · rw [hr]; exact hPR.ne)
  have hmapQ := t.map_of_ne (seamComplementSecond b.val)
    (by
      rcases hsides with ⟨hl, _⟩ | ⟨_, hl⟩
      · rw [hl]; exact hQR.ne
      · rw [hl]; exact hQD)
    (by
      rcases hsides with ⟨_, hr⟩ | ⟨hr, _⟩
      · rw [hr]; exact hQD
      · rw [hr]; exact hQR.ne)
  have hdesc := seamMatchingTarget_first_gt_second c
  rw [hfirst, hsecond, hmapP, hmapQ] at hdesc
  have hb : (b.val.val (seamComplementFirst b.val)).val <
      (b.val.val (seamComplementSecond b.val)).val := b.property
  omega

/-- Between a birth and a death at southwest count three, the neutral rectangle
exchanges exactly one southwest point with a high second-block point. -/
theorem seamPeakPlateau_middle_high (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty) (hne : b ≠ c)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (hcard : (seamSouthwestColumns b.val.val).card = 3)
    (hcard' : (seamSouthwestColumns c.val.val).card = 3) :
    ∃ S D : Fin (n + m + 1),
      (S = seamComplementFirst b.val ∨ S = seamComplementSecond b.val ∨
        S = seamComplementThird b.val (by omega)) ∧
      n ≤ D.val ∧ n < (b.val.val D).val ∧
      ((t.left = S ∧ t.right = D) ∨ (t.right = S ∧ t.left = D)) := by
  have heq : (seamSouthwestColumns b.val.val).card = (seamSouthwestColumns c.val.val).card :=
    hcard.trans hcard'.symm
  have htouch := seamPlateau_neutral_touches_southwest t heq
  have hnot := seamPlateau_not_both_southwest t hne ht hcard
    (seamMatchingBirth_first_lt_third a b r hr hb (by omega))
  obtain ⟨S, D, hS, hD, hsides⟩ : ∃ S D : Fin (n + m + 1),
      S ∈ seamSouthwestColumns b.val.val ∧ D ∉ seamSouthwestColumns b.val.val ∧
      ((t.left = S ∧ t.right = D) ∨ (t.right = S ∧ t.left = D)) := by
    rcases htouch with hl | hh
    · exact ⟨t.left, t.right, hl, fun hh => hnot ⟨hl, hh⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨t.right, t.left, hh, fun hl => hnot ⟨hl, hh⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hrange := seamPlateau_internal_other_ranges t heq S D hS hD hsides
  rw [seamComplement_southwest_eq_triple_of_card_three b.val hcard] at hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hrange with ⟨hDn, hDv⟩ | ⟨hDn, hDv⟩
  · exfalso
    rcases hS with rfl | rfl | rfl
    · exact seamPeakPlateau_low_first_impossible a b c d r t u hr ht hu hb hd D hDn hDv hsides
    · exact seamPeakPlateau_low_second_impossible a b c d r t u hr ht hu hb hd D hDn hDv hsides
    · exact seamPlateau_low_third_false t (by omega) D hDn hDv hsides
  · exact ⟨S, D, hS, hDn, hDv, hsides⟩

end OnLeConjecture.KnotFloer.GridFull
