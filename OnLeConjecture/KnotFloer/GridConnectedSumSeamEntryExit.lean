/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamMatchingPaths

/-!
# Rectangles entering and leaving the complementary seam states

A rectangle crossing between the retained state set and its complement
has exactly one northeast state point on its complementary side. The
endpoint alternatives retain both the nonwrapping and wrapping cases.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The retained row condition at any column strictly before the shared column. -/
theorem seamPairSector_row_le {w : GridState (n + m + 1)} (hw : SeamPairSector w)
    (c : Fin (n + m + 1)) (hc : c.val < n) : (w c).val ≤ n := by
  have he : seamLeft n m (⟨c.val, hc⟩ : Fin n).castSucc = c := Fin.ext rfl
  simpa only [he] using hw (⟨c.val, hc⟩ : Fin n)

/-- Every entering rectangle crosses the column cut and the row cut, in one of two orientations. -/
theorem seamEnteringRectangle_ranges {v w : GridState (n + m + 1)}
    (hv : SeamPairSector v) (hw : ¬ SeamPairSector w) (r : GridRectangleBetween v w) :
    (r.left.val < n ∧ n ≤ r.right.val ∧ r.bottom.val ≤ n ∧ n < r.top.val) ∨
      (r.right.val < n ∧ n ≤ r.left.val ∧ r.top.val ≤ n ∧ n < r.bottom.val) := by
  obtain ⟨c, hc⟩ := (seamNortheastColumns_nonempty_iff w).mpr hw
  obtain ⟨hcl, hcr⟩ := (mem_seamNortheastColumns w c).mp hc
  have hside : c = r.left ∨ c = r.right := by
    by_contra h
    push Not at h
    rw [r.map_of_ne c h.1 h.2] at hcr
    have hh := seamPairSector_row_le hv c hcl
    omega
  rcases hside with rfl | rfl
  · left
    have hh := seamPairSector_row_le hv r.left hcl
    have htop : n < r.top.val := by simpa only [r.map_left, top_def] using hcr
    have hright : n ≤ r.right.val := by
      by_contra h
      have ht := seamPairSector_row_le hv r.right (by omega)
      rw [top_def] at htop
      omega
    exact ⟨hcl, hright, by simpa only [bottom_def] using hh, htop⟩
  · right
    have hh := seamPairSector_row_le hv r.right hcl
    have hbottom : n < r.bottom.val := by simpa only [r.map_right, bottom_def] using hcr
    have hleft : n ≤ r.left.val := by
      by_contra h
      have ht := seamPairSector_row_le hv r.left (by omega)
      rw [bottom_def] at hbottom
      omega
    exact ⟨hcl, hleft, by simpa only [top_def] using hh, hbottom⟩

/-- The unique northeast column of an entering rectangle is its first-block endpoint. -/
theorem seamEnteringRectangle_northeast_eq_singleton {v w : GridState (n + m + 1)}
    (hv : SeamPairSector v) (hw : ¬ SeamPairSector w) (r : GridRectangleBetween v w) :
    seamNortheastColumns (n := n) (m := m) w =
      {if r.left.val < n then r.left else r.right} := by
  classical
  rcases seamEnteringRectangle_ranges hv hw r with h | h
  · rw [if_pos h.1]
    ext c
    simp only [mem_seamNortheastColumns, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hr⟩
      by_contra hne
      have hnr : c ≠ r.right := by intro he; subst c; omega
      rw [r.map_of_ne c hne hnr] at hr
      have hh := seamPairSector_row_le hv c hc
      omega
    · rintro rfl
      refine ⟨h.1, ?_⟩
      simpa only [r.map_left, ← top_def] using h.2.2.2
  · rw [if_neg (by omega)]
    ext c
    simp only [mem_seamNortheastColumns, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hr⟩
      by_contra hne
      have hnl : c ≠ r.left := by intro he; subst c; omega
      rw [r.map_of_ne c hnl hne] at hr
      have hh := seamPairSector_row_le hv c hc
      omega
    · rintro rfl
      refine ⟨h.1, ?_⟩
      simpa only [r.map_right, ← bottom_def] using h.2.2.2

/-- Entering the complement produces exactly one northeast point. -/
theorem seamEnteringRectangle_northeast_card {v w : GridState (n + m + 1)}
    (hv : SeamPairSector v) (hw : ¬ SeamPairSector w) (r : GridRectangleBetween v w) :
    (seamNortheastColumns (n := n) (m := m) w).card = 1 := by
  rw [seamEnteringRectangle_northeast_eq_singleton hv hw r, Finset.card_singleton]

/-- Entering the complement produces exactly two southwest points. -/
theorem seamEnteringRectangle_southwest_card {v w : GridState (n + m + 1)}
    (hv : SeamPairSector v) (hw : ¬ SeamPairSector w) (r : GridRectangleBetween v w) :
    (seamSouthwestColumns (n := n) (m := m) w).card = 2 := by
  rw [seamSouthwestColumns_card, seamEnteringRectangle_northeast_card hv hw r]

/-- The pairing changes no state point in a first-block column. -/
theorem seamComplementPartner_firstBlock_apply (x : SeamComplement n m)
    (c : Fin (n + m + 1)) (hc : c.val < n) : (seamComplementPartner x).val c = x.val c := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x)
  change x.val.swapColumns _ _ c = x.val c
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne]
  · intro he
    have := congrArg Fin.val he
    omega
  · intro he
    have := congrArg Fin.val he
    omega

/-- The pairing preserves the complete northeast column set. -/
theorem seamComplementPartner_northeastColumns (x : SeamComplement n m) :
    seamNortheastColumns (seamComplementPartner x).val = seamNortheastColumns x.val := by
  ext c
  simp only [mem_seamNortheastColumns]
  by_cases hc : c.val < n
  · rw [seamComplementPartner_firstBlock_apply x c hc]
  · simp only [hc, false_and]

/-- Every entry into a complementary matching target comes from a node with one northeast point. -/
theorem seamMatchingEntry_northeast_card (p : GridState (n + 1) × GridState (m + 1))
    (x : SeamMatchingSource n m)
    (r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val) :
    (seamNortheastColumns x.val.val).card = 1 := by
  have hh := seamEnteringRectangle_northeast_card (seamState_mem_pairSector p.1 p.2)
    (seamComplementPartner x.val).property r
  rwa [seamComplementPartner_northeastColumns] at hh

/-- Every entry node has exactly its two selected southwest points. -/
theorem seamMatchingEntry_southwest_card (p : GridState (n + 1) × GridState (m + 1))
    (x : SeamMatchingSource n m)
    (r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val) :
    (seamSouthwestColumns x.val.val).card = 2 := by
  rw [seamSouthwestColumns_card, seamMatchingEntry_northeast_card p x r]



/-- Every leaving rectangle crosses the same two cuts, with its source rows reversed. -/
theorem seamLeavingRectangle_ranges {v w : GridState (n + m + 1)}
    (hv : SeamPairSector v) (hw : ¬ SeamPairSector w) (r : GridRectangleBetween w v) :
    (r.left.val < n ∧ n ≤ r.right.val ∧ r.top.val ≤ n ∧ n < r.bottom.val) ∨
      (r.right.val < n ∧ n ≤ r.left.val ∧ r.bottom.val ≤ n ∧ n < r.top.val) := by
  let rb := ofSwapColumns v w r.left r.right r.left_ne_right r.source_eq_swapColumns
  have hh := seamEnteringRectangle_ranges hv hw rb
  simpa only [rb, ofSwapColumns_left, ofSwapColumns_right,
    bottom_def, top_def, r.map_left, r.map_right] using hh

/-- The unique northeast column of a leaving rectangle is its first-block endpoint. -/
theorem seamLeavingRectangle_northeast_eq_singleton {v w : GridState (n + m + 1)}
    (hv : SeamPairSector v) (hw : ¬ SeamPairSector w) (r : GridRectangleBetween w v) :
    seamNortheastColumns (n := n) (m := m) w =
      {if r.left.val < n then r.left else r.right} := by
  let rb := ofSwapColumns v w r.left r.right r.left_ne_right r.source_eq_swapColumns
  have hh := seamEnteringRectangle_northeast_eq_singleton hv hw rb
  simpa only [rb, ofSwapColumns_left, ofSwapColumns_right] using hh

/-- Every exit source has exactly one northeast state point. -/
theorem seamMatchingExit_northeast_card (p : GridState (n + 1) × GridState (m + 1))
    (x : SeamMatchingSource n m) (r : GridRectangleBetween x.val.val (seamState p.1 p.2)) :
    (seamNortheastColumns x.val.val).card = 1 := by
  rw [seamLeavingRectangle_northeast_eq_singleton
    (seamState_mem_pairSector p.1 p.2) x.val.property r,
    Finset.card_singleton]

/-- Every exit source has exactly two southwest state points. -/
theorem seamMatchingExit_southwest_card (p : GridState (n + 1) × GridState (m + 1))
    (x : SeamMatchingSource n m) (r : GridRectangleBetween x.val.val (seamState p.1 p.2)) :
    (seamSouthwestColumns x.val.val).card = 2 := by
  rw [seamSouthwestColumns_card, seamMatchingExit_northeast_card p x r]

/-- When there are two southwest points, their columns are exactly the selected pair. -/
theorem seamComplement_southwest_eq_pair_of_card_two (x : SeamComplement n m)
    (hc : (seamSouthwestColumns x.val).card = 2) :
    seamSouthwestColumns x.val = {seamComplementFirst x, seamComplementSecond x} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact seamComplementFirst_mem x
    · exact seamComplementSecond_mem x
  · rw [hc]
    simp only [Finset.card_pair (seamComplementFirst_ne_second x), le_refl]

/-- The target of the matching has the opposite order on the two selected southwest rows. -/
theorem seamMatchingTarget_first_gt_second (x : SeamMatchingSource n m) :
    ((seamComplementPartner x.val).val (seamComplementSecond x.val)).val <
      ((seamComplementPartner x.val).val (seamComplementFirst x.val)).val := by
  simpa only [seamComplementPartner, GridState.swapColumns_apply,
    Equiv.swap_apply_right, Equiv.swap_apply_left, SeamComplementSource] using x.property

/-- The partner's first southwest row is the source's second southwest row. -/
theorem seamComplementPartner_apply_first (x : SeamComplement n m) :
    (seamComplementPartner x).val (seamComplementFirst x) = x.val (seamComplementSecond x) := by
  simp only [seamComplementPartner, GridState.swapColumns_apply, Equiv.swap_apply_left]

/-- The partner's second southwest row is the source's first southwest row. -/
theorem seamComplementPartner_apply_second (x : SeamComplement n m) :
    (seamComplementPartner x).val (seamComplementSecond x) = x.val (seamComplementFirst x) := by
  simp only [seamComplementPartner, GridState.swapColumns_apply, Equiv.swap_apply_right]



private theorem mem_cIoo_of_increasing {l : ℕ} {a b c : Fin l}
    (hac : a.val < c.val) (hcb : c.val < b.val) : c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_pos (by omega)]
  exact ⟨fun h => by have := congrArg Fin.val h; omega, hac, hcb⟩

private theorem mem_cIoo_of_wrap_high {l : ℕ} {a b c : Fin l}
    (hba : b.val < a.val) (hac : a.val < c.val) : c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_neg (by omega)]
  exact ⟨fun h => by have := congrArg Fin.val h; omega, Or.inl hac⟩

private theorem mem_cIoo_of_wrap_low {l : ℕ} {a b c : Fin l}
    (hba : b.val < a.val) (hcb : c.val < b.val) : c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_neg (by omega)]
  exact ⟨fun h => by have := congrArg Fin.val h; omega, Or.inr hcb⟩

private theorem entry_target_empty {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) (he : r.IsEmpty) :
    ∀ c ∈ Grid.cIoo r.left r.right, w c ∉ Grid.cIoo r.bottom r.top := by
  simpa only [r.map_right, r.map_left, bottom_def, top_def] using
    (isEmpty_iff_forall_notMem_cIoo_target r).mp he

/-- A nonwrapping entry ends at the first southwest column of its matching node. -/
theorem seamMatchingEntry_right_eq_first_of_left_lt
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : r.IsEmpty) (hl : r.left.val < n) : r.right = seamComplementFirst x.val := by
  have hrg := seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
    (seamComplementPartner x.val).property r
  have hrange : n ≤ r.right.val ∧ r.bottom.val ≤ n ∧ n < r.top.val := by
    rcases hrg with h | h
    · exact h.2
    · omega
  have hsw : r.right ∈ seamSouthwestColumns x.val.val := by
    rw [← seamComplementPartner_southwestColumns]
    apply (mem_seamSouthwestColumns _ _).mpr
    exact ⟨hrange.1, by simpa only [r.map_right, ← bottom_def] using hrange.2.1⟩
  rw [seamComplement_southwest_eq_pair_of_card_two x.val
    (seamMatchingEntry_southwest_card p x r)] at hsw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsw
  rcases hsw with hh | hh
  · exact hh
  · have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
    have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
    have hcol := seamComplementFirst_lt_second x.val
    have hrow := seamMatchingTarget_first_gt_second x
    have hb : (seamComplementPartner x.val).val (seamComplementSecond x.val) = r.bottom := by
      rw [← hh, r.map_right, bottom_def]
    have htgt : ((seamComplementPartner x.val).val (seamComplementFirst x.val)).val ≤ n := by
      rw [seamComplementPartner_apply_first]
      exact hq.2
    have hc : seamComplementFirst x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_of_increasing (by omega) (by rw [hh]; exact hcol)
    apply False.elim ((entry_target_empty r he _ hc) ?_)
    apply mem_cIoo_of_increasing
    · rwa [← hb]
    · omega

/-- A wrapping entry starts at the second southwest column of its matching node. -/
theorem seamMatchingEntry_left_eq_second_of_right_lt
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : r.IsEmpty) (hr : r.right.val < n) : r.left = seamComplementSecond x.val := by
  have hrg := seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
    (seamComplementPartner x.val).property r
  have hrange : n ≤ r.left.val ∧ r.top.val ≤ n ∧ n < r.bottom.val := by
    rcases hrg with h | h
    · omega
    · exact h.2
  have hsw : r.left ∈ seamSouthwestColumns x.val.val := by
    rw [← seamComplementPartner_southwestColumns]
    apply (mem_seamSouthwestColumns _ _).mpr
    exact ⟨hrange.1, by simpa only [r.map_left, ← top_def] using hrange.2.1⟩
  rw [seamComplement_southwest_eq_pair_of_card_two x.val
    (seamMatchingEntry_southwest_card p x r)] at hsw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsw
  rcases hsw with hh | hh
  · have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
    have hcol := seamComplementFirst_lt_second x.val
    have hrow := seamMatchingTarget_first_gt_second x
    have ht : (seamComplementPartner x.val).val (seamComplementFirst x.val) = r.top := by
      rw [← hh, r.map_left, top_def]
    have hc : seamComplementSecond x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_of_wrap_high (by omega) (by rw [hh]; exact hcol)
    apply False.elim ((entry_target_empty r he _ hc) ?_)
    apply mem_cIoo_of_wrap_low (by omega)
    rwa [← ht]
  · exact hh

/-- A nonwrapping exit ends at the first southwest column of its source. -/
theorem seamMatchingExit_right_eq_first_of_left_lt
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamState p.1 p.2))
    (he : r.IsEmpty) (hl : r.left.val < n) : r.right = seamComplementFirst x.val := by
  have hrg := seamLeavingRectangle_ranges (seamState_mem_pairSector p.1 p.2) x.val.property r
  have hrange : n ≤ r.right.val ∧ r.top.val ≤ n ∧ n < r.bottom.val := by
    rcases hrg with h | h
    · exact h.2
    · omega
  have hsw : r.right ∈ seamSouthwestColumns x.val.val :=
    (mem_seamSouthwestColumns _ _).mpr ⟨hrange.1, hrange.2.1⟩
  rw [seamComplement_southwest_eq_pair_of_card_two x.val
    (seamMatchingExit_southwest_card p x r)] at hsw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsw
  rcases hsw with hh | hh
  · exact hh
  · have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
    have hcol := seamComplementFirst_lt_second x.val
    have hrow : (x.val.val (seamComplementFirst x.val)).val <
        (x.val.val (seamComplementSecond x.val)).val := x.property
    have ht : x.val.val (seamComplementSecond x.val) = r.top := by rw [← hh, top_def]
    have hc : seamComplementFirst x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_of_increasing (by omega) (by rw [hh]; exact hcol)
    apply False.elim (((isEmpty_iff_forall_notMem_cIoo r).mp he _ hc) ?_)
    apply mem_cIoo_of_wrap_low (by omega)
    rwa [← ht]

/-- A wrapping exit starts at the second southwest column of its source. -/
theorem seamMatchingExit_left_eq_second_of_right_lt
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamState p.1 p.2))
    (he : r.IsEmpty) (hr : r.right.val < n) : r.left = seamComplementSecond x.val := by
  have hrg := seamLeavingRectangle_ranges (seamState_mem_pairSector p.1 p.2) x.val.property r
  have hrange : n ≤ r.left.val ∧ r.bottom.val ≤ n ∧ n < r.top.val := by
    rcases hrg with h | h
    · omega
    · exact h.2
  have hsw : r.left ∈ seamSouthwestColumns x.val.val :=
    (mem_seamSouthwestColumns _ _).mpr ⟨hrange.1, hrange.2.1⟩
  rw [seamComplement_southwest_eq_pair_of_card_two x.val
    (seamMatchingExit_southwest_card p x r)] at hsw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsw
  rcases hsw with hh | hh
  · have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
    have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
    have hcol := seamComplementFirst_lt_second x.val
    have hrow : (x.val.val (seamComplementFirst x.val)).val <
        (x.val.val (seamComplementSecond x.val)).val := x.property
    have hb : x.val.val (seamComplementFirst x.val) = r.bottom := by rw [← hh, bottom_def]
    have hc : seamComplementSecond x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_of_wrap_high (by omega) (by rw [hh]; exact hcol)
    apply False.elim (((isEmpty_iff_forall_notMem_cIoo r).mp he _ hc) ?_)
    apply mem_cIoo_of_increasing
    · rwa [← hb]
    · omega
  · exact hh



/-- The entry node's northeast column is precisely the first-block rectangle endpoint. -/
theorem seamMatchingEntry_northeast_eq_singleton
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val) :
    seamNortheastColumns x.val.val = {if r.left.val < n then r.left else r.right} := by
  rw [← seamComplementPartner_northeastColumns]
  exact seamEnteringRectangle_northeast_eq_singleton (seamState_mem_pairSector p.1 p.2)
    (seamComplementPartner x.val).property r

/-- The exit node's northeast column is precisely the first-block rectangle endpoint. -/
theorem seamMatchingExit_northeast_eq_singleton
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamState p.1 p.2)) :
    seamNortheastColumns x.val.val = {if r.left.val < n then r.left else r.right} :=
  seamLeavingRectangle_northeast_eq_singleton (seamState_mem_pairSector p.1 p.2) x.val.property r

/-- An entry recovers the retained state by the matching swap and then the rectangle swap. -/
theorem seamMatchingEntry_source_eq_swaps
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val) :
    seamState p.1 p.2 =
      (x.val.val.swapColumns
        (seamComplementFirst x.val) (seamComplementSecond x.val)).swapColumns r.left r.right :=
  r.source_eq_swapColumns

/-- An exit recovers the retained state by its single rectangle swap. -/
theorem seamMatchingExit_target_eq_swap
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamState p.1 p.2)) :
    seamState p.1 p.2 = x.val.val.swapColumns r.left r.right := r.target_eq_swapColumns

/-- Exact endpoint and row alternatives for every empty full entry rectangle. -/
theorem seamMatchingEntry_endpoints
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : r.IsEmpty) :
    (r.left.val < n ∧ r.right = seamComplementFirst x.val ∧
      r.bottom = x.val.val (seamComplementSecond x.val) ∧
      r.top = x.val.val r.left ∧ n < r.top.val) ∨
    (r.right.val < n ∧ r.left = seamComplementSecond x.val ∧
      r.top = x.val.val (seamComplementFirst x.val) ∧
      r.bottom = x.val.val r.right ∧ n < r.bottom.val) := by
  rcases seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
    (seamComplementPartner x.val).property r with h | h
  · left
    have hr := seamMatchingEntry_right_eq_first_of_left_lt p x r he h.1
    refine ⟨h.1, hr, ?_, ?_, h.2.2.2⟩
    · calc
        r.bottom = (seamComplementPartner x.val).val r.right := r.map_right.symm
        _ = x.val.val (seamComplementSecond x.val) := by
          rw [hr, seamComplementPartner_apply_first]
    · calc
        r.top = (seamComplementPartner x.val).val r.left := r.map_left.symm
        _ = x.val.val r.left := seamComplementPartner_firstBlock_apply x.val r.left h.1
  · right
    have hl := seamMatchingEntry_left_eq_second_of_right_lt p x r he h.1
    refine ⟨h.1, hl, ?_, ?_, h.2.2.2⟩
    · calc
        r.top = (seamComplementPartner x.val).val r.left := r.map_left.symm
        _ = x.val.val (seamComplementFirst x.val) := by
          rw [hl, seamComplementPartner_apply_second]
    · calc
        r.bottom = (seamComplementPartner x.val).val r.right := r.map_right.symm
        _ = x.val.val r.right := seamComplementPartner_firstBlock_apply x.val r.right h.1

/-- Exact endpoint and row alternatives for every empty full exit rectangle. -/
theorem seamMatchingExit_endpoints
    (p : GridState (n + 1) × GridState (m + 1)) (x : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamState p.1 p.2)) (he : r.IsEmpty) :
    (r.left.val < n ∧ r.right = seamComplementFirst x.val ∧
      r.top = x.val.val (seamComplementFirst x.val) ∧ n < r.bottom.val) ∨
    (r.right.val < n ∧ r.left = seamComplementSecond x.val ∧
      r.bottom = x.val.val (seamComplementSecond x.val) ∧ n < r.top.val) := by
  rcases seamLeavingRectangle_ranges (seamState_mem_pairSector p.1 p.2) x.val.property r with h | h
  · have hr := seamMatchingExit_right_eq_first_of_left_lt p x r he h.1
    exact Or.inl ⟨h.1, hr, by rw [top_def, hr], h.2.2.2⟩
  · have hl := seamMatchingExit_left_eq_second_of_right_lt p x r he h.1
    exact Or.inr ⟨h.1, hl, by rw [bottom_def, hl], h.2.2.2⟩

end OnLeConjecture.KnotFloer.GridFull
