/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamInternalBirth

/-!
# Internal rectangles decreasing the northeast count

An internal death means a rectangle for which the northeast cardinality
of the matching source decreases by one. Its southwest column set loses
one column. The third southwest column of the original state determines
the two selected columns and their rows after this deletion.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- Every rectangle decreasing the northeast count has one of these two cut orientations. -/
theorem seamRectangle_death_ranges {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w)
    (hd : (seamNortheastColumns (n := n) (m := m) v).card =
      (seamNortheastColumns w).card + 1) :
    (r.left.val < n ∧ n ≤ r.right.val ∧ r.top.val ≤ n ∧ n < r.bottom.val) ∨
      (r.right.val < n ∧ n ≤ r.left.val ∧ r.bottom.val ≤ n ∧ n < r.top.val) := by
  let rb := ofSwapColumns w v r.left r.right r.left_ne_right r.source_eq_swapColumns
  have hh := seamRectangle_birth_ranges rb hd
  simpa only [rb, ofSwapColumns_left, ofSwapColumns_right,
    bottom_def, top_def, r.map_left, r.map_right] using hh

/-- A nonwrapping death deletes precisely the right endpoint from the southwest set. -/
theorem seamRectangle_death_southwest_erase_right {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) (hl : r.left.val < n) (_hr : n ≤ r.right.val)
    (hb : n < r.bottom.val) (_ht : r.top.val ≤ n) :
    seamSouthwestColumns w = (seamSouthwestColumns (n := n) (m := m) v).erase r.right := by
  classical
  ext c
  simp only [mem_seamSouthwestColumns, Finset.mem_erase]
  by_cases hcl : c = r.left
  · subst c
    simp only [r.map_left]
    constructor <;> rintro ⟨hh, _⟩ <;> omega
  · by_cases hcr : c = r.right
    · subst c
      simp only [r.map_right, ← bottom_def, ne_eq, not_true_eq_false, false_and]
      constructor
      · rintro ⟨_, hh⟩
        omega
      · exact False.elim
    · rw [r.map_of_ne c hcl hcr]
      simp only [hcr, ne_eq, not_false_eq_true, true_and]

/-- A wrapping death deletes precisely the left endpoint from the southwest set. -/
theorem seamRectangle_death_southwest_erase_left {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) (hr : r.right.val < n) (hl : n ≤ r.left.val)
    (ht : n < r.top.val) (hb : r.bottom.val ≤ n) :
    seamSouthwestColumns w = (seamSouthwestColumns (n := n) (m := m) v).erase r.left := by
  have hh := seamRectangle_death_southwest_erase_right r.swapSides
    (by simpa only [swapSides_left] using hr)
    (by simpa only [swapSides_right] using hl)
    (by simpa only [swapSides_bottom] using ht)
    (by simpa only [swapSides_top] using hb)
  simpa only [swapSides_right] using hh

/-- A northeast-count decrease between matched nodes has these two cut orientations. -/
theorem seamMatchingDeath_ranges {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hd : (seamNortheastColumns x.val.val).card = (seamNortheastColumns y.val.val).card + 1) :
    (r.left.val < n ∧ n ≤ r.right.val ∧ r.top.val ≤ n ∧ n < r.bottom.val) ∨
      (r.right.val < n ∧ n ≤ r.left.val ∧ r.bottom.val ≤ n ∧ n < r.top.val) := by
  apply seamRectangle_death_ranges r
  rwa [seamComplementPartner_northeastColumns]

/-- The original matching source has at least three southwest columns in an internal death. -/
theorem seamMatchingDeath_three_le_southwest (x y : SeamMatchingSource n m)
    (hd : (seamNortheastColumns x.val.val).card = (seamNortheastColumns y.val.val).card + 1) :
    3 ≤ (seamSouthwestColumns x.val.val).card := by
  have hx := seamSouthwestColumns_card x.val.val
  have hy := seamSouthwestColumns_card y.val.val
  have htwo := two_le_seamSouthwestColumns_card y.val.val y.val.property
  omega

/-- Removing the first two columns leaves a nonempty set if there are at least three. -/
theorem seamComplement_eraseTwo_nonempty (x : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card) :
    (((seamSouthwestColumns x.val).erase (seamComplementFirst x)).erase
      (seamComplementSecond x)).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem (seamComplementSecond_mem_erase x),
    Finset.card_erase_of_mem (seamComplementFirst_mem x)]
  omega

/-- The third southwest column, defined when the southwest set has at least three columns. -/
def seamComplementThird (x : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card) : Fin (n + m + 1) :=
  (((seamSouthwestColumns x.val).erase (seamComplementFirst x)).erase
    (seamComplementSecond x)).min' (seamComplement_eraseTwo_nonempty x hthree)

theorem seamComplementThird_mem_eraseTwo (x : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card) :
    seamComplementThird x hthree ∈
      ((seamSouthwestColumns x.val).erase (seamComplementFirst x)).erase
        (seamComplementSecond x) := Finset.min'_mem _ _

theorem seamComplementThird_mem (x : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card) :
    seamComplementThird x hthree ∈ seamSouthwestColumns x.val :=
  Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (seamComplementThird_mem_eraseTwo x hthree))

theorem seamComplementSecond_lt_third (x : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card) :
    seamComplementSecond x < seamComplementThird x hthree :=
  Finset.min'_lt_of_mem_erase_min' _ _ (seamComplementThird_mem_eraseTwo x hthree)

theorem seamComplementFirst_lt_third (x : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card) :
    seamComplementFirst x < seamComplementThird x hthree :=
  lt_trans (seamComplementFirst_lt_second x) (seamComplementSecond_lt_third x hthree)

private theorem first_le_of_mem (x : SeamComplement n m) {c : Fin (n + m + 1)}
    (hc : c ∈ seamSouthwestColumns x.val) : seamComplementFirst x ≤ c :=
  Finset.min'_le _ c hc

private theorem second_le_of_mem (x : SeamComplement n m) {c : Fin (n + m + 1)}
    (hc : c ∈ seamSouthwestColumns x.val) (hne : c ≠ seamComplementFirst x) :
    seamComplementSecond x ≤ c :=
  Finset.min'_le _ c (Finset.mem_erase.mpr ⟨hne, hc⟩)

private theorem first_eq_of_mem_le (x : SeamComplement n m) {c : Fin (n + m + 1)}
    (hc : c ∈ seamSouthwestColumns x.val)
    (hle : ∀ b ∈ seamSouthwestColumns x.val, c ≤ b) : seamComplementFirst x = c :=
  (Finset.min'_eq_iff _ _ _).mpr ⟨hc, hle⟩

private theorem second_eq_of_mem_le (x : SeamComplement n m) {c : Fin (n + m + 1)}
    (hc : c ∈ seamSouthwestColumns x.val) (hne : c ≠ seamComplementFirst x)
    (hle : ∀ b ∈ seamSouthwestColumns x.val, b ≠ seamComplementFirst x → c ≤ b) :
    seamComplementSecond x = c := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨Finset.mem_erase.mpr ⟨hne, hc⟩, ?_⟩
  intro b hb
  obtain ⟨hbne, hbmem⟩ := Finset.mem_erase.mp hb
  exact hle b hbmem hbne

private theorem first_second_erase_other (x y : SeamComplement n m)
    {c : Fin (n + m + 1)} (hs : seamSouthwestColumns y.val = (seamSouthwestColumns x.val).erase c)
    (hp : seamComplementFirst x ≠ c) (hq : seamComplementSecond x ≠ c) :
    seamComplementFirst y = seamComplementFirst x ∧
      seamComplementSecond y = seamComplementSecond x := by
  classical
  have hf : seamComplementFirst y = seamComplementFirst x := by
    apply first_eq_of_mem_le y
      (by rw [hs]; exact Finset.mem_erase.mpr ⟨hp, seamComplementFirst_mem x⟩)
    intro b hb
    rw [hs] at hb
    exact first_le_of_mem x (Finset.mem_of_mem_erase hb)
  refine ⟨hf, ?_⟩
  apply second_eq_of_mem_le y
    (by rw [hs]; exact Finset.mem_erase.mpr ⟨hq, seamComplementSecond_mem x⟩)
    (by rw [hf]; exact (seamComplementFirst_ne_second x).symm)
  intro b hb hbne
  rw [hs] at hb
  rw [hf] at hbne
  exact second_le_of_mem x (Finset.mem_of_mem_erase hb) hbne

private theorem first_second_erase_first (x y : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card)
    (hs : seamSouthwestColumns y.val =
      (seamSouthwestColumns x.val).erase (seamComplementFirst x)) :
    seamComplementFirst y = seamComplementSecond x ∧
      seamComplementSecond y = seamComplementThird x hthree := by
  have hf : seamComplementFirst y = seamComplementSecond x := by
    simp only [seamComplementFirst, hs, seamComplementSecond]
  refine ⟨hf, ?_⟩
  simp only [seamComplementSecond, hf, hs, seamComplementThird]

private theorem first_second_erase_second (x y : SeamComplement n m)
    (hthree : 3 ≤ (seamSouthwestColumns x.val).card)
    (hs : seamSouthwestColumns y.val =
      (seamSouthwestColumns x.val).erase (seamComplementSecond x)) :
    seamComplementFirst y = seamComplementFirst x ∧
      seamComplementSecond y = seamComplementThird x hthree := by
  classical
  have hf : seamComplementFirst y = seamComplementFirst x := by
    apply first_eq_of_mem_le y
      (by
        rw [hs]
        exact Finset.mem_erase.mpr
          ⟨seamComplementFirst_ne_second x, seamComplementFirst_mem x⟩)
    intro b hb
    rw [hs] at hb
    exact first_le_of_mem x (Finset.mem_of_mem_erase hb)
  refine ⟨hf, ?_⟩
  simp only [seamComplementSecond, hf, hs, Finset.erase_right_comm, seamComplementThird]

private theorem deleted_column_first_or_second (x y : SeamMatchingSource n m)
    {c : Fin (n + m + 1)}
    (hs : seamSouthwestColumns y.val.val = (seamSouthwestColumns x.val.val).erase c)
    (hunchanged : ∀ d ∈ seamSouthwestColumns x.val.val, d ≠ c →
      (seamComplementPartner y.val).val d = x.val.val d) :
    c = seamComplementFirst x.val ∨ c = seamComplementSecond x.val := by
  by_contra hh
  push Not at hh
  obtain ⟨hf, hsecond⟩ := first_second_erase_other x.val y.val hs hh.1.symm hh.2.symm
  have hp := hunchanged _ (seamComplementFirst_mem x.val) hh.1.symm
  have hq := hunchanged _ (seamComplementSecond_mem x.val) hh.2.symm
  have hdesc := seamMatchingTarget_first_gt_second y
  rw [hf, hsecond, hp, hq] at hdesc
  have hasc : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  omega

private theorem mem_cIoo_increasing {l : ℕ} {a b c : Fin l}
    (hac : a.val < c.val) (hcb : c.val < b.val) : c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_pos (by omega)]
  exact ⟨fun h => by have := congrArg Fin.val h; omega, hac, hcb⟩

private theorem mem_cIoo_wrap_high {l : ℕ} {a b c : Fin l}
    (hba : b.val < a.val) (hac : a.val < c.val) : c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_neg (by omega)]
  exact ⟨fun h => by have := congrArg Fin.val h; omega, Or.inl hac⟩

private theorem mem_cIoo_wrap_low {l : ℕ} {a b c : Fin l}
    (hba : b.val < a.val) (hcb : c.val < b.val) : c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_neg (by omega)]
  exact ⟨fun h => by have := congrArg Fin.val h; omega, Or.inr hcb⟩

/-- A nonwrapping internal death deletes the old first southwest column. -/
theorem seamMatchingDeath_right_eq_first_of_left_lt (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hd : (seamNortheastColumns x.val.val).card = (seamNortheastColumns y.val.val).card + 1)
    (hl : r.left.val < n) : r.right = seamComplementFirst x.val := by
  have hranges := seamMatchingDeath_ranges r hd
  have hr : n ≤ r.right.val ∧ r.top.val ≤ n ∧ n < r.bottom.val := by
    rcases hranges with h | h
    · exact h.2
    · omega
  have hs : seamSouthwestColumns y.val.val = (seamSouthwestColumns x.val.val).erase r.right := by
    rw [← seamComplementPartner_southwestColumns]
    exact seamRectangle_death_southwest_erase_right r hl hr.1 hr.2.2 hr.2.1
  have hchoices := deleted_column_first_or_second x y hs (by
    intro d hd hne
    have hd := (mem_seamSouthwestColumns _ _).mp hd
    exact r.map_of_ne d (fun hh => by have := congrArg Fin.val hh; omega) hne)
  rcases hchoices with hh | hh
  · exact hh
  · have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
    have hcol := seamComplementFirst_lt_second x.val
    have hrow : (x.val.val (seamComplementFirst x.val)).val <
        (x.val.val (seamComplementSecond x.val)).val := x.property
    have ht : r.top = x.val.val (seamComplementSecond x.val) := by rw [top_def, hh]
    have hc : seamComplementFirst x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_increasing (by omega) (by rw [hh]; exact hcol)
    apply False.elim (((isEmpty_iff_forall_notMem_cIoo r).mp he _ hc) ?_)
    apply mem_cIoo_wrap_low (by omega)
    rwa [ht]

/-- A wrapping internal death deletes the old second southwest column. -/
theorem seamMatchingDeath_left_eq_second_of_right_lt (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hd : (seamNortheastColumns x.val.val).card = (seamNortheastColumns y.val.val).card + 1)
    (hr : r.right.val < n) : r.left = seamComplementSecond x.val := by
  have hranges := seamMatchingDeath_ranges r hd
  have hl : n ≤ r.left.val ∧ r.bottom.val ≤ n ∧ n < r.top.val := by
    rcases hranges with h | h
    · omega
    · exact h.2
  have hs : seamSouthwestColumns y.val.val = (seamSouthwestColumns x.val.val).erase r.left := by
    rw [← seamComplementPartner_southwestColumns]
    exact seamRectangle_death_southwest_erase_left r hr hl.1 hl.2.2 hl.2.1
  have hchoices := deleted_column_first_or_second x y hs (by
    intro d hd hne
    have hd := (mem_seamSouthwestColumns _ _).mp hd
    exact r.map_of_ne d hne (fun hh => by have := congrArg Fin.val hh; omega))
  rcases hchoices with hh | hh
  · have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
    have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
    have hcol := seamComplementFirst_lt_second x.val
    have hrow : (x.val.val (seamComplementFirst x.val)).val <
        (x.val.val (seamComplementSecond x.val)).val := x.property
    have hb : r.bottom = x.val.val (seamComplementFirst x.val) := by rw [bottom_def, hh]
    have hc : seamComplementSecond x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_wrap_high (by omega) (by rw [hh]; exact hcol)
    apply False.elim (((isEmpty_iff_forall_notMem_cIoo r).mp he _ hc) ?_)
    apply mem_cIoo_increasing
    · rwa [hb]
    · omega
  · exact hh

/-- Deleting the old first column selects the old second and third columns. -/
theorem seamMatchingDeath_nonwrap (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hd : (seamNortheastColumns x.val.val).card = (seamNortheastColumns y.val.val).card + 1)
    (hl : r.left.val < n) :
    let R := seamComplementThird x.val (seamMatchingDeath_three_le_southwest x y hd)
    r.right = seamComplementFirst x.val ∧
      seamSouthwestColumns y.val.val =
        (seamSouthwestColumns x.val.val).erase (seamComplementFirst x.val) ∧
      seamComplementFirst y.val = seamComplementSecond x.val ∧
      seamComplementSecond y.val = R ∧
      y.val.val (seamComplementFirst y.val) = x.val.val R ∧
      y.val.val (seamComplementSecond y.val) = x.val.val (seamComplementSecond x.val) ∧
      (x.val.val R).val < (x.val.val (seamComplementSecond x.val)).val := by
  dsimp only
  let hthree := seamMatchingDeath_three_le_southwest x y hd
  have hr := seamMatchingDeath_right_eq_first_of_left_lt x y r he hd hl
  have hpMem := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hqMem := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have htMem := (mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem x.val hthree)
  have hranges := seamMatchingDeath_ranges r hd
  have hrows : r.top.val ≤ n ∧ n < r.bottom.val := by
    rcases hranges with h | h
    · exact h.2.2
    · omega
  have hs : seamSouthwestColumns y.val.val =
      (seamSouthwestColumns x.val.val).erase (seamComplementFirst x.val) := by
    rw [← hr, ← seamComplementPartner_southwestColumns]
    exact seamRectangle_death_southwest_erase_right r hl (by rw [hr]; exact hpMem.1)
      hrows.2 hrows.1
  obtain ⟨hf, hsecond⟩ := first_second_erase_first x.val y.val hthree hs
  have hqneq : seamComplementSecond x.val ≠ r.right := by
    rw [hr]
    exact (seamComplementFirst_ne_second x.val).symm
  have htneq : seamComplementThird x.val hthree ≠ r.right := by
    rw [hr]
    exact ne_of_gt (seamComplementFirst_lt_third x.val hthree)
  have hq := r.map_of_ne (seamComplementSecond x.val)
    (fun hh => by have := congrArg Fin.val hh; omega) hqneq
  have ht := r.map_of_ne (seamComplementThird x.val hthree)
    (fun hh => by have := congrArg Fin.val hh; omega) htneq
  have hrow1 := seamComplementPartner_apply_second y.val
  rw [hsecond, ht] at hrow1
  have hrow2 := seamComplementPartner_apply_first y.val
  rw [hf, hq] at hrow2
  refine ⟨hr, hs, hf, hsecond, hrow1.symm, hrow2.symm, ?_⟩
  have hy : (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementSecond y.val)).val := y.property
  rwa [← hrow1, ← hrow2] at hy

/-- Deleting the old second column selects the old first and third columns. -/
theorem seamMatchingDeath_wrap (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hd : (seamNortheastColumns x.val.val).card = (seamNortheastColumns y.val.val).card + 1)
    (hr : r.right.val < n) :
    let R := seamComplementThird x.val (seamMatchingDeath_three_le_southwest x y hd)
    r.left = seamComplementSecond x.val ∧
      seamSouthwestColumns y.val.val =
        (seamSouthwestColumns x.val.val).erase (seamComplementSecond x.val) ∧
      seamComplementFirst y.val = seamComplementFirst x.val ∧
      seamComplementSecond y.val = R ∧
      y.val.val (seamComplementFirst y.val) = x.val.val R ∧
      y.val.val (seamComplementSecond y.val) = x.val.val (seamComplementFirst x.val) ∧
      (x.val.val R).val < (x.val.val (seamComplementFirst x.val)).val := by
  dsimp only
  let hthree := seamMatchingDeath_three_le_southwest x y hd
  have hl := seamMatchingDeath_left_eq_second_of_right_lt x y r he hd hr
  have hpMem := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hqMem := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have htMem := (mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem x.val hthree)
  have hranges := seamMatchingDeath_ranges r hd
  have hrows : r.bottom.val ≤ n ∧ n < r.top.val := by
    rcases hranges with h | h
    · omega
    · exact h.2.2
  have hs : seamSouthwestColumns y.val.val =
      (seamSouthwestColumns x.val.val).erase (seamComplementSecond x.val) := by
    rw [← hl, ← seamComplementPartner_southwestColumns]
    exact seamRectangle_death_southwest_erase_left r hr (by rw [hl]; exact hqMem.1)
      hrows.2 hrows.1
  obtain ⟨hf, hsecond⟩ := first_second_erase_second x.val y.val hthree hs
  have hpneq : seamComplementFirst x.val ≠ r.left := by
    rw [hl]
    exact seamComplementFirst_ne_second x.val
  have htneq : seamComplementThird x.val hthree ≠ r.left := by
    rw [hl]
    exact ne_of_gt (seamComplementSecond_lt_third x.val hthree)
  have hp := r.map_of_ne (seamComplementFirst x.val) hpneq
    (fun hh => by have := congrArg Fin.val hh; omega)
  have ht := r.map_of_ne (seamComplementThird x.val hthree) htneq
    (fun hh => by have := congrArg Fin.val hh; omega)
  have hrow1 := seamComplementPartner_apply_second y.val
  rw [hsecond, ht] at hrow1
  have hrow2 := seamComplementPartner_apply_first y.val
  rw [hf, hp] at hrow2
  refine ⟨hl, hs, hf, hsecond, hrow1.symm, hrow2.symm, ?_⟩
  have hy : (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementSecond y.val)).val := y.property
  rwa [← hrow1, ← hrow2] at hy

/-- The two endpoint, southwest-deletion and row alternatives for an internal death. -/
theorem seamMatchingDeath_endpoints (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hd : (seamNortheastColumns x.val.val).card = (seamNortheastColumns y.val.val).card + 1) :
    let R := seamComplementThird x.val (seamMatchingDeath_three_le_southwest x y hd)
    (r.left.val < n ∧ r.right = seamComplementFirst x.val ∧
      r.top = x.val.val (seamComplementFirst x.val) ∧ n < r.bottom.val ∧
      seamSouthwestColumns y.val.val =
        (seamSouthwestColumns x.val.val).erase (seamComplementFirst x.val) ∧
      seamComplementFirst y.val = seamComplementSecond x.val ∧
      seamComplementSecond y.val = R ∧
      y.val.val (seamComplementFirst y.val) = x.val.val R ∧
      y.val.val (seamComplementSecond y.val) = x.val.val (seamComplementSecond x.val) ∧
      (x.val.val R).val < (x.val.val (seamComplementSecond x.val)).val) ∨
    (r.right.val < n ∧ r.left = seamComplementSecond x.val ∧
      r.bottom = x.val.val (seamComplementSecond x.val) ∧ n < r.top.val ∧
      seamSouthwestColumns y.val.val =
        (seamSouthwestColumns x.val.val).erase (seamComplementSecond x.val) ∧
      seamComplementFirst y.val = seamComplementFirst x.val ∧
      seamComplementSecond y.val = R ∧
      y.val.val (seamComplementFirst y.val) = x.val.val R ∧
      y.val.val (seamComplementSecond y.val) = x.val.val (seamComplementFirst x.val) ∧
      (x.val.val R).val < (x.val.val (seamComplementFirst x.val)).val) := by
  dsimp only
  rcases seamMatchingDeath_ranges r hd with h | h
  · obtain ⟨hr, hs, hf, hsecond, hrow1, hrow2, hlt⟩ :=
      seamMatchingDeath_nonwrap x y r he hd h.1
    refine Or.inl ⟨h.1, hr, ?_, h.2.2.2, hs, hf, hsecond, hrow1, hrow2, hlt⟩
    rw [top_def, hr]
  · obtain ⟨hl, hs, hf, hsecond, hrow1, hrow2, hlt⟩ :=
      seamMatchingDeath_wrap x y r he hd h.1
    refine Or.inr ⟨h.1, hl, ?_, h.2.2.2, hs, hf, hsecond, hrow1, hrow2, hlt⟩
    rw [bottom_def, hl]

end OnLeConjecture.KnotFloer.GridFull
