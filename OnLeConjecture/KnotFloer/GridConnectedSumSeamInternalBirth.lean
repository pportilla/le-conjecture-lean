/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamEntryExit

/-!
# Internal rectangles increasing the northeast count

The southwest column set gains exactly the rectangle's right-block
endpoint. Emptiness and the orientation of the complementary pairing
then determine its position among the first two southwest columns.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem northeast_card_eq_of_same_column_block {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) (h : r.left.val < n ↔ r.right.val < n) :
    (seamNortheastColumns (n := n) (m := m) w).card = (seamNortheastColumns v).card := by
  classical
  have hb (c : Fin (n + m + 1)) :
      (Equiv.swap r.left r.right c).val < n ↔ c.val < n := by
    by_cases hl : c = r.left
    · subst c
      rw [Equiv.swap_apply_left]
      exact h.symm
    · by_cases hr : c = r.right
      · subst c
        rw [Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
  have hs : seamNortheastColumns w =
      (seamNortheastColumns v).image (Equiv.swap r.left r.right) := by
    ext c
    constructor
    · intro hc
      obtain ⟨hc, hv⟩ := (mem_seamNortheastColumns w c).mp hc
      refine Finset.mem_image.mpr ⟨Equiv.swap r.left r.right c, ?_, by simp⟩
      apply (mem_seamNortheastColumns _ _).mpr
      exact ⟨(hb c).mpr hc, by rwa [r.target_apply c] at hv⟩
    · rintro hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨ha, hv⟩ := (mem_seamNortheastColumns v a).mp ha
      apply (mem_seamNortheastColumns _ _).mpr
      refine ⟨(hb a).mpr ha, ?_⟩
      simpa only [r.target_apply, Equiv.swap_apply_self] using hv
  rw [hs, Finset.card_image_of_injective _ (Equiv.swap r.left r.right).injective]

/-- Any rectangle increasing the northeast count crosses both cuts in the birth orientation. -/
theorem seamRectangle_birth_ranges {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w)
    (hb : (seamNortheastColumns (n := n) (m := m) w).card =
      (seamNortheastColumns v).card + 1) :
    (r.left.val < n ∧ n ≤ r.right.val ∧ r.bottom.val ≤ n ∧ n < r.top.val) ∨
      (r.right.val < n ∧ n ≤ r.left.val ∧ r.top.val ≤ n ∧ n < r.bottom.val) := by
  have hlt : (seamNortheastColumns v).card < (seamNortheastColumns w).card := by omega
  obtain ⟨c, hc, hcv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hc, hwr⟩ := (mem_seamNortheastColumns w c).mp hc
  have hvr : (v c).val ≤ n := by
    simpa only [mem_seamNortheastColumns, hc, true_and, Nat.not_lt] using hcv
  have hside : c = r.left ∨ c = r.right := by
    by_contra hh
    push Not at hh
    rw [r.map_of_ne c hh.1 hh.2] at hwr
    omega
  rcases hside with rfl | rfl
  · have hright : n ≤ r.right.val := by
      by_contra hh
      have hh : r.left.val < n ↔ r.right.val < n := by constructor <;> intro <;> omega
      have he := northeast_card_eq_of_same_column_block r hh
      omega
    exact Or.inl ⟨hc, hright, hvr, by simpa only [r.map_left, top_def] using hwr⟩
  · have hleft : n ≤ r.left.val := by
      by_contra hh
      have hh : r.left.val < n ↔ r.right.val < n := by constructor <;> intro <;> omega
      have he := northeast_card_eq_of_same_column_block r hh
      omega
    exact Or.inr ⟨hc, hleft, hvr, by simpa only [r.map_right, bottom_def] using hwr⟩

/-- In the nonwrapping birth orientation the southwest set gains precisely the right endpoint. -/
theorem seamRectangle_birth_southwest_insert_right {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w)
    (hl : r.left.val < n) (hr : n ≤ r.right.val)
    (hb : r.bottom.val ≤ n) (_ht : n < r.top.val) :
    seamSouthwestColumns w = insert r.right (seamSouthwestColumns (n := n) (m := m) v) := by
  classical
  ext c
  simp only [mem_seamSouthwestColumns, Finset.mem_insert]
  by_cases hcl : c = r.left
  · subst c
    have hn := r.left_ne_right
    simp only [r.map_left, hn, false_or]
    constructor <;> rintro ⟨hh, _⟩ <;> omega
  · by_cases hcr : c = r.right
    · subst c
      simp only [r.map_right, ← bottom_def, true_or]
      exact iff_of_true ⟨hr, hb⟩ trivial
    · rw [r.map_of_ne c hcl hcr]
      simp only [hcr, false_or]

/-- In the wrapping birth orientation the southwest set gains precisely the left endpoint. -/
theorem seamRectangle_birth_southwest_insert_left {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w)
    (hr : r.right.val < n) (hl : n ≤ r.left.val)
    (ht : r.top.val ≤ n) (hb : n < r.bottom.val) :
    seamSouthwestColumns w = insert r.left (seamSouthwestColumns (n := n) (m := m) v) := by
  have hh := seamRectangle_birth_southwest_insert_right r.swapSides
    (by simpa only [swapSides_left] using hr)
    (by simpa only [swapSides_right] using hl)
    (by simpa only [swapSides_bottom] using ht)
    (by simpa only [swapSides_top] using hb)
  simpa only [swapSides_right] using hh

/-- A northeast-count increase between matched nodes has the same two cut orientations. -/
theorem seamMatchingBirth_ranges {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1) :
    (r.left.val < n ∧ n ≤ r.right.val ∧ r.bottom.val ≤ n ∧ n < r.top.val) ∨
      (r.right.val < n ∧ n ≤ r.left.val ∧ r.top.val ≤ n ∧ n < r.bottom.val) := by
  apply seamRectangle_birth_ranges r
  rwa [seamComplementPartner_northeastColumns]

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

private theorem first_second_insert_before (x y : SeamComplement n m)
    {c : Fin (n + m + 1)} (hs : seamSouthwestColumns y.val = insert c (seamSouthwestColumns x.val))
    (hc : c < seamComplementFirst x) :
    seamComplementFirst y = c ∧ seamComplementSecond y = seamComplementFirst x := by
  classical
  have hfirst : seamComplementFirst y = c := by
    apply first_eq_of_mem_le y (by rw [hs]; exact Finset.mem_insert_self _ _)
    intro b hb
    rw [hs] at hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact le_rfl
    · exact le_trans hc.le (first_le_of_mem x hb)
  refine ⟨hfirst, ?_⟩
  apply second_eq_of_mem_le y
    (by rw [hs]; exact Finset.mem_insert_of_mem (seamComplementFirst_mem x))
    (by rw [hfirst]; exact ne_of_gt hc)
  intro b hb hbne
  rw [hs] at hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact False.elim (hbne hfirst.symm)
  · exact first_le_of_mem x hb

private theorem first_second_insert_between (x y : SeamComplement n m)
    {c : Fin (n + m + 1)} (hs : seamSouthwestColumns y.val = insert c (seamSouthwestColumns x.val))
    (hp : seamComplementFirst x < c) (hq : c < seamComplementSecond x) :
    seamComplementFirst y = seamComplementFirst x ∧ seamComplementSecond y = c := by
  classical
  have hfirst : seamComplementFirst y = seamComplementFirst x := by
    apply first_eq_of_mem_le y
      (by rw [hs]; exact Finset.mem_insert_of_mem (seamComplementFirst_mem x))
    intro b hb
    rw [hs] at hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hp.le
    · exact first_le_of_mem x hb
  refine ⟨hfirst, ?_⟩
  apply second_eq_of_mem_le y (by rw [hs]; exact Finset.mem_insert_self _ _)
    (by rw [hfirst]; exact ne_of_gt hp)
  intro b hb hbne
  rw [hfirst] at hbne
  rw [hs] at hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact le_rfl
  · exact le_trans hq.le (second_le_of_mem x hb hbne)

private theorem first_second_insert_after (x y : SeamComplement n m)
    {c : Fin (n + m + 1)} (hs : seamSouthwestColumns y.val = insert c (seamSouthwestColumns x.val))
    (hq : seamComplementSecond x < c) :
    seamComplementFirst y = seamComplementFirst x ∧
      seamComplementSecond y = seamComplementSecond x := by
  classical
  have hp := seamComplementFirst_lt_second x
  have hfirst : seamComplementFirst y = seamComplementFirst x := by
    apply first_eq_of_mem_le y
      (by rw [hs]; exact Finset.mem_insert_of_mem (seamComplementFirst_mem x))
    intro b hb
    rw [hs] at hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact le_trans hp.le hq.le
    · exact first_le_of_mem x hb
  refine ⟨hfirst, ?_⟩
  apply second_eq_of_mem_le y
    (by rw [hs]; exact Finset.mem_insert_of_mem (seamComplementSecond_mem x))
    (by rw [hfirst]; exact ne_of_gt hp)
  intro b hb hbne
  rw [hfirst] at hbne
  rw [hs] at hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact hq.le
  · exact second_le_of_mem x hb hbne

private theorem new_column_lt_second (x y : SeamMatchingSource n m)
    {c : Fin (n + m + 1)}
    (hs : seamSouthwestColumns y.val.val = insert c (seamSouthwestColumns x.val.val))
    (hnot : c ∉ seamSouthwestColumns x.val.val)
    (hp : (seamComplementPartner y.val).val (seamComplementFirst x.val) =
      x.val.val (seamComplementFirst x.val))
    (hq : (seamComplementPartner y.val).val (seamComplementSecond x.val) =
      x.val.val (seamComplementSecond x.val)) : c < seamComplementSecond x.val := by
  have hne : c ≠ seamComplementSecond x.val := by
    intro he
    exact hnot (he.symm ▸ seamComplementSecond_mem x.val)
  by_contra hh
  have hafter : seamComplementSecond x.val < c := lt_of_le_of_ne (le_of_not_gt hh) hne.symm
  obtain ⟨hf, hsnd⟩ := first_second_insert_after x.val y.val hs hafter
  have hdesc := seamMatchingTarget_first_gt_second y
  rw [hf, hsnd, hp, hq] at hdesc
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

private theorem birth_target_empty {v w : GridState (n + m + 1)}
    (r : GridRectangleBetween v w) (he : r.IsEmpty) :
    ∀ c ∈ Grid.cIoo r.left r.right, w c ∉ Grid.cIoo r.bottom r.top := by
  simpa only [r.map_right, r.map_left, bottom_def, top_def] using
    (isEmpty_iff_forall_notMem_cIoo_target r).mp he

/-- A nonwrapping birth inserts the new column before the first southwest column. -/
theorem seamMatchingBirth_nonwrap (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hl : r.left.val < n) :
    n ≤ r.right.val ∧ r.right < seamComplementFirst x.val ∧
      seamSouthwestColumns y.val.val = insert r.right (seamSouthwestColumns x.val.val) ∧
      seamComplementFirst y.val = r.right ∧
      seamComplementSecond y.val = seamComplementFirst x.val ∧
      y.val.val (seamComplementFirst y.val) = x.val.val (seamComplementFirst x.val) := by
  have hranges := seamMatchingBirth_ranges r hb
  have hr : n ≤ r.right.val ∧ r.bottom.val ≤ n ∧ n < r.top.val := by
    rcases hranges with h | h
    · exact h.2
    · omega
  have hs : seamSouthwestColumns y.val.val = insert r.right (seamSouthwestColumns x.val.val) := by
    rw [← seamComplementPartner_southwestColumns]
    exact seamRectangle_birth_southwest_insert_right r hl hr.1 hr.2.1 hr.2.2
  have hnot : r.right ∉ seamSouthwestColumns x.val.val := by
    intro hh
    have hh := (mem_seamSouthwestColumns _ _).mp hh
    have ht : n < (x.val.val r.right).val := hr.2.2
    omega
  have hpMem := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hqMem := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpne : seamComplementFirst x.val ≠ r.right := by
    intro hh
    exact hnot (hh ▸ seamComplementFirst_mem x.val)
  have hqne : seamComplementSecond x.val ≠ r.right := by
    intro hh
    exact hnot (hh ▸ seamComplementSecond_mem x.val)
  have hpunchanged := r.map_of_ne (seamComplementFirst x.val)
    (fun hh => by have := congrArg Fin.val hh; omega) hpne
  have hqunchanged := r.map_of_ne (seamComplementSecond x.val)
    (fun hh => by have := congrArg Fin.val hh; omega) hqne
  have hcq := new_column_lt_second x y hs hnot hpunchanged hqunchanged
  have hcp : r.right < seamComplementFirst x.val := by
    by_contra hh
    have hpc : seamComplementFirst x.val < r.right :=
      lt_of_le_of_ne (le_of_not_gt hh) hpne
    obtain ⟨hf, hsecond⟩ := first_second_insert_between x.val y.val hs hpc hcq
    have hdesc := seamMatchingTarget_first_gt_second y
    rw [hf, hsecond, hpunchanged, r.map_right, ← bottom_def] at hdesc
    have hcolumn : seamComplementFirst x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_increasing (by omega) hpc
    apply False.elim (birth_target_empty r he _ hcolumn ?_)
    rw [hpunchanged]
    exact mem_cIoo_increasing hdesc (by omega)
  obtain ⟨hf, hsecond⟩ := first_second_insert_before x.val y.val hs hcp
  refine ⟨hr.1, hcp, hs, hf, hsecond, ?_⟩
  have hh := seamComplementPartner_apply_second y.val
  rw [hsecond, hpunchanged] at hh
  exact hh.symm

/-- A wrapping birth inserts a column strictly between the first two southwest columns. -/
theorem seamMatchingBirth_wrap (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hr : r.right.val < n) :
    seamComplementFirst x.val < r.left ∧ r.left < seamComplementSecond x.val ∧
      seamSouthwestColumns y.val.val = insert r.left (seamSouthwestColumns x.val.val) ∧
      seamComplementFirst y.val = seamComplementFirst x.val ∧
      seamComplementSecond y.val = r.left ∧
      (y.val.val (seamComplementFirst y.val)).val <
        (x.val.val (seamComplementFirst x.val)).val := by
  have hranges := seamMatchingBirth_ranges r hb
  have hl : n ≤ r.left.val ∧ r.top.val ≤ n ∧ n < r.bottom.val := by
    rcases hranges with h | h
    · omega
    · exact h.2
  have hs : seamSouthwestColumns y.val.val = insert r.left (seamSouthwestColumns x.val.val) := by
    rw [← seamComplementPartner_southwestColumns]
    exact seamRectangle_birth_southwest_insert_left r hr hl.1 hl.2.1 hl.2.2
  have hnot : r.left ∉ seamSouthwestColumns x.val.val := by
    intro hh
    have hh := (mem_seamSouthwestColumns _ _).mp hh
    have ht : n < (x.val.val r.left).val := hl.2.2
    omega
  have hpMem := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hqMem := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpne : seamComplementFirst x.val ≠ r.left := by
    intro hh
    exact hnot (hh ▸ seamComplementFirst_mem x.val)
  have hqne : seamComplementSecond x.val ≠ r.left := by
    intro hh
    exact hnot (hh ▸ seamComplementSecond_mem x.val)
  have hpunchanged := r.map_of_ne (seamComplementFirst x.val) hpne
    (fun hh => by have := congrArg Fin.val hh; omega)
  have hqunchanged := r.map_of_ne (seamComplementSecond x.val) hqne
    (fun hh => by have := congrArg Fin.val hh; omega)
  have hcq := new_column_lt_second x y hs hnot hpunchanged hqunchanged
  have hpc : seamComplementFirst x.val < r.left := by
    by_contra hh
    have hcp : r.left < seamComplementFirst x.val :=
      lt_of_le_of_ne (le_of_not_gt hh) hpne.symm
    obtain ⟨hf, hsecond⟩ := first_second_insert_before x.val y.val hs hcp
    have hdesc := seamMatchingTarget_first_gt_second y
    rw [hf, hsecond, hpunchanged, r.map_left, ← top_def] at hdesc
    have hcolumn : seamComplementFirst x.val ∈ Grid.cIoo r.left r.right :=
      mem_cIoo_wrap_high (by omega) hcp
    apply False.elim (birth_target_empty r he _ hcolumn ?_)
    rw [hpunchanged]
    exact mem_cIoo_wrap_low (by omega) hdesc
  obtain ⟨hf, hsecond⟩ := first_second_insert_between x.val y.val hs hpc hcq
  refine ⟨hpc, hcq, hs, hf, hsecond, ?_⟩
  have hh := seamComplementPartner_apply_first y.val
  rw [hf, hpunchanged] at hh
  have hy : (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementSecond y.val)).val := y.property
  rwa [← hh] at hy

/-- The complete endpoint, column-set and row alternatives for an internal birth. -/
theorem seamMatchingBirth_endpoints (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1) :
    (r.left.val < n ∧ n ≤ r.right.val ∧ r.right < seamComplementFirst x.val ∧
      seamSouthwestColumns y.val.val = insert r.right (seamSouthwestColumns x.val.val) ∧
      seamComplementFirst y.val = r.right ∧
      seamComplementSecond y.val = seamComplementFirst x.val ∧
      y.val.val (seamComplementFirst y.val) = x.val.val (seamComplementFirst x.val) ∧
      y.val.val (seamComplementSecond y.val) = r.bottom ∧ n < r.top.val) ∨
    (r.right.val < n ∧ seamComplementFirst x.val < r.left ∧
      r.left < seamComplementSecond x.val ∧
      seamSouthwestColumns y.val.val = insert r.left (seamSouthwestColumns x.val.val) ∧
      seamComplementFirst y.val = seamComplementFirst x.val ∧
      seamComplementSecond y.val = r.left ∧
      y.val.val (seamComplementFirst y.val) = r.top ∧
      y.val.val (seamComplementSecond y.val) = x.val.val (seamComplementFirst x.val) ∧
      (y.val.val (seamComplementFirst y.val)).val <
        (x.val.val (seamComplementFirst x.val)).val ∧ n < r.bottom.val) := by
  rcases seamMatchingBirth_ranges r hb with h | h
  · obtain ⟨hr, hcp, hs, hf, hsecond, hrow⟩ := seamMatchingBirth_nonwrap x y r he hb h.1
    refine Or.inl ⟨h.1, hr, hcp, hs, hf, hsecond, hrow, ?_, h.2.2.2⟩
    have hh := seamComplementPartner_apply_first y.val
    rw [hf, r.map_right, ← bottom_def] at hh
    exact hh.symm
  · obtain ⟨hpc, hcq, hs, hf, hsecond, hrow⟩ := seamMatchingBirth_wrap x y r he hb h.1
    have hpMem := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
    have hpunchanged := r.map_of_ne (seamComplementFirst x.val) (ne_of_lt hpc)
      (fun hh => by have := congrArg Fin.val hh; omega)
    refine Or.inr ⟨h.1, hpc, hcq, hs, hf, hsecond, ?_, ?_, hrow, h.2.2.2⟩
    · have hh := seamComplementPartner_apply_second y.val
      rw [hsecond, r.map_left, ← top_def] at hh
      exact hh.symm
    · have hh := seamComplementPartner_apply_first y.val
      rw [hf, hpunchanged] at hh
      exact hh.symm

/-- Every internal birth strictly decreases the lexicographic first southwest row/column pair. -/
theorem seamMatchingBirth_first_row_column_decreases (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1) :
    (y.val.val (seamComplementFirst y.val)).val <
        (x.val.val (seamComplementFirst x.val)).val ∨
      (y.val.val (seamComplementFirst y.val) = x.val.val (seamComplementFirst x.val) ∧
        seamComplementFirst y.val < seamComplementFirst x.val) := by
  rcases seamMatchingBirth_ranges r hb with h | h
  · obtain ⟨_, hcp, _, hf, _, hrow⟩ := seamMatchingBirth_nonwrap x y r he hb h.1
    exact Or.inr ⟨hrow, by rwa [hf]⟩
  · exact Or.inl (seamMatchingBirth_wrap x y r he hb h.1).2.2.2.2.2

end OnLeConjecture.KnotFloer.GridFull
