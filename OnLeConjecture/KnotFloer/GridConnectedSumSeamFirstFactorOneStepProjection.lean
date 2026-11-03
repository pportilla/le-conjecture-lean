/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepLift
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamInternalDeath

/-! # Reverse restrictions on one-step seam corrections

The entry and exit rectangles force both matching sources to have exactly
two southwest columns. The internal rectangle then exchanges exactly one
of those columns with either a low first-block point or a high second-block
point. The restrictions below are derived from the actual rectangles.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem oneStep_first_congr (x y : SeamComplement n m)
    (h : seamSouthwestColumns x.val = seamSouthwestColumns y.val) :
    seamComplementFirst x = seamComplementFirst y := by
  unfold seamComplementFirst
  congr 1

private theorem oneStep_second_congr (x y : SeamComplement n m)
    (h : seamSouthwestColumns x.val = seamSouthwestColumns y.val) :
    seamComplementSecond x = seamComplementSecond y := by
  unfold seamComplementSecond
  congr 1
  rw [h, oneStep_first_congr x y h]

/-- A nonmatching rectangle cannot exchange exactly the two selected southwest columns. -/
theorem seamOneStep_internal_not_matching_sides {x y : SeamMatchingSource n m}
    (hne : x ≠ y) (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) :
    ¬ ((r.left = seamComplementFirst x.val ∧ r.right = seamComplementSecond x.val) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = seamComplementSecond x.val)) := by
  intro h
  have hs : (seamComplementPartner y.val).val = (seamComplementPartner x.val).val := by
    rw [r.target_eq_swapColumns]
    change x.val.val.swapColumns r.left r.right =
      x.val.val.swapColumns (seamComplementFirst x.val) (seamComplementSecond x.val)
    rcases h with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
    · rw [hl, hr, GridState.swapColumns_comm]
  have hp : seamComplementPartner y.val = seamComplementPartner x.val := Subtype.ext hs
  exact hne (Subtype.ext (seamComplementPartner_involutive.injective hp).symm)

/-- With two southwest columns at both nodes, an internal rectangle touches a selected column. -/
theorem seamOneStep_internal_touches_southwest {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hx : (seamSouthwestColumns x.val.val).card = 2)
    (hy : (seamSouthwestColumns y.val.val).card = 2) :
    r.left = seamComplementFirst x.val ∨ r.left = seamComplementSecond x.val ∨
      r.right = seamComplementFirst x.val ∨ r.right = seamComplementSecond x.val := by
  classical
  by_contra h
  push Not at h
  have hsub : seamSouthwestColumns x.val.val ⊆ seamSouthwestColumns y.val.val := by
    intro c hc
    have hside : c = seamComplementFirst x.val ∨ c = seamComplementSecond x.val := by
      rwa [seamComplement_southwest_eq_pair_of_card_two x.val hx,
        Finset.mem_insert, Finset.mem_singleton] at hc
    have hcl : c ≠ r.left := by rcases hside with rfl | rfl <;> tauto
    have hcr : c ≠ r.right := by rcases hside with rfl | rfl <;> tauto
    rw [← seamComplementPartner_southwestColumns y.val]
    obtain ⟨hcn, hcv⟩ := (mem_seamSouthwestColumns _ _).mp hc
    exact (mem_seamSouthwestColumns _ _).mpr ⟨hcn, by rwa [r.map_of_ne c hcl hcr]⟩
  have hsets : seamSouthwestColumns x.val.val = seamSouthwestColumns y.val.val :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hfirst := oneStep_first_congr x.val y.val hsets
  have hsecond := oneStep_second_congr x.val y.val hsets
  have hP := r.map_of_ne (seamComplementFirst x.val) (by tauto) (by tauto)
  have hQ := r.map_of_ne (seamComplementSecond x.val) (by tauto) (by tauto)
  rw [hfirst, seamComplementPartner_apply_first] at hP
  rw [hsecond, seamComplementPartner_apply_second] at hQ
  have hxs : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hys : (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementSecond y.val)).val := y.property
  rw [hfirst, hsecond] at hxs
  have hp := congrArg Fin.val hP
  have hq := congrArg Fin.val hQ
  omega

/-- Exactly one selected southwest point is exchanged with a point outside the southwest set. -/
theorem seamOneStep_internal_one_southwest {x y : SeamMatchingSource n m}
    (hne : x ≠ y) (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hx : (seamSouthwestColumns x.val.val).card = 2)
    (hy : (seamSouthwestColumns y.val.val).card = 2) :
    ∃ S C : Fin (n + m + 1),
      (S = seamComplementFirst x.val ∨ S = seamComplementSecond x.val) ∧
      C ∉ seamSouthwestColumns x.val.val ∧
      ((r.left = S ∧ r.right = C) ∨ (r.right = S ∧ r.left = C)) := by
  have htouch := seamOneStep_internal_touches_southwest r hx hy
  have hnot := seamOneStep_internal_not_matching_sides hne r
  have hnecol := r.left_ne_right
  rw [seamComplement_southwest_eq_pair_of_card_two x.val hx]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases htouch with hP | hQ | hP | hQ
  · refine ⟨r.left, r.right, Or.inl hP, ?_, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨by intro h; exact hnecol (hP.trans h.symm),
      by intro h; exact hnot (Or.inl ⟨hP, h⟩)⟩
  · refine ⟨r.left, r.right, Or.inr hQ, ?_, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨by intro h; exact hnot (Or.inr ⟨h, hQ⟩),
      by intro h; exact hnecol (hQ.trans h.symm)⟩
  · refine ⟨r.right, r.left, Or.inl hP, ?_, Or.inr ⟨rfl, rfl⟩⟩
    exact ⟨by intro h; exact hnecol (h.trans hP.symm),
      by intro h; exact hnot (Or.inr ⟨hP, h⟩)⟩
  · refine ⟨r.right, r.left, Or.inr hQ, ?_, Or.inr ⟨rfl, rfl⟩⟩
    exact ⟨by intro h; exact hnot (Or.inl ⟨h, hQ⟩),
      by intro h; exact hnecol (h.trans hQ.symm)⟩

/-- The outside endpoint is low in the first block or high in the second block. -/
theorem seamOneStep_internal_other_ranges {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hx : (seamSouthwestColumns x.val.val).card = 2)
    (hy : (seamSouthwestColumns y.val.val).card = 2)
    (S C : Fin (n + m + 1)) (hS : S ∈ seamSouthwestColumns x.val.val)
    (hC : C ∉ seamSouthwestColumns x.val.val)
    (hsides : (r.left = S ∧ r.right = C) ∨ (r.right = S ∧ r.left = C)) :
    (C.val < n ∧ (x.val.val C).val ≤ n) ∨
      (n ≤ C.val ∧ n < (x.val.val C).val) := by
  obtain ⟨hSn, hSv⟩ := (mem_seamSouthwestColumns _ _).mp hS
  by_cases hcn : C.val < n
  · left
    refine ⟨hcn, ?_⟩
    by_contra hv
    have hcv : n < (x.val.val C).val := by omega
    have heq : seamSouthwestColumns (seamComplementPartner y.val).val =
        (seamSouthwestColumns x.val.val).erase S := by
      rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · have hh := seamRectangle_death_southwest_erase_left r
          (by rw [hr]; exact hcn) (by rw [hl]; exact hSn)
          (by change n < (x.val.val r.right).val; rwa [hr])
          (by change (x.val.val r.left).val ≤ n; rwa [hl])
        simpa only [hl] using hh
      · have hh := seamRectangle_death_southwest_erase_right r
          (by rw [hl]; exact hcn) (by rw [hr]; exact hSn)
          (by change n < (x.val.val r.left).val; rwa [hl])
          (by change (x.val.val r.right).val ≤ n; rwa [hr])
        simpa only [hr] using hh
    have hSc : S ∈ seamSouthwestColumns x.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨hSn, hSv⟩
    have hh := congrArg Finset.card heq
    rw [seamComplementPartner_southwestColumns, hy, Finset.card_erase_of_mem hSc, hx] at hh
    omega
  · right
    refine ⟨by omega, ?_⟩
    simp only [mem_seamSouthwestColumns, not_and_or] at hC
    omega

/-- The endpoint restriction for an actual one-step correction needs no extra count assumption. -/
theorem seamFirstFactorOneStep_internal_sides (p q : SeamRetainedIndex n m)
    (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState q.1 q.2)) (hne : x ≠ y) :
    ∃ S C : Fin (n + m + 1),
      (S = seamComplementFirst x.val ∨ S = seamComplementSecond x.val) ∧
      ((r.left = S ∧ r.right = C) ∨ (r.right = S ∧ r.left = C)) ∧
      ((C.val < n ∧ (x.val.val C).val ≤ n) ∨
        (n ≤ C.val ∧ n < (x.val.val C).val)) := by
  have hx := seamMatchingEntry_southwest_card p x e
  have hy := seamMatchingExit_southwest_card q y f
  obtain ⟨S, C, hS, hC, hsides⟩ := seamOneStep_internal_one_southwest hne r hx hy
  have hSm : S ∈ seamSouthwestColumns x.val.val := by
    rcases hS with rfl | rfl
    · exact seamComplementFirst_mem x.val
    · exact seamComplementSecond_mem x.val
  exact ⟨S, C, hS, hsides, seamOneStep_internal_other_ranges r hx hy S C hSm hC hsides⟩

private theorem oneStep_southwest_eq_of_low_rows {x y : SeamMatchingSource n m}
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

/-- Exchanging the first southwest point with a low first-block point has only
the wrapping-row orientation, and raises the two selected southwest rows. -/
theorem seamOneStep_low_first {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (C : Fin (n + m + 1))
    (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C)) :
    r.left = C ∧ r.right = seamComplementFirst x.val ∧
      (x.val.val (seamComplementSecond x.val)).val < (x.val.val C).val ∧
      seamComplementFirst y.val = seamComplementFirst x.val ∧
      seamComplementSecond y.val = seamComplementSecond x.val ∧
      y.val.val (seamComplementFirst x.val) = x.val.val (seamComplementSecond x.val) ∧
      y.val.val (seamComplementSecond x.val) = x.val.val C ∧
      y.val.val C = x.val.val (seamComplementFirst x.val) := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hCp : C ≠ seamComplementFirst x.val := by
    intro h; have := congrArg Fin.val h; omega
  have hCq : C ≠ seamComplementSecond x.val := by
    intro h; have := congrArg Fin.val h; omega
  have hrows : r.bottom.val ≤ n ∧ r.top.val ≤ n := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩ <;>
      simp only [bottom_def, top_def, hl, hr] <;> omega
  have hsets := oneStep_southwest_eq_of_low_rows r hrows.1 hrows.2
  have hfirst := oneStep_first_congr y.val x.val hsets
  have hsecond := oneStep_second_congr y.val x.val hsets
  have hPmap : (seamComplementPartner y.val).val (seamComplementFirst x.val) = x.val.val C := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hl, r.map_left, hr]
    · rw [← hr, r.map_right, hl]
  have hQmap : (seamComplementPartner y.val).val (seamComplementSecond x.val) =
      x.val.val (seamComplementSecond x.val) := by
    apply r.map_of_ne
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hl]; exact (seamComplementFirst_ne_second x.val).symm
      · rw [hl]; exact hCq.symm
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hr]; exact hCq.symm
      · rw [hr]; exact (seamComplementFirst_ne_second x.val).symm
  have hCmap : (seamComplementPartner y.val).val C = x.val.val (seamComplementFirst x.val) := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hr, r.map_right, hl]
    · rw [← hl, r.map_left, hr]
  rw [← hfirst, seamComplementPartner_apply_first, hsecond] at hPmap
  rw [← hsecond, seamComplementPartner_apply_second, hfirst, hsecond] at hQmap
  rw [seamComplementPartner_firstBlock_apply y.val C hCn] at hCmap
  have hlt : (x.val.val (seamComplementSecond x.val)).val < (x.val.val C).val := by
    have hh : (y.val.val (seamComplementFirst y.val)).val <
        (y.val.val (seamComplementSecond y.val)).val := y.property
    rwa [hfirst, hsecond, hQmap, hPmap] at hh
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hright : r.right = seamComplementFirst x.val ∧ r.left = C := by
    rcases hsides with ⟨hl, hr⟩ | hh
    · exfalso
      apply (isEmpty_iff_forall_notMem_cIoo r).mp he (seamComplementSecond x.val)
      · rw [Grid.mem_cIoo, hl, hr, if_neg (by omega)]
        exact ⟨hCp.symm, Or.inl hpq⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hl, hr, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, hsource, hlt⟩
    · exact hh
  exact ⟨hright.2, hright.1, hlt, hfirst, hsecond, hQmap, hPmap, hCmap⟩

/-- Exchanging the second southwest point with a low first-block point has only
the opposite wrapping orientation, and lowers the selected southwest rows. -/
theorem seamOneStep_low_second {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (C : Fin (n + m + 1))
    (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C)) :
    r.left = seamComplementSecond x.val ∧ r.right = C ∧
      (x.val.val C).val < (x.val.val (seamComplementFirst x.val)).val ∧
      seamComplementFirst y.val = seamComplementFirst x.val ∧
      seamComplementSecond y.val = seamComplementSecond x.val ∧
      y.val.val (seamComplementFirst x.val) = x.val.val C ∧
      y.val.val (seamComplementSecond x.val) = x.val.val (seamComplementFirst x.val) ∧
      y.val.val C = x.val.val (seamComplementSecond x.val) := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hCp : C ≠ seamComplementFirst x.val := by
    intro h; have := congrArg Fin.val h; omega
  have hCq : C ≠ seamComplementSecond x.val := by
    intro h; have := congrArg Fin.val h; omega
  have hrows : r.bottom.val ≤ n ∧ r.top.val ≤ n := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩ <;>
      simp only [bottom_def, top_def, hl, hr] <;> omega
  have hsets := oneStep_southwest_eq_of_low_rows r hrows.1 hrows.2
  have hfirst := oneStep_first_congr y.val x.val hsets
  have hsecond := oneStep_second_congr y.val x.val hsets
  have hPmap : (seamComplementPartner y.val).val (seamComplementFirst x.val) =
      x.val.val (seamComplementFirst x.val) := by
    apply r.map_of_ne
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hl]; exact seamComplementFirst_ne_second x.val
      · rw [hl]; exact hCp.symm
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hr]; exact hCp.symm
      · rw [hr]; exact seamComplementFirst_ne_second x.val
  have hQmap : (seamComplementPartner y.val).val (seamComplementSecond x.val) = x.val.val C := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hl, r.map_left, hr]
    · rw [← hr, r.map_right, hl]
  have hCmap : (seamComplementPartner y.val).val C = x.val.val (seamComplementSecond x.val) := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hr, r.map_right, hl]
    · rw [← hl, r.map_left, hr]
  rw [← hfirst, seamComplementPartner_apply_first, hsecond, hfirst] at hPmap
  rw [← hsecond, seamComplementPartner_apply_second, hfirst] at hQmap
  rw [seamComplementPartner_firstBlock_apply y.val C hCn] at hCmap
  have hlt : (x.val.val C).val < (x.val.val (seamComplementFirst x.val)).val := by
    have hh : (y.val.val (seamComplementFirst y.val)).val <
        (y.val.val (seamComplementSecond y.val)).val := y.property
    rwa [hfirst, hsecond, hQmap, hPmap] at hh
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hleft : r.left = seamComplementSecond x.val ∧ r.right = C := by
    rcases hsides with hh | ⟨hr, hl⟩
    · exact hh
    · exfalso
      apply (isEmpty_iff_forall_notMem_cIoo r).mp he (seamComplementFirst x.val)
      · rw [Grid.mem_cIoo, hl, hr, if_pos (by omega)]
        exact ⟨hCq, by omega, hpq⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hl, hr, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, hlt, hsource⟩
  exact ⟨hleft.1, hleft.2, hlt, hfirst, hsecond, hQmap, hPmap, hCmap⟩

private theorem oneStep_southwest_high_swap (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (P Q C : Fin (n + m + 1))
    (hx : seamSouthwestColumns x.val.val = {P, Q}) (hPQ : P ≠ Q)
    (hCn : n ≤ C.val) (hCv : n < (x.val.val C).val)
    (hsides : (r.left = P ∧ r.right = C) ∨ (r.right = P ∧ r.left = C)) :
    seamSouthwestColumns y.val.val = {C, Q} := by
  have hPm : P ∈ seamSouthwestColumns x.val.val := by rw [hx]; simp
  have hQm : Q ∈ seamSouthwestColumns x.val.val := by rw [hx]; simp
  obtain ⟨hPn, hPv⟩ := (mem_seamSouthwestColumns _ _).mp hPm
  obtain ⟨_, hQv⟩ := (mem_seamSouthwestColumns _ _).mp hQm
  have hCP : C ≠ P := by intro h; rw [h] at hCv; omega
  have hCQ : C ≠ Q := by intro h; rw [h] at hCv; omega
  have hstate : (seamComplementPartner y.val).val = x.val.val.swapColumns P C := by
    rw [r.target_eq_swapColumns]
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
    · rw [hl, hr, GridState.swapColumns_comm]
  rw [← seamComplementPartner_southwestColumns, hstate]
  ext c
  by_cases hcP : c = P
  · subst c
    simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply, Equiv.swap_apply_left,
      Finset.mem_insert, Finset.mem_singleton]
    simp only [hCP.symm, hPQ, or_self, iff_false, not_and_or]
    omega
  by_cases hcC : c = C
  · subst c
    simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply, Equiv.swap_apply_right,
      Finset.mem_insert, Finset.mem_singleton, true_or, iff_true]
    exact ⟨hCn, hPv⟩
  have hmem : (n ≤ c.val ∧ (x.val.val c).val ≤ n) ↔ c = P ∨ c = Q := by
    rw [← mem_seamSouthwestColumns, hx, Finset.mem_insert, Finset.mem_singleton]
  simpa only [mem_seamSouthwestColumns, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hcP hcC, Finset.mem_insert, Finset.mem_singleton,
    hcC, hcP, false_or] using hmem

/-- Exchanging the first southwest point with a high second-block point moves
that column past the second southwest column and preserves both low rows. -/
theorem seamOneStep_high_first {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (hx : (seamSouthwestColumns x.val.val).card = 2)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (x.val.val C).val)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C)) :
    r.left = C ∧ r.right = seamComplementFirst x.val ∧
      seamComplementSecond x.val < C ∧
      seamComplementFirst y.val = seamComplementSecond x.val ∧
      seamComplementSecond y.val = C ∧
      y.val.val (seamComplementSecond x.val) = x.val.val (seamComplementFirst x.val) ∧
      y.val.val C = x.val.val (seamComplementSecond x.val) := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hCp : C ≠ seamComplementFirst x.val := by intro h; rw [h] at hCv; omega
  have hCq : C ≠ seamComplementSecond x.val := by intro h; rw [h] at hCv; omega
  have hsets := oneStep_southwest_high_swap x y r _ _ C
    (seamComplement_southwest_eq_pair_of_card_two x.val hx)
    (seamComplementFirst_ne_second x.val) hCn hCv hsides
  have hCmap : (seamComplementPartner y.val).val C = x.val.val (seamComplementFirst x.val) := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hr, r.map_right, hl]
    · rw [← hl, r.map_left, hr]
  have hQmap : (seamComplementPartner y.val).val (seamComplementSecond x.val) =
      x.val.val (seamComplementSecond x.val) := by
    apply r.map_of_ne
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hl]; exact (seamComplementFirst_ne_second x.val).symm
      · rw [hl]; exact hCq.symm
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hr]; exact hCq.symm
      · rw [hr]; exact (seamComplementFirst_ne_second x.val).symm
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hQC : seamComplementSecond x.val < C := by
    by_contra h
    have hCQ : C < seamComplementSecond x.val := lt_of_le_of_ne (le_of_not_gt h) hCq
    have hf := seamShortLift_first_of_pair y.val C (seamComplementSecond x.val) hsets hCQ
    have hs := seamShortLift_second_of_pair y.val C (seamComplementSecond x.val) hsets hCQ
    have hh := seamMatchingTarget_first_gt_second y
    rw [hf, hs, hQmap, hCmap] at hh
    omega
  have hsets' : seamSouthwestColumns y.val.val = {seamComplementSecond x.val, C} := by
    rw [hsets, Finset.pair_comm]
  have hfirst := seamShortLift_first_of_pair y.val _ _ hsets' hQC
  have hsecond := seamShortLift_second_of_pair y.val _ _ hsets' hQC
  have hyQ : y.val.val (seamComplementSecond x.val) = x.val.val (seamComplementFirst x.val) := by
    rw [← hsecond, seamComplementPartner_apply_second, hfirst] at hCmap
    exact hCmap
  have hyC : y.val.val C = x.val.val (seamComplementSecond x.val) := by
    rw [← hfirst, seamComplementPartner_apply_first, hsecond, hfirst] at hQmap
    exact hQmap
  have hsides' : r.left = C ∧ r.right = seamComplementFirst x.val := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exfalso
      apply (isEmpty_iff_forall_notMem_cIoo r).mp he (seamComplementSecond x.val)
      · rw [Grid.mem_cIoo, hl, hr, if_pos (by omega)]
        exact ⟨hCp.symm, hpq, hQC⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hl, hr, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, hsource, by omega⟩
    · exact ⟨hl, hr⟩
  exact ⟨hsides'.1, hsides'.2, hQC, hfirst, hsecond, hyQ, hyC⟩

/-- Exchanging the second southwest point with a high second-block point moves
that column before the first southwest column and preserves both low rows. -/
theorem seamOneStep_high_second {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (hx : (seamSouthwestColumns x.val.val).card = 2)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (x.val.val C).val)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C)) :
    r.left = seamComplementSecond x.val ∧ r.right = C ∧
      C < seamComplementFirst x.val ∧
      seamComplementFirst y.val = C ∧
      seamComplementSecond y.val = seamComplementFirst x.val ∧
      y.val.val C = x.val.val (seamComplementFirst x.val) ∧
      y.val.val (seamComplementFirst x.val) = x.val.val (seamComplementSecond x.val) := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hCp : C ≠ seamComplementFirst x.val := by intro h; rw [h] at hCv; omega
  have hCq : C ≠ seamComplementSecond x.val := by intro h; rw [h] at hCv; omega
  have hsets := oneStep_southwest_high_swap x y r _ _ C
    (by rw [seamComplement_southwest_eq_pair_of_card_two x.val hx, Finset.pair_comm])
    (seamComplementFirst_ne_second x.val).symm hCn hCv hsides
  have hCmap : (seamComplementPartner y.val).val C = x.val.val (seamComplementSecond x.val) := by
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hr, r.map_right, hl]
    · rw [← hl, r.map_left, hr]
  have hPmap : (seamComplementPartner y.val).val (seamComplementFirst x.val) =
      x.val.val (seamComplementFirst x.val) := by
    apply r.map_of_ne
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hl]; exact seamComplementFirst_ne_second x.val
      · rw [hl]; exact hCp.symm
    · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hr]; exact hCp.symm
      · rw [hr]; exact seamComplementFirst_ne_second x.val
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hCP : C < seamComplementFirst x.val := by
    by_contra h
    have hPC : seamComplementFirst x.val < C :=
      lt_of_le_of_ne (le_of_not_gt h) hCp.symm
    have hsets' : seamSouthwestColumns y.val.val = {seamComplementFirst x.val, C} := by
      rw [hsets, Finset.pair_comm]
    have hf := seamShortLift_first_of_pair y.val _ _ hsets' hPC
    have hs := seamShortLift_second_of_pair y.val _ _ hsets' hPC
    have hh := seamMatchingTarget_first_gt_second y
    rw [hf, hs, hCmap, hPmap] at hh
    omega
  have hfirst := seamShortLift_first_of_pair y.val _ _ hsets hCP
  have hsecond := seamShortLift_second_of_pair y.val _ _ hsets hCP
  have hyC : y.val.val C = x.val.val (seamComplementFirst x.val) := by
    rw [← hsecond, seamComplementPartner_apply_second, hfirst, hsecond] at hPmap
    exact hPmap
  have hyP : y.val.val (seamComplementFirst x.val) = x.val.val (seamComplementSecond x.val) := by
    rw [← hfirst, seamComplementPartner_apply_first, hsecond] at hCmap
    exact hCmap
  have hsides' : r.left = seamComplementSecond x.val ∧ r.right = C := by
    rcases hsides with hh | ⟨hr, hl⟩
    · exact hh
    · exfalso
      apply (isEmpty_iff_forall_notMem_cIoo r).mp he (seamComplementFirst x.val)
      · rw [Grid.mem_cIoo, hl, hr, if_pos (by omega)]
        exact ⟨hCq, hCP, hpq⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hl, hr, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr hsource⟩
  exact ⟨hsides'.1, hsides'.2, hCP, hfirst, hsecond, hyC, hyP⟩

end OnLeConjecture.KnotFloer.GridFull
