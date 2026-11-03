/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTwoStepEntryBarrier
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorShortLift

/-!
# Retained endpoints of a two-transition birth-death path

The retained zero-preimage column determines which southwest column
survives each outer rectangle. When the second factor is fixed, a
birth-death path has equal entry and exit orientations. This file does
not infer a bound on arbitrary path lengths from finite diagnostics.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A first-block-left entry retains the second selected southwest column. -/
theorem seamTwoStep_entry_southwest_of_left (p : SeamRetainedIndex n m)
    (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : e.IsEmpty) (hl : e.left.val < n) :
    seamComplementSecond x.val = seamRight n m (p.2.toPerm.symm 0) := by
  have hp := seamMatchingEntry_right_eq_first_of_left_lt p x e he hl
  have hn := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hh := e.map_of_ne (seamComplementSecond x.val)
    (by intro h; have := congrArg Fin.val h; omega)
    (by rw [hp]; exact (seamComplementFirst_ne_second x.val).symm)
  rw [seamComplementPartner_apply_second] at hh
  have hc : seamComplementSecond x.val ∈ seamSouthwestColumns (seamState p.1 p.2) := by
    apply (mem_seamSouthwestColumns _ _).mpr
    refine ⟨hn.1, ?_⟩
    rw [← hh]
    exact ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).2
  simpa only [seamState_southwest_singleton, Finset.mem_singleton] using hc

/-- A first-block-right entry retains the first selected southwest column. -/
theorem seamTwoStep_entry_southwest_of_right (p : SeamRetainedIndex n m)
    (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : e.IsEmpty) (hr : e.right.val < n) :
    seamComplementFirst x.val = seamRight n m (p.2.toPerm.symm 0) := by
  have hq := seamMatchingEntry_left_eq_second_of_right_lt p x e he hr
  have hn := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hh := e.map_of_ne (seamComplementFirst x.val)
    (by rw [hq]; exact seamComplementFirst_ne_second x.val)
    (by intro h; have := congrArg Fin.val h; omega)
  rw [seamComplementPartner_apply_first] at hh
  have hc : seamComplementFirst x.val ∈ seamSouthwestColumns (seamState p.1 p.2) := by
    apply (mem_seamSouthwestColumns _ _).mpr
    refine ⟨hn.1, ?_⟩
    rw [← hh]
    exact ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).2
  simpa only [seamState_southwest_singleton, Finset.mem_singleton] using hc

/-- A first-block-left exit retains the second selected southwest column. -/
theorem seamTwoStep_exit_southwest_of_left (p : SeamRetainedIndex n m)
    (x : SeamMatchingSource n m)
    (f : GridRectangleBetween x.val.val (seamState p.1 p.2))
    (hf : f.IsEmpty) (hl : f.left.val < n) :
    seamComplementSecond x.val = seamRight n m (p.2.toPerm.symm 0) := by
  have hp := seamMatchingExit_right_eq_first_of_left_lt p x f hf hl
  have hn := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hh := f.map_of_ne (seamComplementSecond x.val)
    (by intro h; have := congrArg Fin.val h; omega)
    (by rw [hp]; exact (seamComplementFirst_ne_second x.val).symm)
  have hc : seamComplementSecond x.val ∈ seamSouthwestColumns (seamState p.1 p.2) := by
    apply (mem_seamSouthwestColumns _ _).mpr
    exact ⟨hn.1, by rw [hh]; exact hn.2⟩
  simpa only [seamState_southwest_singleton, Finset.mem_singleton] using hc

/-- A first-block-right exit retains the first selected southwest column. -/
theorem seamTwoStep_exit_southwest_of_right (p : SeamRetainedIndex n m)
    (x : SeamMatchingSource n m)
    (f : GridRectangleBetween x.val.val (seamState p.1 p.2))
    (hf : f.IsEmpty) (hr : f.right.val < n) :
    seamComplementFirst x.val = seamRight n m (p.2.toPerm.symm 0) := by
  have hq := seamMatchingExit_left_eq_second_of_right_lt p x f hf hr
  have hn := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hh := f.map_of_ne (seamComplementFirst x.val)
    (by rw [hq]; exact seamComplementFirst_ne_second x.val)
    (by intro h; have := congrArg Fin.val h; omega)
  have hc : seamComplementFirst x.val ∈ seamSouthwestColumns (seamState p.1 p.2) := by
    apply (mem_seamSouthwestColumns _ _).mpr
    exact ⟨hn.1, by rw [hh]; exact hn.2⟩
  simpa only [seamState_southwest_singleton, Finset.mem_singleton] using hc

/-- Equal first-block sides make the two internal high row endpoints agree. -/
theorem seamTwoStep_inner_high_eq (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) (hsame : r.left = t.left) :
    t.bottom = r.top := by
  have hor := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  have hv := r.map_left
  rw [seamComplementPartner_firstBlock_apply y.val r.left hor.1] at hv
  simpa only [bottom_def, top_def, ← hsame] using hv

/-- When the internal first-block sides agree, emptiness forces their other side to the seam. -/
theorem seamTwoStep_inner_cut_of_same_left (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) (hsame : r.left = t.left) :
    r.right.val = n := by
  have hor := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  have hcols := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hB := seamMatchingBirth_nonwrap x y r hr hb hor.1
  have hC := hB.1
  have hCP := hB.2.1
  have hpq := seamComplementFirst_lt_second x.val
  have hfirst := hcols.2.1
  have hsecond := hcols.2.2.1
  have hhigh : n < r.top.val := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.2
    · omega
  have hbottom : r.bottom.val ≤ n := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.1
    · omega
  have htlow : t.top.val ≤ n := by
    rcases seamMatchingDeath_ranges t hd with h | h
    · exact h.2.2.1
    · omega
  by_contra hne
  have hnC : n < r.right.val := by omega
  let c := seamLeft n m (Fin.last n)
  have hcv : c.val = n := rfl
  have hcA : c ≠ r.left := by intro h; have := congrArg Fin.val h; omega
  have hcC : c ≠ r.right := by intro h; have := congrArg Fin.val h; omega
  have hcP : c ≠ seamComplementFirst x.val := by
    intro h; have := congrArg Fin.val h; omega
  have hchigh : n < (x.val.val c).val := by
    by_contra hh
    have hsw : c ∈ seamSouthwestColumns x.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by omega⟩
    have hmin : seamComplementFirst x.val ≤ c := Finset.min'_le _ _ hsw
    omega
  have hvc : y.val.val c = x.val.val c := by
    have hh := r.map_of_ne c hcA hcC
    change y.val.val.swapColumns (seamComplementFirst y.val)
      (seamComplementSecond y.val) c = _ at hh
    rw [GridState.swapColumns_apply, hfirst, hsecond,
      Equiv.swap_apply_of_ne_of_ne hcC hcP] at hh
    exact hh
  have hc : c ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨r.left_ne_right, by omega, by omega⟩
  have htB := seamTwoStep_inner_high_eq x y z r t hr ht hb hd hx hsame
  have hvne : x.val.val c ≠ r.top := by
    intro hh
    exact hcC (x.val.val.toPerm.injective hh)
  by_cases hv : (x.val.val c).val < r.top.val
  · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr c hc
    rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨r.bottom_ne_top, by omega, hv⟩
  · have hvgt : r.top.val < (x.val.val c).val := by
      have hval : (x.val.val c).val ≠ r.top.val := fun hh => hvne (Fin.ext hh)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo t).mp ht c
    · rwa [← hsame, ← hcols.1]
    · rw [hvc, htB, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hvgt⟩

/-- Away from the four involved columns, the two internal transitions preserve every state value. -/
theorem seamTwoStep_values_away (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) (hsame : r.left = t.left)
    (c : Fin (n + m + 1)) (hA : c ≠ r.left) (hC : c ≠ r.right)
    (hP : c ≠ seamComplementFirst x.val) (hQ : c ≠ seamComplementSecond x.val) :
    z.val.val c = x.val.val c := by
  have hs := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have h₁ := r.map_of_ne c hA hC
  change y.val.val.swapColumns (seamComplementFirst y.val)
    (seamComplementSecond y.val) c = _ at h₁
  rw [GridState.swapColumns_apply, hs.2.1, hs.2.2.1,
    Equiv.swap_apply_of_ne_of_ne hC hP] at h₁
  have h₂ := t.map_of_ne c (by rwa [← hsame]) (by rwa [← hs.1])
  change z.val.val.swapColumns (seamComplementFirst z.val)
    (seamComplementSecond z.val) c = _ at h₂
  rw [GridState.swapColumns_apply, hs.2.2.2.1, hs.2.2.2.2.1,
    Equiv.swap_apply_of_ne_of_ne hP hQ] at h₂
  exact h₂.trans h₁

/-- Equal internal first-block sides preserve the northeast column set. -/
theorem seamTwoStep_northeast_eq_of_same_left (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) (hsame : r.left = t.left) :
    seamNortheastColumns z.val.val = seamNortheastColumns x.val.val := by
  have hor := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  have hs := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hB := seamMatchingBirth_nonwrap x y r hr hb hor.1
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hlowX : (x.val.val r.left).val ≤ n := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.1
    · omega
  have hZA : z.val.val r.left = x.val.val (seamComplementFirst x.val) := by
    have hh := t.map_left
    rw [seamComplementPartner_firstBlock_apply z.val t.left hor.2, ← hsame, ← hs.1] at hh
    rw [← hs.2.1, hB.2.2.2.2.2] at hh
    exact hh
  ext c
  simp only [mem_seamNortheastColumns]
  by_cases hcn : c.val < n
  · simp only [hcn, true_and]
    by_cases hcA : c = r.left
    · subst c
      rw [hZA]
      omega
    · rw [seamTwoStep_values_away x y z r t hr ht hb hd hx hsame c hcA
        (by intro h; have := congrArg Fin.val h; have hn := hB.1; omega)
        (by intro h; have := congrArg Fin.val h; omega)
        (by intro h; have := congrArg Fin.val h; omega)]
  · simp only [hcn, false_and]

section Complete
variable (p q : SeamRetainedIndex n m) (x y z : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (f : GridRectangleBetween z.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns y.val.val).card = 2)

include e f hr ht hmid in
/-- The complete local path supplies the exact hypotheses of the birth-death column theorem. -/
theorem seamTwoStep_complete_selected_columns :
    seamComplementFirst z.val = seamComplementFirst x.val ∧
      seamComplementSecond z.val = seamComplementSecond x.val := by
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hcols := seamTwoStep_birth_death_columns x y z r t hr ht hb hd
    (seamMatchingEntry_southwest_card p x e)
  exact ⟨hcols.2.2.2.1, hcols.2.2.2.2.1⟩

include he hr ht hf hmid in
/-- Fixing the second factor forces equal orientations of entry and exit in this local path. -/
theorem seamTwoStep_same_second_orientations (hpq : p.2 = q.2) :
    (e.left.val < n ∧ f.left.val < n) ∨ (e.right.val < n ∧ f.right.val < n) := by
  obtain ⟨hP, hQ⟩ := seamTwoStep_complete_selected_columns p q x y z e r t f hr ht hmid
  have heR := seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
    (seamComplementPartner x.val).property e
  have hfR := seamLeavingRectangle_ranges (seamState_mem_pairSector q.1 q.2) z.val.property f
  rcases heR with heR | heR <;> rcases hfR with hfR | hfR
  · exact Or.inl ⟨heR.1, hfR.1⟩
  · have hs := seamTwoStep_entry_southwest_of_left p x e he heR.1
    have htgt := seamTwoStep_exit_southwest_of_right q z f hf hfR.1
    rw [hP, ← hpq] at htgt
    exact False.elim ((seamComplementFirst_ne_second x.val) (htgt.trans hs.symm))
  · have hs := seamTwoStep_entry_southwest_of_right p x e he heR.1
    have htgt := seamTwoStep_exit_southwest_of_left q z f hf hfR.1
    rw [hQ, ← hpq] at htgt
    exact False.elim ((seamComplementFirst_ne_second x.val) (hs.trans htgt.symm))
  · exact Or.inr ⟨heR.1, hfR.1⟩

include he hr ht hf hmid in
/-- The independently proved entry barrier selects the wrapping outer orientation. -/
theorem seamTwoStep_complete_outer_right (hpq : p.2 = q.2) :
    e.right.val < n ∧ f.right.val < n := by
  have hor := seamTwoStep_same_second_orientations p q x y z e r t f he hr ht hf hmid hpq
  have hn := seamTwoStep_entry_not_left p q hpq x y z e r t f he hr ht hf hmid
  exact hor.resolve_left (fun h => hn h.1)

include he hr ht hf hmid in
/-- Preserving the second factor forces the two internal first-block endpoints to agree. -/
theorem seamTwoStep_complete_inner_left_eq (hpq : p.2 = q.2) : r.left = t.left := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hx := seamMatchingEntry_southwest_card p x e
  have hor := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  have hc := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hB := seamMatchingBirth_nonwrap x y r hr hb hor.1
  have hCP := hB.2.1
  have hCQ := hCP.trans (seamComplementFirst_lt_second x.val)
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e he ho.1
  have hF := seamMatchingExit_left_eq_second_of_right_lt q z f hf ho.2
  rw [hc.2.2.2.2.1] at hF
  have hCe : r.right ≠ e.right := by
    intro h; have := congrArg Fin.val h; have hn := hB.1; omega
  have hCf : r.right ≠ f.right := by
    intro h; have := congrArg Fin.val h; have hn := hB.1; omega
  have hpC : seamState p.1 p.2 r.right = x.val.val r.right := by
    have hv := e.map_of_ne r.right (by rw [hE]; exact hCQ.ne) hCe
    change x.val.val.swapColumns (seamComplementFirst x.val)
      (seamComplementSecond x.val) r.right = _ at hv
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hCP.ne hCQ.ne] at hv
    exact hv.symm
  have hqC : seamState q.1 q.2 r.right = z.val.val r.right :=
    f.map_of_ne r.right (by rw [hF]; exact hCQ.ne) hCf
  have hhigh : n < (seamState p.1 p.2 r.right).val := by
    rw [hpC]
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.2
    · omega
  have hv := seamRetained_same_second_high p q hpq r.right hB.1 hhigh
  rw [hpC, hqC] at hv
  have hleft := r.map_left
  rw [seamComplementPartner_firstBlock_apply y.val r.left hor.1] at hleft
  have hright := t.map_right
  change z.val.val.swapColumns (seamComplementFirst z.val)
    (seamComplementSecond z.val) t.right = y.val.val t.left at hright
  rw [GridState.swapColumns_apply, ← hc.1, hc.2.2.2.1, hc.2.2.2.2.1,
    Equiv.swap_apply_of_ne_of_ne hCP.ne hCQ.ne] at hright
  exact y.val.val.toPerm.injective (hleft.trans (hv.trans hright))

include he hr ht hf hmid in
/-- The internal rectangle sides at or beyond the cut are exactly the seam column. -/
theorem seamTwoStep_complete_inner_cut (hpq : p.2 = q.2) : r.right.val = n ∧ t.right.val = n := by
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hx := seamMatchingEntry_southwest_card p x e
  have hc := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hleft := seamTwoStep_complete_inner_left_eq p q x y z e r t f he hr ht hf hmid hpq
  have hcut := seamTwoStep_inner_cut_of_same_left x y z r t hr ht hb hd hx hleft
  exact ⟨hcut, congrArg Fin.val hc.1.symm |>.trans hcut⟩

include he hr ht hf hmid in
/-- The outer first-block endpoints agree after the birth and death at the common inner side. -/
theorem seamTwoStep_complete_outer_right_eq (hpq : p.2 = q.2) : e.right = f.right := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hx := seamMatchingEntry_southwest_card p x e
  have hleft := seamTwoStep_complete_inner_left_eq p q x y z e r t f he hr ht hf hmid hpq
  have hNE := seamTwoStep_northeast_eq_of_same_left x y z r t hr ht hb hd hx hleft
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e he ho.1
  have hF := seamMatchingExit_left_eq_second_of_right_lt q z f hf ho.2
  have hnX := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hnZ := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem z.val)).1
  rw [seamMatchingEntry_northeast_eq_singleton p x e,
    seamMatchingExit_northeast_eq_singleton q z f,
    if_neg (by rw [hF]; omega), if_neg (by rw [hE]; omega)] at hNE
  exact (Finset.singleton_inj.mp hNE).symm

end Complete
end OnLeConjecture.KnotFloer.GridFull
