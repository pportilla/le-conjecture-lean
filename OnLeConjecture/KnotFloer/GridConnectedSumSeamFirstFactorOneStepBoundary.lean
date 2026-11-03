/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepFixedSecond

/-! # Boundary columns in one-step first-factor corrections

The surviving low-point exchanges force the selected southwest columns to
be the first and last columns of the second block. The two empty exterior
rectangles supply the boundary condition not forced by the internal edge.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem oneStep_high_before_first (x : SeamMatchingSource n m)
    (c : Fin (n + m + 1)) (hcn : n ≤ c.val) (hc : c < seamComplementFirst x.val) :
    n < (x.val.val c).val := by
  by_contra h
  have hm := (mem_seamSouthwestColumns x.val.val c).mpr ⟨hcn, by omega⟩
  have hh : seamComplementFirst x.val ≤ c := Finset.min'_le _ _ hm
  exact (not_lt_of_ge hh) hc

private theorem oneStep_high_after_second (x : SeamMatchingSource n m)
    (hx : (seamSouthwestColumns x.val.val).card = 2)
    (c : Fin (n + m + 1)) (hc : seamComplementSecond x.val < c) :
    n < (x.val.val c).val := by
  have hpq := seamComplementFirst_lt_second x.val
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  by_contra h
  have hm := (mem_seamSouthwestColumns x.val.val c).mpr ⟨by omega, by omega⟩
  rw [seamComplement_southwest_eq_pair_of_card_two x.val hx,
    Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h <;> have := congrArg Fin.val h <;> omega

/-- The low exchange at the first southwest column cannot pass any second-block
column before it, since such a point would lie in the internal rectangle. -/
theorem seamOneStep_low_first_cut {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (C : Fin (n + m + 1))
    (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C)) :
    seamComplementFirst x.val = seamRight n m 0 := by
  obtain ⟨hL, hR, hrow, _, _, _, _, _⟩ := seamOneStep_low_first r he C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  apply Fin.ext
  change (seamComplementFirst x.val).val = n + 0
  by_contra h
  let T := seamRight n m 0
  have hT : T.val = n := by simp [T]
  have hTP : T < seamComplementFirst x.val := by change T.val < _; omega
  have hhigh := oneStep_high_before_first x T (by omega) hTP
  apply (isEmpty_iff_forall_notMem_cIoo r).mp he T
  · rw [Grid.mem_cIoo, hL, hR, if_pos (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hTP⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, hL, hR, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩

/-- With two southwest points, a low exchange at the second cannot leave a
later column, since its high row would lie in the internal rectangle. -/
theorem seamOneStep_low_second_last {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (hx : (seamSouthwestColumns x.val.val).card = 2)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C)) :
    seamComplementSecond x.val = Fin.last (n + m) := by
  obtain ⟨hL, hR, hrow, _, _, _, _, _⟩ := seamOneStep_low_second r he C hCn hCv hsides
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  apply Fin.ext
  change (seamComplementSecond x.val).val = n + m
  by_contra h
  let T : Fin (n + m + 1) := Fin.last (n + m)
  have hT : T.val = n + m := rfl
  have hQ := (seamComplementSecond x.val).isLt
  have hQT : seamComplementSecond x.val < T := by change _ < T.val; omega
  have hhigh := oneStep_high_after_second x hx T hQT
  apply (isEmpty_iff_forall_notMem_cIoo r).mp he T
  · rw [Grid.mem_cIoo, hL, hR, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hQT⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, hL, hR, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩

/-- The two wrapping exterior rectangles also force the last southwest column
in the first-southwest low exchange to be the final full-grid column. -/
theorem seamOneStep_same_second_low_first_last
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C)) :
    seamComplementSecond x.val = Fin.last (n + m) := by
  obtain ⟨hrL, hrR, hrow, hYfirst, hYsecond, hyP, hyQ, _⟩ :=
    seamOneStep_low_first r hr C hCn hCv hsides
  obtain ⟨heR, hfR, hAeq, _⟩ :=
    seamOneStep_same_second_low_first_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have heQ := seamMatchingEntry_left_eq_second_of_right_lt (u, z) x e he heR
  have hfQ := (seamMatchingExit_left_eq_second_of_right_lt (v, z) y f hf hfR).trans hYsecond
  obtain ⟨heTop, heBot, heHigh⟩ :
      e.top = x.val.val (seamComplementFirst x.val) ∧
      e.bottom = x.val.val e.right ∧ n < e.bottom.val := by
    rcases seamMatchingEntry_endpoints (u, z) x e he with h | h
    · have hh := congrArg Fin.val h.2.1; omega
    · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hhighA : n < (x.val.val e.right).val := by rwa [heBot] at heHigh
  have hyA := seamOneStep_low_high_point r
    (by simpa only [bottom_def, hrL] using hCv)
    (by simpa only [top_def, hrR] using hp.2) e.right heR hhighA
  apply Fin.ext
  change (seamComplementSecond x.val).val = n + m
  by_contra h
  let T : Fin (n + m + 1) := Fin.last (n + m)
  have hT : T.val = n + m := rfl
  have hQ := (seamComplementSecond x.val).isLt
  have hQT : seamComplementSecond x.val < T := by change _ < T.val; omega
  have hhigh := oneStep_high_after_second x (seamMatchingEntry_southwest_card (u, z) x e) T hQT
  have hTP : T ≠ seamComplementFirst x.val := by intro hh; have := congrArg Fin.val hh; omega
  have hTQ : T ≠ seamComplementSecond x.val := hQT.ne.symm
  have hTA : T ≠ e.right := by intro hh; have := congrArg Fin.val hh; omega
  have hTC : T ≠ C := by intro hh; have := congrArg Fin.val hh; omega
  have hpx : (seamComplementPartner x.val).val T = x.val.val T := by
    change x.val.val.swapColumns _ _ T = _
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hTP hTQ]
  have hpy : (seamComplementPartner y.val).val T = y.val.val T := by
    change y.val.val.swapColumns (seamComplementFirst y.val) (seamComplementSecond y.val) T = _
    rw [hYfirst, hYsecond, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hTP hTQ]
  have hVT : seamState u z T = x.val.val T := by
    have hh := e.map_of_ne T (by rw [heQ]; exact hTQ) hTA
    exact hh.symm.trans hpx
  have hYT : y.val.val T = x.val.val T := by
    have hh := r.map_of_ne T (by rw [hrL]; exact hTC) (by rw [hrR]; exact hTP)
    rwa [hpy] at hh
  have hneq : (x.val.val T).val ≠ (x.val.val e.right).val := by
    intro hh
    exact hTA (x.val.val.toPerm.injective (Fin.ext hh))
  rcases lt_or_gt_of_ne hneq with hbelow | habove
  · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf T
    · rw [Grid.mem_cIoo, hfQ, ← hAeq, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hQT⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hfQ, ← hAeq, hyQ, hyA, hYT,
        if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hbelow⟩
  · apply (isEmpty_iff_forall_notMem_cIoo e).mp he T
    · rw [Grid.mem_cIoo, heQ, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hQT⟩
    · rw [Grid.mem_cIoo, heBot, heTop, hVT, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl habove⟩

/-- The two nonwrapping exterior rectangles force the first southwest column
in the second-southwest low exchange to be the shared full-grid column. -/
theorem seamOneStep_same_second_low_second_cut
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C)) :
    seamComplementFirst x.val = seamRight n m 0 := by
  obtain ⟨hrL, hrR, hrow, hYfirst, hYsecond, hyP, hyQ, _⟩ :=
    seamOneStep_low_second r hr C hCn hCv hsides
  obtain ⟨heL, hfL, hAeq, _⟩ :=
    seamOneStep_same_second_low_second_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have heP := seamMatchingEntry_right_eq_first_of_left_lt (u, z) x e he heL
  have hfP := (seamMatchingExit_right_eq_first_of_left_lt (v, z) y f hf hfL).trans hYfirst
  obtain ⟨heBot, heTop, heHigh⟩ :
      e.bottom = x.val.val (seamComplementSecond x.val) ∧
      e.top = x.val.val e.left ∧ n < e.top.val := by
    rcases seamMatchingEntry_endpoints (u, z) x e he with h | h
    · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · have hh := congrArg Fin.val h.2.1; omega
  have hhighA : n < (x.val.val e.left).val := by rwa [heTop] at heHigh
  have hyA := seamOneStep_low_high_point r
    (by simpa only [bottom_def, hrL] using hq.2)
    (by simpa only [top_def, hrR] using hCv) e.left heL hhighA
  apply Fin.ext
  change (seamComplementFirst x.val).val = n + 0
  by_contra h
  let T := seamRight n m 0
  have hT : T.val = n := by simp [T]
  have hTP : T < seamComplementFirst x.val := by change T.val < _; omega
  have hhigh := oneStep_high_before_first x T (by omega) hTP
  have hTP' : T ≠ seamComplementFirst x.val := hTP.ne
  have hTQ : T ≠ seamComplementSecond x.val := by intro hh; have := congrArg Fin.val hh; omega
  have hTA : T ≠ e.left := by intro hh; have := congrArg Fin.val hh; omega
  have hTC : T ≠ C := by intro hh; have := congrArg Fin.val hh; omega
  have hpx : (seamComplementPartner x.val).val T = x.val.val T := by
    change x.val.val.swapColumns _ _ T = _
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hTP' hTQ]
  have hpy : (seamComplementPartner y.val).val T = y.val.val T := by
    change y.val.val.swapColumns (seamComplementFirst y.val) (seamComplementSecond y.val) T = _
    rw [hYfirst, hYsecond, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hTP' hTQ]
  have hVT : seamState u z T = x.val.val T := by
    have hh := e.map_of_ne T hTA (by rw [heP]; exact hTP')
    exact hh.symm.trans hpx
  have hYT : y.val.val T = x.val.val T := by
    have hh := r.map_of_ne T (by rw [hrL]; exact hTQ) (by rw [hrR]; exact hTC)
    rwa [hpy] at hh
  have hneq : (x.val.val T).val ≠ (x.val.val e.left).val := by
    intro hh
    exact hTA (x.val.val.toPerm.injective (Fin.ext hh))
  rcases lt_or_gt_of_ne hneq with hbelow | habove
  · apply (isEmpty_iff_forall_notMem_cIoo e).mp he T
    · rw [Grid.mem_cIoo, heP, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hTP⟩
    · rw [Grid.mem_cIoo, heBot, heTop, hVT, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hbelow⟩
  · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf T
    · rw [Grid.mem_cIoo, hfP, ← hAeq, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hTP⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hfP, ← hAeq, hyP, hyA, hYT,
        if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl habove⟩

/-- The first-southwest low case necessarily comes from the second factor's
zero row in column zero. -/
theorem seamOneStep_same_second_low_first_zero
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C)) : z 0 = 0 := by
  have hcut := seamOneStep_low_first_cut r hr C hCn hCv hsides
  have hor := seamOneStep_same_second_low_first_orientations
    u v z x y e r f he hr hf C hCn hCv hsides
  have heQ := seamMatchingEntry_left_eq_second_of_right_lt (u, z) x e he hor.1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have heNot : ¬ e.left.val < n := by rw [heQ]; omega
  have hm : seamRight n m 0 ∈ seamSouthwestColumns (seamState u z) := by
    rw [seamOneStep_entry_zero_column (u, z) x e he, if_neg heNot, hcut]
    exact Finset.mem_singleton_self _
  exact (seamState_right_row_le_iff u z 0).mp ((mem_seamSouthwestColumns _ _).mp hm).2

/-- The second-southwest low case necessarily comes from the second factor's
zero row in its last column. -/
theorem seamOneStep_same_second_low_second_zero
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C)) : z (Fin.last m) = 0 := by
  have hlast := seamOneStep_low_second_last r hr (seamMatchingEntry_southwest_card (u, z) x e)
    C hCn hCv hsides
  have hor := seamOneStep_same_second_low_second_orientations
    u v z x y e r f he hr hf C hCn hCv hsides
  have hm : seamRight n m (Fin.last m) ∈ seamSouthwestColumns (seamState u z) := by
    rw [seamOneStep_entry_zero_column (u, z) x e he, if_pos hor.1, hlast]
    have hh : seamRight n m (Fin.last m) = Fin.last (n + m) := Fin.ext rfl
    rw [hh]
    exact Finset.mem_singleton_self _
  exact (seamState_right_row_le_iff u z (Fin.last m)).mp ((mem_seamSouthwestColumns _ _).mp hm).2

/-- The selected southwest columns and the second-factor zero position of any
complete one-step correction with fixed second factor are forced to the boundaries. -/
theorem seamFirstFactorOneStep_boundaries
    (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (hne : x ≠ y) (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) :
    seamComplementFirst x.val = seamRight n m 0 ∧
      seamComplementSecond x.val = Fin.last (n + m) ∧
      (z 0 = 0 ∨ z (Fin.last m) = 0) := by
  obtain ⟨C, hCn, hCv, hsides⟩ :=
    seamFirstFactorOneStep_internal_low u v z x y e r f hne he hr hf
  rcases hsides with h | h
  · have hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
        (r.right = seamComplementFirst x.val ∧ r.left = C) := Or.inr ⟨h.2, h.1⟩
    exact ⟨seamOneStep_low_first_cut r hr C hCn hCv hsides,
      seamOneStep_same_second_low_first_last u v z x y e r f he hr hf C hCn hCv hsides,
      Or.inl (seamOneStep_same_second_low_first_zero u v z x y e r f he hr hf C hCn hCv hsides)⟩
  · have hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
        (r.right = seamComplementSecond x.val ∧ r.left = C) := Or.inl h
    exact ⟨seamOneStep_same_second_low_second_cut u v z x y e r f he hr hf C hCn hCv hsides,
      seamOneStep_low_second_last r hr (seamMatchingEntry_southwest_card (u, z) x e)
        C hCn hCv hsides,
      Or.inr (seamOneStep_same_second_low_second_zero u v z x y e r f he hr hf C hCn hCv hsides)⟩

end OnLeConjecture.KnotFloer.GridFull
