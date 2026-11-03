/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamBirthDeathGeneral
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepFixedSecond
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTwoStepRecovery

/-!
# Rectangle barriers after an internal birth-death peak

The statements use actual empty rectangles and the specified changes in
northeast counts. They do not infer a universal path bound from finite
computations.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The column inserted and then removed at a peak again has a high row. -/
theorem seamPeak_removed_column_high (a b c : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (hr : r.IsEmpty) (hs : s.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1) :
    n < (c.val.val r.right).val := by
  have ho := seamMatchingBirthDeath_nonwrap a b c r s hr hs hb hd
  have hB := seamMatchingBirth_nonwrap a b r hr hb ho.1
  have hc := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  by_contra h
  have hmem : r.right ∈ seamSouthwestColumns c.val.val :=
    (mem_seamSouthwestColumns _ _).mpr ⟨hB.1, by omega⟩
  rw [hc.2.2.2.2.2] at hmem
  have hmin := Finset.min'_le _ r.right hmem
  change seamComplementFirst a.val ≤ r.right at hmin
  exact (not_le_of_gt hB.2.1) hmin

/-- A peak cannot be followed by a neutral exchange of the first southwest
point with a low first-block point. The removed column obstructs that rectangle. -/
theorem seamPeak_then_low_first_impossible (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : L.val < n) (hLv : (c.val.val L).val ≤ n)
    (hside : (t.left = seamComplementFirst c.val ∧ t.right = L) ∨
      (t.right = seamComplementFirst c.val ∧ t.left = L)) : False := by
  have ho := seamMatchingBirthDeath_nonwrap a b c r s hr hs hb hd
  have hB := seamMatchingBirth_nonwrap a b r hr hb ho.1
  have hc := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  have hhigh := seamPeak_removed_column_high a b c r s hr hs hb hd
  obtain ⟨htL, htP, hrow, _, _, _, _, _⟩ := seamOneStep_low_first t ht L hLn hLv hside
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem c.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem c.val)
  have horder := c.property
  change (c.val.val (seamComplementFirst c.val)).val <
    (c.val.val (seamComplementSecond c.val)).val at horder
  apply (isEmpty_iff_forall_notMem_cIoo t).mp ht r.right
  · rw [Grid.mem_cIoo, htL, htP, hc.2.2.2.1, if_pos (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega,
      by omega, hB.2.1⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, htL, htP, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩

/-- A peak preserves right-block columns away from the inserted and selected columns. -/
theorem seamPeak_rightBlock_away (a b c : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (hr : r.IsEmpty) (hs : s.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1)
    (j : Fin (n + m + 1)) (hjn : n ≤ j.val) (hjC : j ≠ r.right)
    (hjP : j ≠ seamComplementFirst a.val) (hjQ : j ≠ seamComplementSecond a.val) :
    c.val.val j = a.val.val j := by
  have ho := seamMatchingBirthDeath_nonwrap a b c r s hr hs hb hd
  have hc := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  have hv := r.map_of_ne j (by intro hh; have := congrArg Fin.val hh; omega) hjC
  change b.val.val.swapColumns (seamComplementFirst b.val) (seamComplementSecond b.val) j = _ at hv
  rw [hc.2.1, hc.2.2.1, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hjC hjP] at hv
  have hw := s.map_of_ne j (by intro hh; have := congrArg Fin.val hh; omega)
    (by rw [← hc.1]; exact hjC)
  change c.val.val.swapColumns (seamComplementFirst c.val) (seamComplementSecond c.val) j = _ at hw
  rw [hc.2.2.2.1, hc.2.2.2.2.1, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hjP hjQ] at hw
  exact hw.trans hv

/-- With the retained second factor fixed, a peak cannot be followed by
an exchange of the first southwest point with a high right-block point. -/
theorem seamPeak_then_high_first_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : n ≤ L.val) (hLv : n < (c.val.val L).val)
    (hside : (t.left = seamComplementFirst c.val ∧ t.right = L) ∨
      (t.right = seamComplementFirst c.val ∧ t.left = L)) : False := by
  have hSWc : (seamSouthwestColumns c.val.val).card = 2 := by
    rw [seamSouthwestColumns_card]
    have ha := seamMatchingEntry_northeast_card (u, w) a e
    omega
  have hcols := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  obtain ⟨hL, hR, hQL, hDfirst, hDsecond, _, _⟩ :=
    seamOneStep_high_first t ht hSWc L hLn hLv hside
  rw [hcols.2.2.2.1] at hR
  rw [hcols.2.2.2.2.1] at hQL hDfirst
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hpq := seamComplementFirst_lt_second a.val
  have hPL := hpq.trans hQL
  have hmatch := seamOneStep_same_second_zero_column u v w a d e f he hf
  have heL : e.left.val < n := by
    by_contra hnot
    rw [if_neg hnot, hDfirst, hDsecond] at hmatch
    split_ifs at hmatch
    · have hh := congrArg Fin.val hmatch; omega
    · exact (seamComplementFirst_ne_second a.val) hmatch
  have hfL : ¬ f.left.val < n := by
    intro h
    rw [if_pos heL, if_pos h, hDsecond] at hmatch
    exact hQL.ne hmatch
  obtain ⟨heP, heTop, heHigh⟩ : e.right = seamComplementFirst a.val ∧
      e.top = a.val.val e.left ∧ n < e.top.val := by
    rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
    · exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · have hh := congrArg Fin.val h.2.1
      omega
  obtain ⟨hfR, hfC⟩ : f.right.val < n ∧ f.left = L := by
    rcases seamMatchingExit_endpoints (v, w) d f hf with h | h
    · exact False.elim (hfL h.1)
    · exact ⟨h.1, h.2.1.trans hDsecond⟩
  have hvP : seamState u w (seamComplementFirst a.val) = a.val.val e.left := by
    calc
      _ = e.top := by rw [← heP]; rfl
      _ = _ := heTop
  have hpD : (seamComplementPartner d.val).val (seamComplementFirst a.val) =
      d.val.val (seamComplementFirst a.val) := by
    change d.val.val.swapColumns (seamComplementFirst d.val)
      (seamComplementSecond d.val) (seamComplementFirst a.val) = _
    rw [hDfirst, hDsecond, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hpq.ne hPL.ne]
  have hdP : d.val.val (seamComplementFirst a.val) = c.val.val L := by
    rw [← hpD, ← hR, t.map_right, hL]
  have hwP : seamState v w (seamComplementFirst a.val) = c.val.val L := by
    rw [f.map_of_ne (seamComplementFirst a.val)
      (by rw [hfC]; exact hPL.ne)
      (by intro h; have := congrArg Fin.val h; omega), hdP]
  have hfixed := seamOneStep_same_second_high_value u v w (seamComplementFirst a.val) hp.1
    (by rw [← heP]; exact heHigh)
  have htail := seamMatchingBirthDeath_tail_apply a b c r s hr hs hb hd L hQL
  have hh : a.val.val e.left = a.val.val L := hvP.symm.trans (hfixed.trans (hwP.trans htail))
  have hc := congrArg Fin.val (a.val.val.toPerm.injective hh)
  omega

/-- In the second-southwest high case, preserving the second factor forces
the neutral move to use exactly the column inserted at the peak. -/
theorem seamPeak_then_high_second_column
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : n ≤ L.val) (hLv : n < (c.val.val L).val)
    (hside : (t.left = seamComplementSecond c.val ∧ t.right = L) ∨
      (t.right = seamComplementSecond c.val ∧ t.left = L)) :
    L = r.right ∧ e.right.val < n ∧ f.left.val < n ∧
      e.left = seamComplementSecond a.val ∧ f.right = L ∧
      e.bottom = a.val.val e.right ∧ n < e.bottom.val ∧
      c.val.val L = a.val.val e.right := by
  have hSWc : (seamSouthwestColumns c.val.val).card = 2 := by
    rw [seamSouthwestColumns_card]
    have ha := seamMatchingEntry_northeast_card (u, w) a e
    omega
  have hc := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  obtain ⟨hTQ, hTL, hLP, hDfirst, hDsecond, _, _⟩ :=
    seamOneStep_high_second t ht hSWc L hLn hLv hside
  rw [hc.2.2.2.2.1] at hTQ
  rw [hc.2.2.2.1] at hLP hDsecond
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hPQ := seamComplementFirst_lt_second a.val
  have hLQ := hLP.trans hPQ
  have hmatch := seamOneStep_same_second_zero_column u v w a d e f he hf
  have heL : ¬ e.left.val < n := by
    intro h
    rw [if_pos h, hDfirst, hDsecond] at hmatch
    split_ifs at hmatch
    · exact (seamComplementFirst_ne_second a.val).symm hmatch
    · have hh := congrArg Fin.val hmatch; omega
  have hfL : f.left.val < n := by
    by_contra h
    rw [if_neg heL, if_neg h, hDfirst] at hmatch
    exact hLP.ne hmatch.symm
  obtain ⟨heR, heQ, heBot, heHigh⟩ : e.right.val < n ∧
      e.left = seamComplementSecond a.val ∧
      e.bottom = a.val.val e.right ∧ n < e.bottom.val := by
    rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
    · exact False.elim (heL h.1)
    · exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hfC : f.right = L :=
    (seamMatchingExit_right_eq_first_of_left_lt (v, w) d f hf hfL).trans hDfirst
  have hvQ : seamState u w (seamComplementSecond a.val) = a.val.val e.right := by
    calc
      _ = e.bottom := by rw [← heQ]; rfl
      _ = _ := heBot
  have hpD : (seamComplementPartner d.val).val (seamComplementSecond a.val) =
      d.val.val (seamComplementSecond a.val) := by
    change d.val.val.swapColumns (seamComplementFirst d.val)
      (seamComplementSecond d.val) (seamComplementSecond a.val) = _
    rw [hDfirst, hDsecond, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hLQ.ne.symm hPQ.ne.symm]
  have hdQ : d.val.val (seamComplementSecond a.val) = c.val.val L := by
    rw [← hpD, ← hTQ, t.map_left, hTL]
  have hwQ : seamState v w (seamComplementSecond a.val) = c.val.val L := by
    rw [f.map_of_ne (seamComplementSecond a.val)
      (by intro h; have := congrArg Fin.val h; omega)
      (by rw [hfC]; exact hLQ.ne.symm), hdQ]
  have hfixed := seamOneStep_same_second_high_value u v w (seamComplementSecond a.val) hq.1
    (by rw [← heQ]; exact heHigh)
  have hvalue : c.val.val L = a.val.val e.right := (hvQ.symm.trans (hfixed.trans hwQ)).symm
  have heq : L = r.right := by
    by_contra hne
    have haway := seamPeak_rightBlock_away a b c r s hr hs hb hd L hLn hne hLP.ne hLQ.ne
    have hcol := a.val.val.toPerm.injective (hvalue.symm.trans haway)
    have hh := congrArg Fin.val hcol
    omega
  exact ⟨heq, heR, hfL, heQ, hfC, heBot, heHigh, hvalue⟩

/-- The remaining high-point exchange is incompatible with the outer empty rectangles. -/
theorem seamPeak_then_high_second_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : n ≤ L.val) (hLv : n < (c.val.val L).val)
    (hside : (t.left = seamComplementSecond c.val ∧ t.right = L) ∨
      (t.right = seamComplementSecond c.val ∧ t.left = L)) : False := by
  obtain ⟨hLC, heR, hfL, heQ, hfC, heBot, heHigh, hvalue⟩ :=
    seamPeak_then_high_second_column u v w a b c d e r s t f he hr hs ht hf hb hd L hLn hLv hside
  subst L
  have ho := seamMatchingBirthDeath_nonwrap a b c r s hr hs hb hd
  have hc := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  have hB := seamMatchingBirth_nonwrap a b r hr hb ho.1
  have hrows := seamMatchingBirthDeath_final_rows a b c r s hr hs hb hd
  have hSWc : (seamSouthwestColumns c.val.val).card = 2 := by
    rw [seamSouthwestColumns_card]
    have ha := seamMatchingEntry_northeast_card (u, w) a e
    omega
  obtain ⟨htQ, htC, hCP, hdP, hdQ, hdC, _⟩ :=
    seamOneStep_high_second t ht hSWc r.right hLn hLv hside
  rw [hc.2.2.2.2.1] at htQ
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hPQ := seamComplementFirst_lt_second a.val
  have hCQ := hB.2.1.trans hPQ
  have hrLow : r.bottom.val ≤ n := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.1
    · omega
  have hrHigh : n < r.top.val := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.2
    · omega
  have hAB : r.left ≠ e.right := by
    intro hh
    rw [heBot, ← hh] at heHigh
    change (a.val.val r.left).val ≤ n at hrLow
    omega
  have hAC : r.left ≠ r.right := r.left_ne_right
  have hBC : e.right ≠ r.right := by intro hh; have := congrArg Fin.val hh; omega
  have hbB : b.val.val e.right = a.val.val e.right := by
    have hh := r.map_of_ne e.right hAB.symm hBC
    rwa [seamComplementPartner_firstBlock_apply b.val e.right heR] at hh
  have hcC : c.val.val r.right = b.val.val s.left := by
    have hh := s.map_right
    rw [← hc.1] at hh
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) r.right = _ at hh
    rw [hc.2.2.2.1, hc.2.2.2.2.1, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hB.2.1.ne hCQ.ne] at hh
    exact hh
  have hsB : s.left = e.right :=
    b.val.val.toPerm.injective (hcC.symm.trans (hvalue.trans hbB.symm))
  have hbA : b.val.val r.left = r.top := by
    have hh := r.map_left
    rwa [seamComplementPartner_firstBlock_apply b.val r.left ho.1] at hh
  have hcA : c.val.val r.left = r.top := by
    have hh := s.map_of_ne r.left (by rw [hsB]; exact hAB) (by rw [← hc.1]; exact hAC)
    rw [seamComplementPartner_firstBlock_apply c.val r.left ho.1, hbA] at hh
    exact hh
  have hdA : d.val.val r.left = r.top := by
    have hh := t.map_of_ne r.left
      (by rw [htQ]; intro h; have := congrArg Fin.val h; omega)
      (by rw [htC]; exact hAC)
    rw [seamComplementPartner_firstBlock_apply d.val r.left ho.1, hcA] at hh
    exact hh
  have hpC : seamState u w r.right = r.top := by
    have hh := e.map_of_ne r.right (by rw [heQ]; exact hCQ.ne) hBC.symm
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) r.right = _ at hh
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hB.2.1.ne hCQ.ne] at hh
    exact hh.symm
  have hfixed := seamOneStep_same_second_high_value u v w r.right hLn
    (by rw [hpC]; exact hrHigh)
  have hfBot : f.bottom = r.top := by
    calc
      _ = seamState v w f.right := f.map_right.symm
      _ = seamState v w r.right := by rw [hfC]
      _ = _ := hfixed.symm.trans hpC
  have hfA : f.left = r.left :=
    d.val.val.toPerm.injective (hfBot.trans hdA.symm)
  have hsTop : s.top = a.val.val (seamComplementFirst a.val) := by
    rw [top_def, ← hc.1, ← hc.2.1, hB.2.2.2.2.2]
  have hcB : c.val.val e.right = a.val.val (seamComplementFirst a.val) := by
    have hh := s.map_left
    rw [hsB, seamComplementPartner_firstBlock_apply c.val e.right heR] at hh
    exact hh.trans hsTop
  have hdB : d.val.val e.right = a.val.val (seamComplementFirst a.val) := by
    have hh := t.map_of_ne e.right
      (by rw [htQ]; intro h; have := congrArg Fin.val h; omega)
      (by rw [htC]; exact hBC)
    rw [seamComplementPartner_firstBlock_apply d.val e.right heR, hcB] at hh
    exact hh
  have hfTop : f.top = a.val.val (seamComplementSecond a.val) := by
    rw [top_def, hfC, hdC, hrows.1]
  have horder := a.property
  change (a.val.val (seamComplementFirst a.val)).val <
    (a.val.val (seamComplementSecond a.val)).val at horder
  by_cases hBA : r.left.val < e.right.val
  · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf e.right
    · rw [hfA, hfC, Grid.mem_cIoo, if_pos (by omega)]
      exact ⟨r.left_ne_right, hBA, by omega⟩
    · rw [hdB, hfBot, hfTop, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr horder⟩
  · have hBA' : e.right.val < r.left.val := by
      have hh : r.left.val ≠ e.right.val := fun hh => hAB (Fin.ext hh)
      omega
    have hsBot : s.bottom = c.val.val r.right := hcC.symm
    have htBot : t.bottom = r.bottom := by
      rw [bottom_def, htQ, ← hc.2.2.2.2.1, hrows.2]
    have htTop : t.top = c.val.val r.right := by rw [top_def, htC]
    have hne : r.top ≠ c.val.val r.right := by
      rw [hvalue, top_def]
      exact fun hh => hBC.symm (a.val.val.toPerm.injective hh)
    by_cases hv : r.top.val < (c.val.val r.right).val
    · apply (isEmpty_iff_forall_notMem_cIoo t).mp ht r.left
      · rw [htQ, htC, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr (by omega)⟩
      · rw [hcA, htBot, htTop, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hv⟩
    · have hgt : (c.val.val r.right).val < r.top.val := by
        have hh : r.top.val ≠ (c.val.val r.right).val := fun hh => hne (Fin.ext hh)
        omega
      apply (isEmpty_iff_forall_notMem_cIoo s).mp hs r.left
      · rw [hsB, ← hc.1, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hBA', by omega⟩
      · rw [hbA, hsBot, hsTop, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hgt⟩

/-- A subsequent low second-point exchange leaves the removed column fixed,
so equality of the retained second factor identifies the two peak first-block sides. -/
theorem seamPeak_low_second_same_left
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : L.val < n) (hLv : (c.val.val L).val ≤ n)
    (hside : (t.left = seamComplementSecond c.val ∧ t.right = L) ∨
      (t.right = seamComplementSecond c.val ∧ t.left = L)) :
    r.left = s.left ∧ seamState u w r.right = r.top ∧
      c.val.val r.right = r.top ∧ d.val.val r.right = r.top := by
  have ho := seamMatchingBirthDeath_nonwrap a b c r s hr hs hb hd
  have hc := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  have hB := seamMatchingBirth_nonwrap a b r hr hb ho.1
  obtain ⟨htQ, htL, _, hdP, hdQ, _, _, _⟩ := seamOneStep_low_second t ht L hLn hLv hside
  rw [hc.2.2.2.2.1] at htQ hdQ
  rw [hc.2.2.2.1] at hdP
  have hPQ := seamComplementFirst_lt_second a.val
  have hCQ := hB.2.1.trans hPQ
  have hCP := hB.2.1
  have hpC : seamState u w r.right = r.top := by
    have hne (j : Fin (n + m + 1)) (hj : j.val < n) : r.right ≠ j := by
      intro hh; have := congrArg Fin.val hh; have hn := hB.1; omega
    have hv : (seamComplementPartner a.val).val r.right = seamState u w r.right := by
      rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
      · exact e.map_of_ne r.right (hne _ h.1) (by rw [h.2.1]; exact hCP.ne)
      · exact e.map_of_ne r.right (by rw [h.2.1]; exact hCQ.ne) (hne _ h.1)
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) r.right = _ at hv
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hCP.ne hCQ.ne] at hv
    exact hv.symm
  have hdC : d.val.val r.right = c.val.val r.right := by
    have hv := t.map_of_ne r.right (by rw [htQ]; exact hCQ.ne)
      (by rw [htL]; intro hh; have := congrArg Fin.val hh; have hn := hB.1; omega)
    change d.val.val.swapColumns (seamComplementFirst d.val)
      (seamComplementSecond d.val) r.right = _ at hv
    rw [hdP, hdQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCP.ne hCQ.ne] at hv
    exact hv
  have hqC : seamState v w r.right = c.val.val r.right := by
    have hne (j : Fin (n + m + 1)) (hj : j.val < n) : r.right ≠ j := by
      intro hh; have := congrArg Fin.val hh; have hn := hB.1; omega
    have hv : seamState v w r.right = d.val.val r.right := by
      rcases seamMatchingExit_endpoints (v, w) d f hf with h | h
      · exact f.map_of_ne r.right (hne _ h.1) (by rw [h.2.1, hdP]; exact hCP.ne)
      · exact f.map_of_ne r.right (by rw [h.2.1, hdQ]; exact hCQ.ne) (hne _ h.1)
    exact hv.trans hdC
  have hhigh : n < r.top.val := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.2
    · omega
  have hfixed := seamOneStep_same_second_high_value u v w r.right hB.1
    (by rw [hpC]; exact hhigh)
  have hrow : c.val.val r.right = r.top := hqC.symm.trans (hfixed.symm.trans hpC)
  have hbA : b.val.val r.left = r.top := by
    have hv := r.map_left
    rwa [seamComplementPartner_firstBlock_apply b.val r.left ho.1] at hv
  have hbD : b.val.val s.left = c.val.val r.right := by
    have hv := s.map_right
    rw [← hc.1] at hv
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) r.right = _ at hv
    rw [hc.2.2.2.1, hc.2.2.2.2.1, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCP.ne hCQ.ne] at hv
    exact hv.symm
  exact ⟨b.val.val.toPerm.injective (hbA.trans (hbD.trans hrow).symm), hpC, hrow, hdC.trans hrow⟩

/-- The low second-point exchange is also excluded by the outer rectangle conditions. -/
theorem seamPeak_then_low_second_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns b.val.val).card = (seamNortheastColumns c.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : L.val < n) (hLv : (c.val.val L).val ≤ n)
    (hside : (t.left = seamComplementSecond c.val ∧ t.right = L) ∨
      (t.right = seamComplementSecond c.val ∧ t.left = L)) : False := by
  obtain ⟨hsame, hpC, hcC, hdC⟩ := seamPeak_low_second_same_left
    u v w a b c d e r s t f he hr hs ht hf hb hd L hLn hLv hside
  have ho := seamMatchingBirthDeath_nonwrap a b c r s hr hs hb hd
  have hc := seamMatchingBirthDeath_columns a b c r s hr hs hb hd
  have hB := seamMatchingBirth_nonwrap a b r hr hb ho.1
  have hrows := seamMatchingBirthDeath_final_rows a b c r s hr hs hb hd
  obtain ⟨htQ, htL, hLrow, hdP, hdQ, hdProw, hdQrow, hdLrow⟩ :=
    seamOneStep_low_second t ht L hLn hLv hside
  rw [hc.2.2.2.2.1] at htQ hdQ
  rw [hc.2.2.2.1] at hdP
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hPQ := seamComplementFirst_lt_second a.val
  have hCP := hB.2.1
  have hCQ := hCP.trans hPQ
  have hhigh : n < r.top.val := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.2
    · omega
  have hlow : r.bottom.val ≤ n := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.1
    · omega
  have hmatch := seamOneStep_same_second_zero_column u v w a d e f he hf
  rw [hdP, hdQ] at hmatch
  by_cases heL : e.left.val < n
  · have hfL : f.left.val < n := by
      by_contra hh
      rw [if_pos heL, if_neg hh] at hmatch
      exact (seamComplementFirst_ne_second a.val).symm hmatch
    have heP := seamMatchingEntry_right_eq_first_of_left_lt (u, w) a e he heL
    have hfP := (seamMatchingExit_right_eq_first_of_left_lt (v, w) d f hf hfL).trans hdP
    have heBottom : e.bottom = a.val.val (seamComplementSecond a.val) := by
      have hh := e.map_right
      rw [heP, seamComplementPartner_apply_first] at hh
      exact hh.symm
    have heHigh : n < e.top.val := by
      rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
      · exact h.2.2.2.2
      · have hh := congrArg Fin.val h.2.1; omega
    have hfixed := seamOneStep_same_second_high_value u v w (seamComplementFirst a.val) hP.1
      (by rw [← heP]; exact heHigh)
    have hfBottom : f.bottom = e.top := by
      calc
        _ = seamState v w f.right := f.map_right.symm
        _ = seamState v w (seamComplementFirst a.val) := by rw [hfP]
        _ = seamState u w (seamComplementFirst a.val) := hfixed.symm
        _ = e.top := by rw [← heP]; rfl
    have hfTop : f.top = c.val.val L := by rw [top_def, hfP, ← hc.2.2.2.1, hdProw]
    have hne : r.top ≠ e.top := by
      rw [← hpC, top_def, heP]
      exact fun hh => hCP.ne ((seamState u w).toPerm.injective hh)
    by_cases hv : r.top.val < e.top.val
    · apply (isEmpty_iff_forall_notMem_cIoo e).mp he r.right
      · rw [heP, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hCP⟩
      · rw [hpC, heBottom, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hv⟩
    · have hgt : e.top.val < r.top.val := by
        have hh : r.top.val ≠ e.top.val := fun hh => hne (Fin.ext hh)
        omega
      apply (isEmpty_iff_forall_notMem_cIoo f).mp hf r.right
      · rw [hfP, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hCP⟩
      · rw [hdC, hfBottom, hfTop, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hgt⟩
  · have hfNot : ¬ f.left.val < n := by
      intro hh
      rw [if_neg heL, if_pos hh] at hmatch
      exact (seamComplementFirst_ne_second a.val) hmatch
    obtain ⟨heR, heQ, heBottom, heHigh⟩ : e.right.val < n ∧
        e.left = seamComplementSecond a.val ∧
        e.bottom = a.val.val e.right ∧ n < e.bottom.val := by
      rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
      · exact False.elim (heL h.1)
      · exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
    obtain ⟨hfR, hfQ⟩ : f.right.val < n ∧ f.left = seamComplementSecond a.val := by
      rcases seamMatchingExit_endpoints (v, w) d f hf with h | h
      · exact False.elim (hfNot h.1)
      · exact ⟨h.1, h.2.1.trans hdQ⟩
    have hBA : e.right ≠ r.left := by
      intro hh
      rw [heBottom, hh] at heHigh
      change (a.val.val r.left).val ≤ n at hlow
      omega
    have hBC : e.right ≠ r.right := by
      intro hh; have := congrArg Fin.val hh; have hn := hB.1; omega
    have hBP : e.right ≠ seamComplementFirst a.val := by
      intro hh; have := congrArg Fin.val hh; omega
    have hBQ : e.right ≠ seamComplementSecond a.val := by
      intro hh; have := congrArg Fin.val hh; omega
    have hcB := seamTwoStep_values_away a b c r s hr hs hb hd
      (seamMatchingEntry_southwest_card (u, w) a e) hsame e.right hBA hBC hBP hBQ
    have hcHigh : n < (c.val.val e.right).val := by rw [hcB, ← heBottom]; exact heHigh
    have htb : t.bottom.val ≤ n := by rw [bottom_def, htQ, ← hc.2.2.2.2.1, hrows.2]; exact hlow
    have htt : t.top.val ≤ n := by rw [top_def, htL]; exact hLv
    have hdB := seamOneStep_low_high_point t htb htt e.right heR hcHigh
    have hfixed := seamOneStep_same_second_high_value u v w (seamComplementSecond a.val) hQ.1
      (by rw [← heQ]; exact heHigh)
    have hfTop : f.top = e.bottom := by
      calc
        _ = seamState v w f.left := f.map_left.symm
        _ = seamState v w (seamComplementSecond a.val) := by rw [hfQ]
        _ = seamState u w (seamComplementSecond a.val) := hfixed.symm
        _ = e.bottom := by rw [← heQ]; rfl
    have hfB : f.right = e.right :=
      d.val.val.toPerm.injective (hfTop.trans (heBottom.trans (hcB.symm.trans hdB.symm)))
    have hfBottom : f.bottom = c.val.val (seamComplementFirst c.val) := by
      rw [bottom_def, hfQ, ← hc.2.2.2.2.1, hdQrow]
    have hdL : d.val.val L = r.bottom := hdLrow.trans hrows.2
    have hcOrder := c.property
    change (c.val.val (seamComplementFirst c.val)).val <
      (c.val.val (seamComplementSecond c.val)).val at hcOrder
    rw [hrows.2] at hcOrder
    have hBL : e.right ≠ L := by intro hh; rw [hh] at hcHigh; omega
    by_cases hv : e.right.val < L.val
    · apply (isEmpty_iff_forall_notMem_cIoo t).mp ht e.right
      · rw [htQ, htL, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hv⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, htQ, htL, ← hc.2.2.2.2.1, hrows.2,
          if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩
    · have hlt : L.val < e.right.val := by
        have hh : e.right.val ≠ L.val := fun hh => hBL (Fin.ext hh)
        omega
      apply (isEmpty_iff_forall_notMem_cIoo f).mp hf L
      · rw [hfQ, hfB, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hlt⟩
      · rw [hdL, hfBottom, hfTop, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hcOrder, by omega⟩

/-- An empty complete path with fixed second state cannot have northeast
counts `1, 2, 1, 1`. Only the final edge needs a separate nonmatching hypothesis. -/
theorem seamPeakThenFlat_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns b.val.val).card = 2)
    (hnext : (seamNortheastColumns c.val.val).card = 1) (hne : c ≠ d) : False := by
  have hentry := seamMatchingEntry_northeast_card (u, w) a e
  have hb : (seamNortheastColumns b.val.val).card =
      (seamNortheastColumns a.val.val).card + 1 := by omega
  have hd : (seamNortheastColumns b.val.val).card =
      (seamNortheastColumns c.val.val).card + 1 := by omega
  have hSWc : (seamSouthwestColumns c.val.val).card = 2 := by
    rw [seamSouthwestColumns_card, hnext]
  have hSWd := seamMatchingExit_southwest_card (v, w) d f
  obtain ⟨S, L, hS, hnot, hside⟩ := seamOneStep_internal_one_southwest hne t hSWc hSWd
  have hSmem : S ∈ seamSouthwestColumns c.val.val := by
    rcases hS with rfl | rfl
    · exact seamComplementFirst_mem c.val
    · exact seamComplementSecond_mem c.val
  have hL := seamOneStep_internal_other_ranges t hSWc hSWd S L hSmem hnot hside
  rcases hL with ⟨hLn, hLv⟩ | ⟨hLn, hLv⟩ <;> rcases hS with rfl | rfl
  · exact seamPeak_then_low_first_impossible a b c d r s t hr hs ht hb hd L hLn hLv hside
  · exact seamPeak_then_low_second_impossible u v w a b c d e r s t f
      he hr hs ht hf hb hd L hLn hLv hside
  · exact seamPeak_then_high_first_impossible u v w a b c d e r s t f
      he hr hs ht hf hb hd L hLn hLv hside
  · exact seamPeak_then_high_second_impossible u v w a b c d e r s t f
      he hr hs ht hf hb hd L hLn hLv hside

/-- The same exclusion for arbitrary retained pairs with equal second components. -/
theorem seamPeakThenFlat_same_second_impossible
    (p q : SeamRetainedIndex n m) (hpq : p.2 = q.2) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns b.val.val).card = 2)
    (hnext : (seamNortheastColumns c.val.val).card = 1) (hne : c ≠ d) : False := by
  rcases p with ⟨u, w⟩
  rcases q with ⟨v, w'⟩
  change w = w' at hpq
  subst w'
  exact seamPeakThenFlat_impossible u v w a b c d e r s t f he hr hs ht hf hmid hnext hne

/-- The actual three-transition path type has no `1,2,1,1` sector with fixed second component. -/
theorem seamCorrectionThree_not_peak_then_flat
    (u v : GridState (n + 1)) (w : GridState (m + 1))
    (path : SeamCorrectionPath 3 (u, w) (v, w)) :
    ¬ ((seamNortheastColumns path.2.2.2.1.1.val.val).card = 2 ∧
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card = 1) := by
  rcases path with ⟨a, d, e, ⟨b, r, ⟨c, s, ⟨d', t, tail⟩⟩⟩, f⟩
  have hlast : d' = d := tail.property
  subst d'
  rintro ⟨hmid, hnext⟩
  exact seamPeakThenFlat_impossible u v w a b c d e.val r.val s.val t.val f.val
    e.property r.property.2 s.property.2 t.property.2 f.property hmid hnext t.property.1

end OnLeConjecture.KnotFloer.GridFull
