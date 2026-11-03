/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakThenFlatBarrier

/-!
# Rectangle barriers before an internal birth-death peak

The exclusions use the actual empty rectangles of a complete seam correction.
The retained second factor is fixed, while intermediate states need not remain
in a confined set of columns or preserve particular rows.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A neutral low first-point exchange cannot precede a birth/death peak. -/
theorem seamLowFirst_then_peak_impossible (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns c.val.val).card = (seamNortheastColumns b.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : L.val < n) (hLv : (a.val.val L).val ≤ n)
    (hside : (r.left = seamComplementFirst a.val ∧ r.right = L) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = L)) : False := by
  have ho := seamMatchingBirthDeath_nonwrap b c d s t hs ht hb hd
  have hB := seamMatchingBirth_nonwrap b c s hs hb ho.1
  obtain ⟨hrL, hrP, hrow, hbP, _, _, _, _⟩ := seamOneStep_low_first r hr L hLn hLv hside
  rw [hbP] at hB
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hhigh : n < (a.val.val s.right).val := by
    by_contra h
    have hmem : s.right ∈ seamSouthwestColumns a.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨hB.1, by omega⟩
    have hmin := Finset.min'_le _ s.right hmem
    change seamComplementFirst a.val ≤ s.right at hmin
    exact (not_le_of_gt hB.2.1) hmin
  have horder := a.property
  change (a.val.val (seamComplementFirst a.val)).val <
    (a.val.val (seamComplementSecond a.val)).val at horder
  apply (isEmpty_iff_forall_notMem_cIoo r).mp hr s.right
  · rw [Grid.mem_cIoo, hrL, hrP, if_pos (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hB.2.1⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrP, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩

/-- A high second-point exchange followed by a peak is incompatible with a
fixed retained second factor. -/
theorem seamHighSecond_then_peak_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns c.val.val).card = (seamNortheastColumns b.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : n ≤ L.val) (hLv : n < (a.val.val L).val)
    (hside : (r.left = seamComplementSecond a.val ∧ r.right = L) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = L)) : False := by
  have hc := seamMatchingBirthDeath_columns b c d s t hs ht hb hd
  obtain ⟨hrQ, hrL, hLP, hbP, hbQ, _, _⟩ :=
    seamOneStep_high_second r hr (seamMatchingEntry_southwest_card (u, w) a e) L hLn hLv hside
  have hdP := hc.2.2.2.1.trans hbP
  have hdQ := hc.2.2.2.2.1.trans hbQ
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hpq := seamComplementFirst_lt_second a.val
  have hLQ := hLP.trans hpq
  have hmatch := seamOneStep_same_second_zero_column u v w a d e f he hf
  have heL : ¬ e.left.val < n := by
    intro h
    rw [if_pos h, hdP, hdQ] at hmatch
    split_ifs at hmatch
    · exact (seamComplementFirst_ne_second a.val).symm hmatch
    · have hh := congrArg Fin.val hmatch; omega
  have hfL : f.left.val < n := by
    by_contra h
    rw [if_neg heL, if_neg h, hdP] at hmatch
    exact hLP.ne hmatch.symm
  obtain ⟨heR, heQ, heBot, heHigh⟩ : e.right.val < n ∧
      e.left = seamComplementSecond a.val ∧
      e.bottom = a.val.val e.right ∧ n < e.bottom.val := by
    rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
    · exact False.elim (heL h.1)
    · exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hfC : f.right = L :=
    (seamMatchingExit_right_eq_first_of_left_lt (v, w) d f hf hfL).trans hdP
  have hvQ : seamState u w (seamComplementSecond a.val) = a.val.val e.right := by
    calc
      _ = e.bottom := by rw [← heQ]; rfl
      _ = _ := heBot
  have hpB : (seamComplementPartner b.val).val (seamComplementSecond a.val) =
      b.val.val (seamComplementSecond a.val) := by
    change b.val.val.swapColumns (seamComplementFirst b.val)
      (seamComplementSecond b.val) (seamComplementSecond a.val) = _
    rw [hbP, hbQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hLQ.ne.symm hpq.ne.symm]
  have hbValue : b.val.val (seamComplementSecond a.val) = a.val.val L := by
    rw [← hpB, ← hrQ, r.map_left, hrL]
  have hdValue : d.val.val (seamComplementSecond a.val) = a.val.val L := by
    have hh := seamMatchingBirthDeath_tail_apply b c d s t hs ht hb hd
      (seamComplementSecond a.val) (by rw [hbQ]; exact hpq)
    exact hh.trans hbValue
  have hwQ : seamState v w (seamComplementSecond a.val) = a.val.val L := by
    rw [f.map_of_ne (seamComplementSecond a.val)
      (by intro h; have := congrArg Fin.val h; omega)
      (by rw [hfC]; exact hLQ.ne.symm), hdValue]
  have hfixed := seamOneStep_same_second_high_value u v w (seamComplementSecond a.val) hq.1
    (by rw [← heQ]; exact heHigh)
  have hh : a.val.val e.right = a.val.val L := hvQ.symm.trans (hfixed.trans hwQ)
  have hcol := congrArg Fin.val (a.val.val.toPerm.injective hh)
  omega

/-- In a high first-point exchange followed by a peak, fixing the second
factor forces the birth to use the original first southwest column. -/
theorem seamHighFirst_then_peak_column
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns c.val.val).card = (seamNortheastColumns b.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : n ≤ L.val) (hLv : n < (a.val.val L).val)
    (hside : (r.left = seamComplementFirst a.val ∧ r.right = L) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = L)) :
    s.right = seamComplementFirst a.val ∧ e.left.val < n ∧
      e.right = seamComplementFirst a.val ∧ e.top = a.val.val e.left ∧ n < e.top.val := by
  have hc := seamMatchingBirthDeath_columns b c d s t hs ht hb hd
  obtain ⟨hrL, hrP, hQL, hbP, hbQ, _, _⟩ :=
    seamOneStep_high_first r hr (seamMatchingEntry_southwest_card (u, w) a e) L hLn hLv hside
  have hdP := hc.2.2.2.1.trans hbP
  have hdQ := hc.2.2.2.2.1.trans hbQ
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hpq := seamComplementFirst_lt_second a.val
  have hPL := hpq.trans hQL
  have hmatch := seamOneStep_same_second_zero_column u v w a d e f he hf
  have heL : e.left.val < n := by
    by_contra h
    rw [if_neg h, hdP, hdQ] at hmatch
    split_ifs at hmatch
    · have hh := congrArg Fin.val hmatch; omega
    · exact (seamComplementFirst_ne_second a.val) hmatch
  have hfL : ¬ f.left.val < n := by
    intro h
    rw [if_pos heL, if_pos h, hdQ] at hmatch
    exact hQL.ne hmatch
  obtain ⟨heP, heTop, heHigh⟩ : e.right = seamComplementFirst a.val ∧
      e.top = a.val.val e.left ∧ n < e.top.val := by
    rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
    · exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · have hh := congrArg Fin.val h.2.1; omega
  obtain ⟨hfR, hfC⟩ : f.right.val < n ∧ f.left = L := by
    rcases seamMatchingExit_endpoints (v, w) d f hf with h | h
    · exact False.elim (hfL h.1)
    · exact ⟨h.1, h.2.1.trans hdQ⟩
  have hvP : seamState u w (seamComplementFirst a.val) = a.val.val e.left := by
    calc
      _ = e.top := by rw [← heP]; rfl
      _ = _ := heTop
  have hpB : (seamComplementPartner b.val).val (seamComplementFirst a.val) =
      b.val.val (seamComplementFirst a.val) := by
    change b.val.val.swapColumns (seamComplementFirst b.val)
      (seamComplementSecond b.val) (seamComplementFirst a.val) = _
    rw [hbP, hbQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hpq.ne hPL.ne]
  have hbValue : b.val.val (seamComplementFirst a.val) = a.val.val L := by
    rw [← hpB, ← hrP, r.map_right, hrL]
  have hwP : seamState v w (seamComplementFirst a.val) = d.val.val (seamComplementFirst a.val) := by
    exact f.map_of_ne (seamComplementFirst a.val)
      (by rw [hfC]; exact hPL.ne)
      (by intro h; have := congrArg Fin.val h; omega)
  have hfixed := seamOneStep_same_second_high_value u v w (seamComplementFirst a.val) hp.1
    (by rw [← heP]; exact heHigh)
  have hvalue : d.val.val (seamComplementFirst a.val) = a.val.val e.left :=
    hwP.symm.trans (hfixed.symm.trans hvP)
  have heq : s.right = seamComplementFirst a.val := by
    by_contra hne
    have haway := seamPeak_rightBlock_away b c d s t hs ht hb hd
      (seamComplementFirst a.val) hp.1 (Ne.symm hne)
      (by rw [hbP]; exact hpq.ne) (by rw [hbQ]; exact hPL.ne)
    have hcol := a.val.val.toPerm.injective (hvalue.symm.trans (haway.trans hbValue))
    have hh := congrArg Fin.val hcol
    omega
  exact ⟨heq, heL, heP, heTop, heHigh⟩

/-- The forced column is incompatible with the entry and birth rectangles. -/
theorem seamHighFirst_then_peak_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns c.val.val).card = (seamNortheastColumns b.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : n ≤ L.val) (hLv : n < (a.val.val L).val)
    (hside : (r.left = seamComplementFirst a.val ∧ r.right = L) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = L)) : False := by
  obtain ⟨hsP, heL, heP, heTop, heHigh⟩ :=
    seamHighFirst_then_peak_column u v w a b c d e r s t f he hr hs ht hf hb hd L hLn hLv hside
  have ho := seamMatchingBirthDeath_nonwrap b c d s t hs ht hb hd
  have hrows := seamMatchingBirthDeath_final_rows b c d s t hs ht hb hd
  have hc := seamMatchingBirthDeath_columns b c d s t hs ht hb hd
  obtain ⟨hrL, hrP, hQL, hbP, hbQ, _, hbL⟩ :=
    seamOneStep_high_first r hr (seamMatchingEntry_southwest_card (u, w) a e) L hLn hLv hside
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hpq := seamComplementFirst_lt_second a.val
  have hPL := hpq.trans hQL
  have heBot : e.bottom = a.val.val (seamComplementSecond a.val) := by
    have hh := e.map_right
    rw [heP, seamComplementPartner_apply_first] at hh
    exact hh.symm
  have hfirst (j : Fin (n + m + 1)) (hj : j.val < n) : b.val.val j = a.val.val j := by
    have hh := r.map_of_ne j
      (by rw [hrL]; intro hh; have := congrArg Fin.val hh; omega)
      (by rw [hrP]; intro hh; have := congrArg Fin.val hh; omega)
    rwa [seamComplementPartner_firstBlock_apply b.val j hj] at hh
  have hsTop : s.top = a.val.val L := by
    rw [top_def, hsP]
    have hh := r.map_right
    rw [hrP, hrL] at hh
    change b.val.val.swapColumns _ _ (seamComplementFirst a.val) = _ at hh
    rwa [hbP, hbQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hpq.ne hPL.ne] at hh
  have horder := d.property
  change (d.val.val (seamComplementFirst d.val)).val <
    (d.val.val (seamComplementSecond d.val)).val at horder
  rw [hrows.1, hrows.2, hbQ, hbL] at horder
  have hsBot : s.bottom = a.val.val s.left := by rw [bottom_def, hfirst s.left ho.1]
  have hsHigh : n < s.top.val := by rw [hsTop]; exact hLv
  have hsLow : (a.val.val s.left).val ≤ n := by
    have hh := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem d.val)
    rw [hrows.2, hsBot] at hh
    exact hh.2
  rw [hsBot] at horder
  have heHigh' : n < (a.val.val e.left).val := by rwa [heTop] at heHigh
  have heNot : e.top ≠ a.val.val L := by
    rw [heTop]
    intro hh
    have hcol := congrArg Fin.val (a.val.val.toPerm.injective hh)
    omega
  have hlt : e.top.val < (a.val.val L).val := by
    by_contra hh
    have hgt : (a.val.val L).val < e.top.val := by
      have hn : e.top.val ≠ (a.val.val L).val := fun h => heNot (Fin.ext h)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo r).mp hr e.left
    · rw [Grid.mem_cIoo, hrL, hrP, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr (by omega)⟩
    · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrP, if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl (by rwa [heTop] at hgt)⟩
  have hne : s.left ≠ e.left := by
    intro hh
    rw [hh, ← heTop] at horder
    have hlow := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem d.val)
    rw [hrows.2] at hlow
    rw [hsBot, hh, ← heTop] at hlow
    omega
  by_cases hAE : s.left.val < e.left.val
  · apply (isEmpty_iff_forall_notMem_cIoo s).mp hs e.left
    · rw [Grid.mem_cIoo, hsP, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, hAE, by omega⟩
    · rw [hfirst e.left heL, ← heTop, hsBot, hsTop, Grid.mem_cIoo, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hlt⟩
  · have hEA : e.left.val < s.left.val := by
      have hh : s.left.val ≠ e.left.val := fun h => hne (Fin.ext h)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo_target e).mp he s.left
    · rw [Grid.mem_cIoo, heP, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, hEA, by omega⟩
    · rw [seamComplementPartner_firstBlock_apply a.val s.left ho.1,
        e.map_right, e.map_left]
      change a.val.val s.left ∈ Grid.cIoo e.bottom e.top
      rw [heBot, heTop, Grid.mem_cIoo, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, by omega⟩

/-- A low second-point exchange before a peak preserves the high birth-column
value, so a fixed second factor identifies the two peak first-block sides. -/
theorem seamLowSecond_then_peak_same_left
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns c.val.val).card = (seamNortheastColumns b.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : L.val < n) (hLv : (a.val.val L).val ≤ n)
    (hside : (r.left = seamComplementSecond a.val ∧ r.right = L) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = L)) :
    s.left = t.left ∧ seamState u w s.right = s.top ∧ d.val.val s.right = s.top := by
  have ho := seamMatchingBirthDeath_nonwrap b c d s t hs ht hb hd
  have hc := seamMatchingBirthDeath_columns b c d s t hs ht hb hd
  have hB := seamMatchingBirth_nonwrap b c s hs hb ho.1
  obtain ⟨hrQ, hrL, _, hbP, hbQ, _, _, _⟩ := seamOneStep_low_second r hr L hLn hLv hside
  have hdP := hc.2.2.2.1.trans hbP
  have hdQ := hc.2.2.2.2.1.trans hbQ
  have hCP : s.right < seamComplementFirst a.val := by simpa only [hbP] using hB.2.1
  have hCQ := hCP.trans (seamComplementFirst_lt_second a.val)
  have hne (j : Fin (n + m + 1)) (hj : j.val < n) : s.right ≠ j := by
    intro hh; have := congrArg Fin.val hh; have hn := hB.1; omega
  have hbC : b.val.val s.right = a.val.val s.right := by
    have hh := r.map_of_ne s.right (by rw [hrQ]; exact hCQ.ne) (by rw [hrL]; exact hne L hLn)
    change b.val.val.swapColumns _ _ s.right = _ at hh
    rwa [hbP, hbQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCP.ne hCQ.ne] at hh
  have hpC : seamState u w s.right = s.top := by
    have hv : (seamComplementPartner a.val).val s.right = seamState u w s.right := by
      rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
      · exact e.map_of_ne s.right (hne _ h.1) (by rw [h.2.1]; exact hCP.ne)
      · exact e.map_of_ne s.right (by rw [h.2.1]; exact hCQ.ne) (hne _ h.1)
    change a.val.val.swapColumns _ _ s.right = _ at hv
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hCP.ne hCQ.ne] at hv
    exact hv.symm.trans hbC.symm
  have hqC : seamState v w s.right = d.val.val s.right := by
    rcases seamMatchingExit_endpoints (v, w) d f hf with h | h
    · exact f.map_of_ne s.right (hne _ h.1) (by rw [h.2.1, hdP]; exact hCP.ne)
    · exact f.map_of_ne s.right (by rw [h.2.1, hdQ]; exact hCQ.ne) (hne _ h.1)
  have hhigh : n < s.top.val := by
    rcases seamMatchingBirth_ranges s hb with h | h
    · exact h.2.2.2
    · omega
  have hfixed := seamOneStep_same_second_high_value u v w s.right hB.1
    (by rw [hpC]; exact hhigh)
  have hrow : d.val.val s.right = s.top := hqC.symm.trans (hfixed.symm.trans hpC)
  have hcA : c.val.val s.left = s.top := by
    have hv := s.map_left
    rwa [seamComplementPartner_firstBlock_apply c.val s.left ho.1] at hv
  have hcD : c.val.val t.left = d.val.val s.right := by
    have hv := t.map_right
    rw [← hc.1] at hv
    change d.val.val.swapColumns _ _ s.right = _ at hv
    rw [hc.2.2.2.1, hc.2.2.2.2.1, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hB.2.1.ne
        (hB.2.1.trans (seamComplementFirst_lt_second b.val)).ne] at hv
    exact hv.symm
  exact ⟨c.val.val.toPerm.injective (hcA.trans (hcD.trans hrow).symm), hpC, hrow⟩

/-- The low second-point case is excluded by the outer empty rectangles. -/
theorem seamLowSecond_then_peak_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hb : (seamNortheastColumns c.val.val).card = (seamNortheastColumns b.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (L : Fin (n + m + 1)) (hLn : L.val < n) (hLv : (a.val.val L).val ≤ n)
    (hside : (r.left = seamComplementSecond a.val ∧ r.right = L) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = L)) : False := by
  obtain ⟨_, hpC, hdC⟩ := seamLowSecond_then_peak_same_left
    u v w a b c d e r s t f he hr hs ht hf hb hd L hLn hLv hside
  have ho := seamMatchingBirthDeath_nonwrap b c d s t hs ht hb hd
  have hc := seamMatchingBirthDeath_columns b c d s t hs ht hb hd
  have hB := seamMatchingBirth_nonwrap b c s hs hb ho.1
  have hrows := seamMatchingBirthDeath_final_rows b c d s t hs ht hb hd
  obtain ⟨hrQ, hrL, hLrow, hbP, hbQ, hbProw, hbQrow, _⟩ :=
    seamOneStep_low_second r hr L hLn hLv hside
  have hdP := hc.2.2.2.1.trans hbP
  have hdQ := hc.2.2.2.2.1.trans hbQ
  have hdProw : d.val.val (seamComplementFirst a.val) = a.val.val (seamComplementFirst a.val) := by
    calc
      _ = b.val.val (seamComplementSecond b.val) := by simpa only [hdP] using hrows.1
      _ = _ := by rw [hbQ, hbQrow]
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hPQ := seamComplementFirst_lt_second a.val
  have hCP : s.right < seamComplementFirst a.val := by simpa only [hbP] using hB.2.1
  have hhigh : n < s.top.val := by
    rcases seamMatchingBirth_ranges s hb with h | h
    · exact h.2.2.2
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
    have hfTop : f.top = a.val.val (seamComplementFirst a.val) := by
      rw [top_def, hfP, hdProw]
    have hne : s.top ≠ e.top := by
      rw [← hpC, top_def, heP]
      exact fun hh => hCP.ne ((seamState u w).toPerm.injective hh)
    by_cases hv : s.top.val < e.top.val
    · apply (isEmpty_iff_forall_notMem_cIoo e).mp he s.right
      · rw [heP, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hCP⟩
      · rw [hpC, heBottom, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hv⟩
    · have hgt : e.top.val < s.top.val := by
        have hh : s.top.val ≠ e.top.val := fun hh => hne (Fin.ext hh)
        omega
      apply (isEmpty_iff_forall_notMem_cIoo f).mp hf s.right
      · rw [hfP, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hCP⟩
      · rw [hdC, hfBottom, hfTop, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hgt⟩
  · obtain ⟨heR, heQ, heTop, heBot, heHigh⟩ : e.right.val < n ∧
        e.left = seamComplementSecond a.val ∧
        e.top = a.val.val (seamComplementFirst a.val) ∧
        e.bottom = a.val.val e.right ∧ n < e.bottom.val := by
      rcases seamMatchingEntry_endpoints (u, w) a e he with h | h
      · exact False.elim (heL h.1)
      · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    have horder := a.property
    change (a.val.val (seamComplementFirst a.val)).val <
      (a.val.val (seamComplementSecond a.val)).val at horder
    have hBL : e.right ≠ L := by
      intro hh
      rw [heBot, hh] at heHigh
      omega
    by_cases hv : e.right.val < L.val
    · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr e.right
      · rw [hrQ, hrL, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hv⟩
      · rw [bottom_def, top_def, hrQ, hrL, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩
    · have hlt : L.val < e.right.val := by
        have hh : e.right.val ≠ L.val := fun hh => hBL (Fin.ext hh)
        omega
      apply (isEmpty_iff_forall_notMem_cIoo_target e).mp he L
      · rw [heQ, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hlt⟩
      · rw [seamComplementPartner_firstBlock_apply a.val L hLn, e.map_right, e.map_left]
        change a.val.val L ∈ Grid.cIoo e.bottom e.top
        rw [heBot, heTop, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hLrow⟩

/-- A complete empty path with fixed second factor cannot have northeast
counts `1,1,2,1`. Only the initial neutral transition needs a nonmatching hypothesis. -/
theorem seamFlatThenPeak_impossible
    (u v : GridState (n + 1)) (w : GridState (m + 1)) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u w) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState v w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns b.val.val).card = 1)
    (hnext : (seamNortheastColumns c.val.val).card = 2) (hne : a ≠ b) : False := by
  have hexit := seamMatchingExit_northeast_card (v, w) d f
  have hb : (seamNortheastColumns c.val.val).card =
      (seamNortheastColumns b.val.val).card + 1 := by omega
  have hd : (seamNortheastColumns c.val.val).card =
      (seamNortheastColumns d.val.val).card + 1 := by omega
  have hSWa := seamMatchingEntry_southwest_card (u, w) a e
  have hSWb : (seamSouthwestColumns b.val.val).card = 2 := by
    rw [seamSouthwestColumns_card, hmid]
  obtain ⟨S, L, hS, hnot, hside⟩ := seamOneStep_internal_one_southwest hne r hSWa hSWb
  have hSmem : S ∈ seamSouthwestColumns a.val.val := by
    rcases hS with rfl | rfl
    · exact seamComplementFirst_mem a.val
    · exact seamComplementSecond_mem a.val
  have hL := seamOneStep_internal_other_ranges r hSWa hSWb S L hSmem hnot hside
  rcases hL with ⟨hLn, hLv⟩ | ⟨hLn, hLv⟩ <;> rcases hS with rfl | rfl
  · exact seamLowFirst_then_peak_impossible a b c d r s t hr hs ht hb hd L hLn hLv hside
  · exact seamLowSecond_then_peak_impossible u v w a b c d e r s t f
      he hr hs ht hf hb hd L hLn hLv hside
  · exact seamHighFirst_then_peak_impossible u v w a b c d e r s t f
      he hr hs ht hf hb hd L hLn hLv hside
  · exact seamHighSecond_then_peak_impossible u v w a b c d e r s t f
      he hr hs ht hf hb hd L hLn hLv hside

/-- The same exclusion for arbitrary retained pairs with equal second components. -/
theorem seamFlatThenPeak_same_second_impossible
    (p q : SeamRetainedIndex n m) (hpq : p.2 = q.2) (a b c d : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (s : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (t : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hs : s.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns b.val.val).card = 1)
    (hnext : (seamNortheastColumns c.val.val).card = 2) (hne : a ≠ b) : False := by
  rcases p with ⟨u, w⟩
  rcases q with ⟨v, w'⟩
  change w = w' at hpq
  subst w'
  exact seamFlatThenPeak_impossible u v w a b c d e r s t f he hr hs ht hf hmid hnext hne

/-- The actual three-transition path type has no `1,1,2,1` sector with fixed second component. -/
theorem seamCorrectionThree_not_flat_then_peak
    (u v : GridState (n + 1)) (w : GridState (m + 1))
    (path : SeamCorrectionPath 3 (u, w) (v, w)) :
    ¬ ((seamNortheastColumns path.2.2.2.1.1.val.val).card = 1 ∧
      (seamNortheastColumns path.2.2.2.1.2.2.1.val.val).card = 2) := by
  rcases path with ⟨a, d, e, ⟨b, r, ⟨c, s, ⟨d', t, tail⟩⟩⟩, f⟩
  have hlast : d' = d := tail.property
  subst d'
  rintro ⟨hmid, hnext⟩
  exact seamFlatThenPeak_impossible u v w a b c d e.val r.val s.val t.val f.val
    e.property r.property.2 s.property.2 t.property.2 f.property hmid hnext r.property.1

end OnLeConjecture.KnotFloer.GridFull
