/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakPlateauReduction

/-! # Entry and exit obstructions for the two plateau configurations -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem plateau_entry_blocked {p : SeamRetainedIndex n m} {a : SeamMatchingSource n m}
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (he : e.IsEmpty) (C : Fin (n + m + 1)) (hc : C ∈ Grid.cIoo e.left e.right)
    (hv : (seamComplementPartner a.val).val C ∈ Grid.cIoo e.bottom e.top) : False := by
  apply (isEmpty_iff_forall_notMem_cIoo_target e).mp he C hc
  simpa only [e.map_right, e.map_left, bottom_def, top_def] using hv

private theorem plateau_wrap_high_lt {x y : GridState (n + m + 1)}
    (t : GridRectangleBetween x y) (ht : t.IsEmpty)
    (hcol : t.right < t.left) (hRn : n ≤ t.right.val)
    (hB : n < t.bottom.val) (hT : t.top.val ≤ n)
    (A : Fin (n + m + 1)) (hAn : A.val < n) :
    (x A).val < t.bottom.val := by
  have hne : (x A).val ≠ t.bottom.val := by
    intro h
    have hh := x.toPerm.injective (Fin.ext h)
    have := congrArg Fin.val hh
    omega
  by_contra hn
  have hv : t.bottom.val < (x A).val := by omega
  apply (isEmpty_iff_forall_notMem_cIoo t).mp ht A
  · rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨t.left_ne_right, Or.inr (by omega)⟩
  · rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨t.bottom_ne_top, Or.inl hv⟩

/-- The first remaining plateau configuration admits no empty entry rectangle.
The statement uses the actual birth and neutral rectangles and no retained
factor equality. -/
theorem seamPeakPlateau_high_first_no_entry (p : SeamRetainedIndex n m)
    (a b c : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hcard : (seamSouthwestColumns b.val.val).card = 3)
    (hcard' : (seamSouthwestColumns c.val.val).card = 3)
    (hrL : r.left.val < n)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (b.val.val D).val)
    (htL : t.left = D) (htR : t.right = seamComplementFirst b.val)
    (hRD : seamComplementThird b.val (by omega) < D) : False := by
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by omega
  have hPQ := seamComplementFirst_lt_second a.val
  have hPa := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hQa := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hPb := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  obtain ⟨_, _, _, hcase⟩ := seamPlateau_high_first t ht hcard hcard' D hDn hDv
    (Or.inr ⟨htR, htL⟩)
  have hrows : (b.val.val (seamComplementThird b.val h3b)).val <
      (b.val.val (seamComplementSecond b.val)).val := by
    rcases hcase with h | h
    · exact False.elim ((not_lt_of_gt hRD) h.1)
    · exact h.2.2.2.2
  rcases seamMatchingBirth_endpoints a b r hr hb with hB | hB
  swap
  · have hn := hB.2.1
    omega
  obtain ⟨_, hrRn, hCP, _, hfirst, hsecond, _, hbQ, hhigh⟩ := hB
  have hthird := seamMatchingBirth_third a b r hr hb h3b
  rw [seamMatchingBirth_third_row a b r hr hb h3b, hbQ] at hrows
  have hQD : seamComplementSecond a.val < D := by rwa [hthird] at hRD
  have hPD := hPQ.trans hQD
  have hCD := hCP.trans hPD
  have haD : a.val.val D = b.val.val D := by
    have hh := r.map_of_ne D
      (by intro h; have := congrArg Fin.val h; omega) hCD.ne.symm
    change b.val.val.swapColumns (seamComplementFirst b.val)
      (seamComplementSecond b.val) D = _ at hh
    rw [hfirst, hsecond, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hCD.ne.symm hPD.ne.symm] at hh
    exact hh.symm
  have hpD : (seamComplementPartner a.val).val D = a.val.val D := by
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) D = _
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hPD.ne.symm hQD.ne.symm]
  have hpC : (seamComplementPartner a.val).val r.right = r.top := by
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) r.right = _
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hCP.ne (hCP.trans hPQ).ne]
    rfl
  have hbottomlow : r.bottom.val ≤ n := by
    rw [← hbQ]
    exact ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem b.val)).2
  have hhighbound (A : Fin (n + m + 1)) (hAn : A.val < n) (hAv : n < (a.val.val A).val) :
      (a.val.val A).val < (a.val.val D).val := by
    have hAB : A ≠ r.left := by intro hh; rw [hh] at hAv; change n < r.bottom.val at hAv; omega
    have hAC : A ≠ r.right := by intro hh; have := congrArg Fin.val hh; omega
    have hbA : b.val.val A = a.val.val A := by
      have hh := r.map_of_ne A hAB hAC
      rwa [seamComplementPartner_firstBlock_apply b.val A hAn] at hh
    have hh := plateau_wrap_high_lt t ht
      (by rw [htR, htL, hfirst]; exact hCD) (by simpa only [htR] using hPb.1)
      (by simpa only [bottom_def, htL] using hDv)
      (by simpa only [top_def, htR] using hPb.2) A hAn
    simpa only [bottom_def, htL, hbA, ← haD] using hh
  rcases seamMatchingEntry_endpoints p a e he with hE | hE
  · obtain ⟨hAn, heR, heB, heT, hehigh⟩ := hE
    have hAH : n < (a.val.val e.left).val := by rwa [heT] at hehigh
    have hAB : e.left ≠ r.left := by
      intro hh; rw [hh] at hAH; change n < r.bottom.val at hAH; omega
    have hABv : e.left.val ≠ r.left.val := fun hh => hAB (Fin.ext hh)
    by_cases hABlt : e.left.val < r.left.val
    · apply plateau_entry_blocked e he r.left
      · rw [Grid.mem_cIoo, heR, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hABlt, by omega⟩
      · rw [seamComplementPartner_firstBlock_apply a.val r.left hrL,
          Grid.mem_cIoo, heB, heT, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hrows, by
          change r.bottom.val < (a.val.val e.left).val
          omega⟩
    · have hBA : r.left.val < e.left.val := by omega
      by_cases hKH : r.top.val < (a.val.val e.left).val
      · apply plateau_entry_blocked e he r.right
        · rw [Grid.mem_cIoo, heR, if_pos (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hCP⟩
        · rw [hpC, Grid.mem_cIoo, heB, heT, if_pos (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hKH⟩
      · have hHKne : (a.val.val e.left).val ≠ r.top.val := by
          intro hh
          have heC := a.val.val.toPerm.injective (Fin.ext hh)
          have := congrArg Fin.val heC
          omega
        have hHK : (a.val.val e.left).val < r.top.val := by omega
        apply (isEmpty_iff_forall_notMem_cIoo r).mp hr e.left
        · rw [Grid.mem_cIoo, if_pos (by omega)]
          exact ⟨r.left_ne_right, hBA, by omega⟩
        · rw [Grid.mem_cIoo, if_pos (by omega)]
          exact ⟨r.bottom_ne_top, by omega, hHK⟩
  · obtain ⟨hAn, heL, heT, heB, hehigh⟩ := hE
    have hAH : n < (a.val.val e.right).val := by rwa [heB] at hehigh
    have hHD := hhighbound e.right hAn hAH
    apply plateau_entry_blocked e he D
    · rw [Grid.mem_cIoo, heL, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hQD⟩
    · rw [hpD, Grid.mem_cIoo, heB, heT, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl hHD⟩

private theorem plateau_wrap_high_gt {x y : GridState (n + m + 1)}
    (t : GridRectangleBetween x y) (ht : t.IsEmpty)
    (hcol : t.right < t.left) (hRn : n ≤ t.right.val)
    (hB : t.bottom.val ≤ n) (hT : n < t.top.val)
    (A : Fin (n + m + 1)) (hAn : A.val < n) (hAv : n < (x A).val) :
    t.top.val < (x A).val := by
  have hne : (x A).val ≠ t.top.val := by
    intro h
    have hh := x.toPerm.injective (Fin.ext h)
    have := congrArg Fin.val hh
    omega
  by_contra hn
  have hv : (x A).val < t.top.val := by omega
  apply (isEmpty_iff_forall_notMem_cIoo t).mp ht A
  · rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨t.left_ne_right, Or.inr (by omega)⟩
  · rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨t.bottom_ne_top, by omega, hv⟩

/-- The second remaining plateau configuration admits no empty exit rectangle.
The first-row inequality is the one proved for the preceding birth. -/
theorem seamPeakPlateau_high_third_no_exit (q : SeamRetainedIndex n m)
    (b c d : SeamMatchingSource n m)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (f : GridRectangleBetween d.val.val (seamState q.1 q.2))
    (ht : t.IsEmpty) (hu : u.IsEmpty) (hf : f.IsEmpty)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (hcard : (seamSouthwestColumns b.val.val).card = 3)
    (hcard' : (seamSouthwestColumns c.val.val).card = 3)
    (hrow : (b.val.val (seamComplementFirst b.val)).val <
      (b.val.val (seamComplementThird b.val (by omega))).val)
    (huL : u.left.val < n)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (b.val.val D).val)
    (htL : t.left = seamComplementThird b.val (by omega)) (htR : t.right = D) : False := by
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by omega
  have h3c : 3 ≤ (seamSouthwestColumns c.val.val).card := by omega
  have hPQ := seamComplementFirst_lt_second b.val
  have hPR := seamComplementFirst_lt_third b.val h3b
  have hQR := seamComplementSecond_lt_third b.val h3b
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem b.val)
  have hr := (mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem b.val h3b)
  obtain ⟨_, _, hDP, hP, hQ, hR⟩ := seamPlateau_high_third t ht hcard hcard' hrow D hDn hDv
    (Or.inl ⟨htL, htR⟩)
  have hcP : c.val.val (seamComplementFirst c.val) = b.val.val (seamComplementFirst b.val) := by
    have hh := t.map_of_ne (seamComplementFirst b.val)
      (by rw [htL]; exact hPR.ne) (by rw [htR]; exact hDP.ne.symm)
    rw [← hQ, seamComplementPartner_apply_second, hQ] at hh
    exact hh
  have hcQ : c.val.val (seamComplementSecond c.val) =
      b.val.val (seamComplementThird b.val h3b) := by
    have hh := t.map_right
    rw [htR, htL, ← hP, seamComplementPartner_apply_first] at hh
    exact hh
  have hcR : c.val.val (seamComplementThird c.val h3c) =
      b.val.val (seamComplementSecond b.val) := by
    rw [hR]
    have hh := t.map_of_ne (seamComplementSecond b.val)
      (by rw [htL]; exact hQR.ne) (by rw [htR]; exact (hDP.trans hPQ).ne.symm)
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) _ = _ at hh
    simpa only [hP, hQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (hDP.trans hPQ).ne.symm hPQ.ne.symm] using hh
  have hcRemoved : c.val.val (seamComplementThird b.val h3b) = b.val.val D := by
    have hh := t.map_left
    rw [htL, htR] at hh
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) _ = _ at hh
    simpa only [hP, hQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (hDP.trans hPR).ne.symm hPR.ne.symm] using hh
  obtain ⟨huR, _, hdP, hdQ, hdProw, hdQrow, _⟩ := seamMatchingDeath_nonwrap c d u hu hd huL
  have hdP' : seamComplementFirst d.val = seamComplementFirst b.val := hdP.trans hQ
  have hdQ' : seamComplementSecond d.val = seamComplementSecond b.val := hdQ.trans hR
  have hdProw' : d.val.val (seamComplementFirst d.val) = b.val.val (seamComplementSecond b.val) :=
    hdProw.trans hcR
  have hdQrow' : d.val.val (seamComplementSecond d.val) =
      b.val.val (seamComplementThird b.val h3b) :=
    hdQrow.trans hcQ
  have hdE : d.val.val u.left = b.val.val (seamComplementFirst b.val) := by
    have hh := u.map_left
    rw [seamComplementPartner_firstBlock_apply d.val u.left huL, huR, hcP] at hh
    exact hh
  have hdD : d.val.val D = u.bottom := by
    rw [bottom_def]
    have hh := u.map_right
    rw [huR, hP] at hh
    change d.val.val.swapColumns (seamComplementFirst d.val)
      (seamComplementSecond d.val) D = _ at hh
    simpa only [hdP', hdQ', GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hDP.ne (hDP.trans hPQ).ne] using hh
  have hdRemoved : d.val.val (seamComplementThird b.val h3b) = b.val.val D := by
    have hh := u.map_of_ne (seamComplementThird b.val h3b)
      (by intro h; have := congrArg Fin.val h; omega)
      (by rw [huR, hP]; exact (hDP.trans hPR).ne.symm)
    change d.val.val.swapColumns (seamComplementFirst d.val)
      (seamComplementSecond d.val) _ = _ at hh
    simpa only [hdP', hdQ', GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hPR.ne.symm hQR.ne.symm, hcRemoved] using hh
  have huTop : u.top = b.val.val (seamComplementFirst b.val) := by rw [top_def, huR, hcP]
  have huHigh : n < u.bottom.val := by
    rcases seamMatchingDeath_ranges u hd with h | h
    · exact h.2.2.2
    · have hn := h.2.1
      omega
  have hsource : (b.val.val (seamComplementFirst b.val)).val <
      (b.val.val (seamComplementSecond b.val)).val := b.property
  have hfirstBlock (A : Fin (n + m + 1)) (hAn : A.val < n) (hAv : n < (d.val.val A).val) :
      c.val.val A = d.val.val A ∧ b.val.val A = d.val.val A := by
    have hAE : A ≠ u.left := by intro h; rw [h, hdE] at hAv; omega
    have hAD : A ≠ D := by intro h; have := congrArg Fin.val h; omega
    have hh := u.map_of_ne A hAE (by rw [huR, hP]; exact hAD)
    rw [seamComplementPartner_firstBlock_apply d.val A hAn] at hh
    have hh' := t.map_of_ne A
      (by rw [htL]; intro h; have := congrArg Fin.val h; omega) (by rwa [htR])
    rw [seamComplementPartner_firstBlock_apply c.val A hAn] at hh'
    exact ⟨hh.symm, hh'.symm.trans hh.symm⟩
  rcases seamMatchingExit_endpoints q d f hf with hF | hF
  · obtain ⟨hFn, hfR, hfTop, hfHigh⟩ := hF
    have hFH : n < (d.val.val f.left).val := hfHigh
    obtain ⟨hcF, _⟩ := hfirstBlock f.left hFn hFH
    have hFE : f.left ≠ u.left := by intro h; rw [h, hdE] at hFH; omega
    have hFEv : f.left.val ≠ u.left.val := fun h => hFE (Fin.ext h)
    by_cases hFElt : f.left.val < u.left.val
    · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf u.left
      · rw [Grid.mem_cIoo, hfR, hdP', if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, hFElt, by omega⟩
      · rw [Grid.mem_cIoo, hfTop, hdProw', bottom_def, hdE, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr hsource⟩
    · have hEF : u.left.val < f.left.val := by omega
      by_cases hEFrow : u.bottom.val < (c.val.val f.left).val
      · apply (isEmpty_iff_forall_notMem_cIoo u).mp hu f.left
        · rw [Grid.mem_cIoo, huR, hP, if_pos (by omega)]
          exact ⟨by intro h; have := congrArg Fin.val h; omega, hEF, by omega⟩
        · rw [Grid.mem_cIoo, huTop, if_neg (by omega)]
          exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hEFrow⟩
      · have hrowsNe : (c.val.val f.left).val ≠ u.bottom.val := by
          intro h
          exact hFE (c.val.val.toPerm.injective (Fin.ext h))
        have hFlt : (d.val.val f.left).val < u.bottom.val := by rw [← hcF]; omega
        apply (isEmpty_iff_forall_notMem_cIoo f).mp hf D
        · rw [Grid.mem_cIoo, hfR, hdP', if_pos (by omega)]
          exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hDP⟩
        · rw [Grid.mem_cIoo, hfTop, hdProw', bottom_def, hdD, if_neg (by omega)]
          exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hFlt⟩
  · obtain ⟨hFn, hfL, hfBottom, hfHigh⟩ := hF
    have hFH : n < (d.val.val f.right).val := hfHigh
    obtain ⟨_, hbF⟩ := hfirstBlock f.right hFn hFH
    have hheight := plateau_wrap_high_gt t ht
      (by rw [htR, htL]; exact hDP.trans hPR) (by rwa [htR])
      (by simpa only [bottom_def, htL] using hr.2)
      (by simpa only [top_def, htR] using hDv) f.right hFn (by rwa [hbF])
    simp only [top_def, htR, hbF] at hheight
    apply (isEmpty_iff_forall_notMem_cIoo f).mp hf (seamComplementThird b.val h3b)
    · rw [Grid.mem_cIoo, hfL, hdQ', if_neg (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hQR⟩
    · rw [Grid.mem_cIoo, hfBottom, hdQrow', top_def, hdRemoved, if_pos (by omega)]
      exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hheight⟩

end OnLeConjecture.KnotFloer.GridFull
