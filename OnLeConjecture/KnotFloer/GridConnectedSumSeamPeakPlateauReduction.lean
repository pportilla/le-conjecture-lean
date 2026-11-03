/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakPlateauHighBarriers

/-! # The remaining birth, neutral step, and death configurations -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The middle high exchange cannot remove the second southwest point. -/
theorem seamPeakPlateau_high_second_false (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (hcard : (seamSouthwestColumns b.val.val).card = 3)
    (hcard' : (seamSouthwestColumns c.val.val).card = 3)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (b.val.val D).val)
    (hsides : (t.left = seamComplementSecond b.val ∧ t.right = D) ∨
      (t.right = seamComplementSecond b.val ∧ t.left = D)) : False := by
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by omega
  have h3c : 3 ≤ (seamSouthwestColumns c.val.val).card := by omega
  have hbirthrow := seamMatchingBirth_first_lt_third a b r hr hb h3b
  obtain ⟨htL, htR, hDP, hP, hQ, hR⟩ :=
    seamPlateau_high_second t ht hcard hcard' hbirthrow D hDn hDv hsides
  rcases seamMatchingBirth_endpoints a b r hr hb with hB | hB
  · exact seamPlateau_high_before_first_after_nonwrap_birth_false a b c r t hr ht hb hB.1
      (by rw [htL]; exact seamComplementSecond_mem b.val)
      (by rwa [htR]) (by simpa only [top_def, htR] using hDv) (by rwa [htR])
  have hPmap : c.val.val (seamComplementFirst c.val) =
      b.val.val (seamComplementFirst b.val) := by
    have hh := t.map_of_ne (seamComplementFirst b.val)
      (by rw [htL]; exact (seamComplementFirst_lt_second b.val).ne)
      (by rw [htR]; exact hDP.ne.symm)
    rw [← hQ, seamComplementPartner_apply_second, hQ] at hh
    exact hh
  have hQmap : c.val.val (seamComplementSecond c.val) =
      b.val.val (seamComplementSecond b.val) := by
    have hh := t.map_right
    rw [htR, htL, ← hP, seamComplementPartner_apply_first] at hh
    exact hh
  have hRmap : c.val.val (seamComplementThird c.val h3c) =
      b.val.val (seamComplementThird b.val h3b) := by
    rw [hR]
    have hPR := seamComplementFirst_lt_third b.val h3b
    have hQR := seamComplementSecond_lt_third b.val h3b
    have hh := t.map_of_ne (seamComplementThird b.val h3b)
      (by rw [htL]; exact hQR.ne.symm)
      (by rw [htR]; exact (hDP.trans hPR).ne.symm)
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) _ = _ at hh
    simpa only [hP, hQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (hDP.trans hPR).ne.symm hPR.ne.symm] using hh
  rcases seamMatchingDeath_endpoints c d u hu hd with hD | hD
  · have hh := hD.2.2.2.2.2.2.2.2.2
    rw [hRmap, hQmap, seamMatchingBirth_third_row a b r hr hb h3b,
      hB.2.2.2.2.2.2.2.1] at hh
    have ha : (a.val.val (seamComplementFirst a.val)).val <
        (a.val.val (seamComplementSecond a.val)).val := a.property
    omega
  · have hh := hD.2.2.2.2.2.2.2.2.2
    rw [hRmap, hPmap] at hh
    omega

/-- A middle high exchange at the third point forces a wrapping birth and a
nonwrapping death. -/
theorem seamPeakPlateau_high_third_orientations (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (hcard : (seamSouthwestColumns b.val.val).card = 3)
    (hcard' : (seamSouthwestColumns c.val.val).card = 3)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (b.val.val D).val)
    (hsides : (t.left = seamComplementThird b.val (by omega) ∧ t.right = D) ∨
      (t.right = seamComplementThird b.val (by omega) ∧ t.left = D)) :
    r.right.val < n ∧ u.left.val < n := by
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by omega
  have h3c : 3 ≤ (seamSouthwestColumns c.val.val).card := by omega
  have hbirthrow := seamMatchingBirth_first_lt_third a b r hr hb h3b
  obtain ⟨htL, htR, hDP, hP, hQ, hR⟩ :=
    seamPlateau_high_third t ht hcard hcard' hbirthrow D hDn hDv hsides
  have hrR : r.right.val < n := by
    rcases seamMatchingBirth_endpoints a b r hr hb with hB | hB
    · exact False.elim (seamPlateau_high_before_first_after_nonwrap_birth_false
        a b c r t hr ht hb hB.1
        (by rw [htL]; exact seamComplementThird_mem b.val h3b)
        (by rwa [htR]) (by simpa only [top_def, htR] using hDv) (by rwa [htR]))
    · exact hB.1
  refine ⟨hrR, ?_⟩
  rcases seamMatchingDeath_endpoints c d u hu hd with hD | hD
  · exact hD.1
  exfalso
  have hPmap : c.val.val (seamComplementFirst c.val) =
      b.val.val (seamComplementFirst b.val) := by
    have hh := t.map_of_ne (seamComplementFirst b.val)
      (by rw [htL]; exact (seamComplementFirst_lt_third b.val h3b).ne)
      (by rw [htR]; exact hDP.ne.symm)
    rw [← hQ, seamComplementPartner_apply_second, hQ] at hh
    exact hh
  have hRmap : c.val.val (seamComplementThird c.val h3c) =
      b.val.val (seamComplementSecond b.val) := by
    rw [hR]
    have hPQ := seamComplementFirst_lt_second b.val
    have hQR := seamComplementSecond_lt_third b.val h3b
    have hh := t.map_of_ne (seamComplementSecond b.val)
      (by rw [htL]; exact hQR.ne)
      (by rw [htR]; exact (hDP.trans hPQ).ne.symm)
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) _ = _ at hh
    simpa only [hP, hQ, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (hDP.trans hPQ).ne.symm hPQ.ne.symm] using hh
  have hh := hD.2.2.2.2.2.2.2.2.2
  rw [hRmap, hPmap] at hh
  have hsource : (b.val.val (seamComplementFirst b.val)).val <
      (b.val.val (seamComplementSecond b.val)).val := b.property
  omega

/-- A middle high exchange at the first point inserts beyond the third point,
and forces a nonwrapping birth followed by a wrapping death. -/
theorem seamPeakPlateau_high_first_orientations (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (hcard : (seamSouthwestColumns b.val.val).card = 3)
    (hcard' : (seamSouthwestColumns c.val.val).card = 3)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (b.val.val D).val)
    (hsides : (t.left = seamComplementFirst b.val ∧ t.right = D) ∨
      (t.right = seamComplementFirst b.val ∧ t.left = D)) :
    r.left.val < n ∧ u.right.val < n ∧ seamComplementThird b.val (by omega) < D ∧
      seamComplementFirst c.val = seamComplementSecond b.val ∧
      seamComplementSecond c.val = seamComplementThird b.val (by omega) ∧
      seamComplementThird c.val (by omega) = D := by
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by omega
  have h3c : 3 ≤ (seamSouthwestColumns c.val.val).card := by omega
  have hbirthrow := seamMatchingBirth_first_lt_third a b r hr hb h3b
  obtain ⟨htL, htR, hQD, hcase⟩ := seamPlateau_high_first t ht hcard hcard' D hDn hDv hsides
  have hP : seamComplementFirst c.val = seamComplementSecond b.val := by
    rcases hcase with h | h <;> exact h.2.1
  have hpq := seamComplementFirst_lt_second b.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  have hUnot : ¬ u.left.val < n := by
    intro hU
    apply seamPlateau_high_first_before_nonwrap_death_false b c d t u ht hu hd hU
    · rwa [htL]
    · simpa only [htR] using hp.1
    · simpa only [bottom_def, htL] using hDv
    · simpa only [top_def, htR] using hp.2
    · rw [htR, htL]; exact hpq.trans hQD
    · rw [htR, hP]; exact hpq
  rcases seamMatchingDeath_endpoints c d u hu hd with hU | hU
  · exact False.elim (hUnot hU.1)
  rcases hcase with ⟨hDR, _, hQ, hR⟩ | ⟨hRD, _, hQ, hR, hrows⟩
  · exfalso
    have hPmap : c.val.val (seamComplementFirst c.val) =
        b.val.val (seamComplementFirst b.val) := by
      have hh := t.map_left
      rw [htL, htR, ← hQ, seamComplementPartner_apply_second] at hh
      exact hh
    have hRmap : c.val.val (seamComplementThird c.val h3c) =
        b.val.val (seamComplementThird b.val h3b) := by
      rw [hR]
      have hPR := seamComplementFirst_lt_third b.val h3b
      have hQR := seamComplementSecond_lt_third b.val h3b
      have hh := t.map_of_ne (seamComplementThird b.val h3b)
        (by rw [htL]; exact hDR.ne.symm) (by rw [htR]; exact hPR.ne.symm)
      change c.val.val.swapColumns (seamComplementFirst c.val)
        (seamComplementSecond c.val) _ = _ at hh
      simpa only [hP, hQ, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hQR.ne.symm hDR.ne.symm] using hh
    have hh := hU.2.2.2.2.2.2.2.2.2
    rw [hRmap, hPmap] at hh
    omega
  · refine ⟨?_, hU.1, hRD, hP, hQ, hR⟩
    rcases seamMatchingBirth_endpoints a b r hr hb with hB | hB
    · exact hB.1
    · exfalso
      rw [seamMatchingBirth_third_row a b r hr hb h3b,
        hB.2.2.2.2.2.2.2.1] at hrows
      have ha : (a.val.val (seamComplementFirst a.val)).val <
          (a.val.val (seamComplementSecond a.val)).val := a.property
      omega

/-- Only the two indicated high exchanges can occur between an actual birth
and death at southwest count three. Entry and exit conditions are not used. -/
theorem seamPeakPlateau_middle_cases (a b c d : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty) (hu : u.IsEmpty) (hne : b ≠ c)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (hcard : (seamSouthwestColumns b.val.val).card = 3)
    (hcard' : (seamSouthwestColumns c.val.val).card = 3) :
    ∃ D : Fin (n + m + 1), n ≤ D.val ∧ n < (b.val.val D).val ∧
      ((r.left.val < n ∧ t.left = D ∧ t.right = seamComplementFirst b.val ∧
        seamComplementThird b.val (by omega) < D ∧ u.right.val < n ∧
        seamComplementFirst c.val = seamComplementSecond b.val ∧
        seamComplementSecond c.val = seamComplementThird b.val (by omega) ∧
        seamComplementThird c.val (by omega) = D) ∨
      (r.right.val < n ∧ t.left = seamComplementThird b.val (by omega) ∧ t.right = D ∧
        D < seamComplementFirst b.val ∧ u.left.val < n ∧
        seamComplementFirst c.val = D ∧ seamComplementSecond c.val = seamComplementFirst b.val ∧
        seamComplementThird c.val (by omega) = seamComplementSecond b.val)) := by
  have h3b : 3 ≤ (seamSouthwestColumns b.val.val).card := by omega
  obtain ⟨S, D, hS, hDn, hDv, hsides⟩ :=
    seamPeakPlateau_middle_high a b c d r t u hr ht hu hne hb hd hcard hcard'
  refine ⟨D, hDn, hDv, ?_⟩
  rcases hS with rfl | rfl | rfl
  · obtain ⟨hL, hR, _, _⟩ := seamPlateau_high_first t ht hcard hcard' D hDn hDv hsides
    obtain ⟨hrL, huR, hRD, hP, hQ, hR'⟩ :=
      seamPeakPlateau_high_first_orientations a b c d r t u hr ht hu hb hd
        hcard hcard' D hDn hDv hsides
    exact Or.inl ⟨hrL, hL, hR, hRD, huR, hP, hQ, hR'⟩
  · exact False.elim (seamPeakPlateau_high_second_false a b c d r t u hr ht hu hb hd
      hcard hcard' D hDn hDv hsides)
  · obtain ⟨hL, hR, hDP, hP, hQ, hR'⟩ := seamPlateau_high_third t ht hcard hcard'
      (seamMatchingBirth_first_lt_third a b r hr hb h3b) D hDn hDv hsides
    obtain ⟨hrR, huL⟩ := seamPeakPlateau_high_third_orientations a b c d r t u hr ht hu hb hd
      hcard hcard' D hDn hDv hsides
    exact Or.inr ⟨hrR, hL, hR, hDP, huL, hP, hQ, hR'⟩

end OnLeConjecture.KnotFloer.GridFull
