/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakPlateauHigh

/-! # Empty-rectangle barriers for high neutral exchanges -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A high neutral insertion before the first southwest column cannot follow a
nonwrapping birth: the inserted high point would lie inside the birth rectangle. -/
theorem seamPlateau_high_before_first_after_nonwrap_birth_false
    (a b c : SeamMatchingSource n m)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns b.val.val).card = (seamNortheastColumns a.val.val).card + 1)
    (hrL : r.left.val < n)
    (hS : t.left ∈ seamSouthwestColumns b.val.val)
    (hDn : n ≤ t.right.val) (hDv : n < t.top.val)
    (hD : t.right < seamComplementFirst b.val) : False := by
  obtain ⟨hSn, hSv⟩ := (mem_seamSouthwestColumns _ _).mp hS
  have hmin : seamComplementFirst b.val ≤ t.left := Finset.min'_le _ _ hS
  obtain ⟨hrR, _, _, hfirst, _, _⟩ := seamMatchingBirth_nonwrap a b r hr hb hrL
  have hranges : r.bottom.val ≤ n ∧ n < r.top.val := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2
    · omega
  have hE : b.val.val r.left = r.top := by
    have hh := r.map_left
    rwa [seamComplementPartner_firstBlock_apply b.val r.left hrL] at hh
  have hDL : t.right ≠ r.left := by intro h; have := congrArg Fin.val h; omega
  have hDR : t.right ≠ r.right := by rw [← hfirst]; exact hD.ne
  have haD : a.val.val t.right = b.val.val t.right := by
    have hh := r.map_of_ne t.right hDL hDR
    change b.val.val.swapColumns (seamComplementFirst b.val)
      (seamComplementSecond b.val) t.right = _ at hh
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hD.ne
      (hD.trans (seamComplementFirst_lt_second b.val)).ne] at hh
    exact hh.symm
  have hrowne : t.top.val ≠ r.top.val := by
    intro hh
    have hval : b.val.val t.right = b.val.val r.left := by
      rw [hE]
      exact Fin.ext hh
    exact hDL (b.val.val.toPerm.injective hval)
  have hheight : t.top.val < r.top.val := by
    by_contra hh
    have hlt : r.top.val < t.top.val := by omega
    apply (isEmpty_iff_forall_notMem_cIoo t).mp ht r.left
    · rw [Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨t.left_ne_right, Or.inr (by omega)⟩
    · rw [Grid.mem_cIoo, if_pos (by change (b.val.val t.left).val < t.top.val; omega), hE]
      exact ⟨t.bottom_ne_top, by change (b.val.val t.left).val < r.top.val; omega, hlt⟩
  apply (isEmpty_iff_forall_notMem_cIoo r).mp hr t.right
  · rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨r.left_ne_right, by omega, by rwa [← hfirst]⟩
  · rw [Grid.mem_cIoo, if_pos (by omega), haD]
    exact ⟨r.bottom_ne_top, by change r.bottom.val < t.top.val; omega, hheight⟩

/-- A high neutral exchange removing a column before the new first southwest
column cannot precede a nonwrapping death. The removed point blocks that death. -/
theorem seamPlateau_high_first_before_nonwrap_death_false
    (b c d : SeamMatchingSource n m)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (u : GridRectangleBetween c.val.val (seamComplementPartner d.val).val)
    (ht : t.IsEmpty) (hu : u.IsEmpty)
    (hd : (seamNortheastColumns c.val.val).card = (seamNortheastColumns d.val.val).card + 1)
    (huL : u.left.val < n)
    (htLn : n ≤ t.left.val) (htRn : n ≤ t.right.val)
    (htB : n < t.bottom.val) (htT : t.top.val ≤ n)
    (htcols : t.right < t.left) (hbefore : t.right < seamComplementFirst c.val) : False := by
  obtain ⟨huR, _, _, _, _, _, _⟩ := seamMatchingDeath_nonwrap c d u hu hd huL
  have hcP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem c.val)
  have hhigh : n < (c.val.val u.left).val := by
    rcases seamMatchingDeath_ranges u hd with h | h
    · exact h.2.2.2
    · omega
  have hEL : u.left ≠ t.left := by intro h; have := congrArg Fin.val h; omega
  have hER : u.left ≠ t.right := by intro h; have := congrArg Fin.val h; omega
  have hE : b.val.val u.left = c.val.val u.left := by
    have hh := t.map_of_ne u.left hEL hER
    rw [seamComplementPartner_firstBlock_apply c.val u.left huL] at hh
    exact hh.symm
  have hremoved : c.val.val t.right = t.bottom := by
    have hh := t.map_right
    change c.val.val.swapColumns (seamComplementFirst c.val)
      (seamComplementSecond c.val) t.right = _ at hh
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hbefore.ne
      (hbefore.trans (seamComplementFirst_lt_second c.val)).ne] at hh
    exact hh
  have hrowne : (b.val.val u.left).val ≠ t.bottom.val := by
    intro hh
    exact hEL (b.val.val.toPerm.injective (Fin.ext hh))
  have hheight : (b.val.val u.left).val < t.bottom.val := by
    by_contra hh
    have hlt : t.bottom.val < (b.val.val u.left).val := by omega
    apply (isEmpty_iff_forall_notMem_cIoo t).mp ht u.left
    · rw [Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨t.left_ne_right, Or.inr (by omega)⟩
    · rw [Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨t.bottom_ne_top, Or.inl hlt⟩
  apply (isEmpty_iff_forall_notMem_cIoo u).mp hu t.right
  · rw [Grid.mem_cIoo, huR, if_pos (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by omega, hbefore⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, huR, if_neg (by omega), hremoved]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by rwa [← hE])⟩

end OnLeConjecture.KnotFloer.GridFull
