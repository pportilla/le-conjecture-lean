/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamBirthDeath
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPathRewrite

/-!
# Birth/death peaks with arbitrarily many southwest points

Every birth inserts a column before the old second southwest column. The
third column after the insertion is therefore the old second column,
irrespective of the number of other southwest points. This forces every
immediate birth/death peak to use nonwrapping cut orientations. Consecutive
nonwrapping births also have strictly increasing high endpoint rows.

These statements concern actual empty rectangles. They do not assert a
bound on the length of a complete seam correction path.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The third southwest column after any birth is the old second column. -/
theorem seamMatchingBirth_third (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hthree : 3 ≤ (seamSouthwestColumns y.val.val).card) :
    seamComplementThird y.val hthree = seamComplementSecond x.val := by
  classical
  have hpq := seamComplementFirst_lt_second x.val
  have hmin (c : Fin (n + m + 1)) (hc : c ∈ seamSouthwestColumns x.val.val)
      (hne : c ≠ seamComplementFirst x.val) : seamComplementSecond x.val ≤ c :=
    Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hne, hc⟩)
  rcases seamMatchingBirth_endpoints x y r he hb with h | h
  · obtain ⟨_, _, hcp, hs, hf, hsecond, _⟩ := h
    have hcq := hcp.trans hpq
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hf, hsecond, hs]
    simp only [Finset.mem_erase, Finset.mem_insert]
    refine ⟨⟨hpq.ne.symm, hcq.ne.symm, Or.inr (seamComplementSecond_mem x.val)⟩, ?_⟩
    intro c hc
    obtain ⟨hcP, hcC, hc⟩ := hc
    rcases hc with hc | hc
    · exact False.elim (hcC hc)
    · exact hmin c hc hcP
  · obtain ⟨_, hpc, hcq, hs, hf, hsecond, _⟩ := h
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hf, hsecond, hs]
    simp only [Finset.mem_erase, Finset.mem_insert]
    refine ⟨⟨hcq.ne.symm, hpq.ne.symm, Or.inr (seamComplementSecond_mem x.val)⟩, ?_⟩
    intro c hc
    obtain ⟨hcC, hcP, hc⟩ := hc
    rcases hc with hc | hc
    · exact False.elim (hcC hc)
    · exact hmin c hc hcP

/-- A birth preserves the old second point, now the third southwest point. -/
theorem seamMatchingBirth_third_row (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hthree : 3 ≤ (seamSouthwestColumns y.val.val).card) :
    y.val.val (seamComplementThird y.val hthree) = x.val.val (seamComplementSecond x.val) := by
  have ht := seamMatchingBirth_third x y r he hb hthree
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hends : seamComplementSecond x.val ≠ r.left ∧ seamComplementSecond x.val ≠ r.right := by
    rcases seamMatchingBirth_endpoints x y r he hb with h | h
    · exact ⟨by intro hh; have := congrArg Fin.val hh; omega,
        (h.2.2.1.trans hpq).ne.symm⟩
    · exact ⟨h.2.2.1.ne.symm, by intro hh; have := congrArg Fin.val hh; omega⟩
  have hv := r.map_of_ne (seamComplementSecond x.val) hends.1 hends.2
  change y.val.val.swapColumns (seamComplementFirst y.val)
    (seamComplementSecond y.val) (seamComplementSecond x.val) = _ at hv
  have hfirst : seamComplementSecond x.val ≠ seamComplementFirst y.val := by
    rw [← ht]
    exact (seamComplementFirst_lt_third y.val hthree).ne.symm
  have hsecond : seamComplementSecond x.val ≠ seamComplementSecond y.val := by
    rw [← ht]
    exact (seamComplementSecond_lt_third y.val hthree).ne.symm
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hfirst hsecond] at hv
  rwa [ht]

/-- Every immediate internal birth/death peak uses nonwrapping cut orientations. -/
theorem seamMatchingBirthDeath_nonwrap (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1) :
    r.left.val < n ∧ t.left.val < n := by
  let hthree := seamMatchingDeath_three_le_southwest y z hd
  have hv := seamMatchingBirth_third_row x y r he hb hthree
  have hrows : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  rcases seamMatchingBirth_endpoints x y r he hb with hB | hB <;>
    rcases seamMatchingDeath_endpoints y z t ht hd with hD | hD
  · exact ⟨hB.1, hD.1⟩
  · have hbrow := hB.2.2.2.2.2.2.1
    have hdrow := hD.2.2.2.2.2.2.2.2.2
    rw [hv, hbrow] at hdrow
    omega
  · have hbrow := hB.2.2.2.2.2.2.2.1
    have hdrow := hD.2.2.2.2.2.2.2.2.2
    rw [hv, hbrow] at hdrow
    omega
  · have hbrow := hB.2.2.2.2.2.2.2.2.1
    have hdrow := hD.2.2.2.2.2.2.2.2.2
    rw [hv] at hdrow
    omega

/-- A birth/death peak restores the entire southwest column set and its selected columns. -/
theorem seamMatchingBirthDeath_columns (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1) :
    r.right = t.right ∧ seamComplementFirst y.val = r.right ∧
      seamComplementSecond y.val = seamComplementFirst x.val ∧
      seamComplementFirst z.val = seamComplementFirst x.val ∧
      seamComplementSecond z.val = seamComplementSecond x.val ∧
      seamSouthwestColumns z.val.val = seamSouthwestColumns x.val.val := by
  classical
  have hor := seamMatchingBirthDeath_nonwrap x y z r t he ht hb hd
  obtain ⟨_, hcp, hsB, hfB, hsecondB, _⟩ := seamMatchingBirth_nonwrap x y r he hb hor.1
  obtain ⟨hrD, hsD, hfD, hsecondD, _, _, _⟩ :=
    seamMatchingDeath_nonwrap y z t ht hd hor.2
  have hthird := seamMatchingBirth_third x y r he hb
    (seamMatchingDeath_three_le_southwest y z hd)
  have hnot : r.right ∉ seamSouthwestColumns x.val.val := by
    intro hc
    have hmin := Finset.min'_le _ r.right hc
    change seamComplementFirst x.val ≤ r.right at hmin
    exact (not_le_of_gt hcp) hmin
  refine ⟨hfB.symm.trans hrD.symm, hfB, hsecondB, hfD.trans hsecondB,
    hsecondD.trans hthird, ?_⟩
  rw [hsD, hfB, hsB, Finset.erase_insert hnot]

/-- A birth/death peak transports the two selected low rows explicitly. -/
theorem seamMatchingBirthDeath_final_rows (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1) :
    z.val.val (seamComplementFirst z.val) = x.val.val (seamComplementSecond x.val) ∧
      z.val.val (seamComplementSecond z.val) = r.bottom := by
  have hor := seamMatchingBirthDeath_nonwrap x y z r t he ht hb hd
  have hD := seamMatchingDeath_nonwrap y z t ht hd hor.2
  refine ⟨hD.2.2.2.2.1.trans (seamMatchingBirth_third_row x y r he hb _), ?_⟩
  rw [hD.2.2.2.2.2.1]
  rcases seamMatchingBirth_endpoints x y r he hb with h | h
  · exact h.2.2.2.2.2.2.2.1
  · have hh := seamMatchingBirth_ranges r hb
    have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
    have hside := h.2.1
    omega

/-- A birth/death peak preserves every right-block point after the old second column. -/
theorem seamMatchingBirthDeath_tail_apply (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (c : Fin (n + m + 1)) (hqc : seamComplementSecond x.val < c) :
    z.val.val c = x.val.val c := by
  have hor := seamMatchingBirthDeath_nonwrap x y z r t he ht hb hd
  have hcols := seamMatchingBirthDeath_columns x y z r t he ht hb hd
  have hB := seamMatchingBirth_nonwrap x y r he hb hor.1
  have hcp := (seamComplementFirst_lt_second x.val).trans hqc
  have hcr := hB.2.1.trans hcp
  have hcn := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hcl : c ≠ r.left := by intro hh; have := congrArg Fin.val hh; omega
  have hct : c ≠ t.left := by intro hh; have := congrArg Fin.val hh; omega
  have hr := r.map_of_ne c hcl hcr.ne.symm
  have ht' := t.map_of_ne c hct (by rw [← hcols.1]; exact hcr.ne.symm)
  change y.val.val.swapColumns (seamComplementFirst y.val)
    (seamComplementSecond y.val) c = _ at hr
  change z.val.val.swapColumns (seamComplementFirst z.val)
    (seamComplementSecond z.val) c = _ at ht'
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne
    (by rw [hcols.2.1]; exact hcr.ne.symm)
    (by rw [hcols.2.2.1]; exact hcp.ne.symm)] at hr
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne
    (by rw [hcols.2.2.2.1]; exact hcp.ne.symm)
    (by rw [hcols.2.2.2.2.1]; exact hqc.ne.symm)] at ht'
  exact ht'.trans hr

/-- Every preceding right-block column has row above a nonwrapping birth's high endpoint. -/
theorem seamMatchingBirth_nonwrap_prefix_rows_gt
    (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hl : r.left.val < n) (c : Fin (n + m + 1))
    (hcn : n ≤ c.val) (hcr : c < r.right) : r.top.val < (x.val.val c).val := by
  have hB := seamMatchingBirth_nonwrap x y r he hb hl
  have hcp : c < seamComplementFirst x.val := hcr.trans hB.2.1
  have hhigh : n < (x.val.val c).val := by
    by_contra hh
    have hc : c ∈ seamSouthwestColumns x.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨hcn, by omega⟩
    have hmin := Finset.min'_le _ c hc
    change seamComplementFirst x.val ≤ c at hmin
    exact (not_le_of_gt hcp) hmin
  have hc : c ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨fun hh => by have := congrArg Fin.val hh; omega, by omega, hcr⟩
  have hranges := seamMatchingBirth_ranges r hb
  have hrows : r.bottom.val ≤ n ∧ n < r.top.val := by
    rcases hranges with h | h
    · exact h.2.2
    · omega
  have hne : (x.val.val c).val ≠ r.top.val := by
    intro hh
    have hv : x.val.val c = x.val.val r.right := Fin.ext hh
    exact hcr.ne (x.val.val.toPerm.injective hv)
  by_contra hh
  have hlt : (x.val.val c).val < r.top.val := by omega
  apply (isEmpty_iff_forall_notMem_cIoo r).mp he c hc
  rw [Grid.mem_cIoo, if_pos (by omega)]
  exact ⟨fun hh => by have := congrArg Fin.val hh; omega, by omega, hlt⟩

/-- Consecutive nonwrapping births have strictly increasing high endpoint rows. -/
theorem seamMatchingBirth_nonwrap_consecutive_rows_lt
    (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hb' : (seamNortheastColumns z.val.val).card = (seamNortheastColumns y.val.val).card + 1)
    (hl : r.left.val < n) (hl' : t.left.val < n) : r.top.val < t.top.val := by
  have hB := seamMatchingBirth_nonwrap x y r he hb hl
  have hB' := seamMatchingBirth_nonwrap y z t ht hb' hl'
  have hcr : t.right < r.right := by simpa only [hB.2.2.2.1] using hB'.2.1
  have hh := seamMatchingBirth_nonwrap_prefix_rows_gt x y r he hb hl t.right hB'.1 hcr
  have hcl : t.right ≠ r.left := by intro hh; have := congrArg Fin.val hh; omega
  have hfirst : t.right ≠ seamComplementFirst y.val := by
    rw [hB.2.2.2.1]
    exact hcr.ne
  have hsecond : t.right ≠ seamComplementSecond y.val := by
    have hlt := hcr.trans hB.2.1
    rw [hB.2.2.2.2.1]
    exact hlt.ne
  have hv := r.map_of_ne t.right hcl hcr.ne
  change y.val.val.swapColumns (seamComplementFirst y.val)
    (seamComplementSecond y.val) t.right = _ at hv
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hfirst hsecond] at hv
  change r.top.val < (y.val.val t.right).val
  rwa [hv]

end OnLeConjecture.KnotFloer.GridFull
