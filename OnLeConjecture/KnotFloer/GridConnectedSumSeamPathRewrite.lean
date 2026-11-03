/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamInternalDeath

/-! # Marked-point barriers for seam correction paths

An internal death leaves a high state point in its deleted southwest column.
For nonwrapping deaths this column precedes the next first southwest column.
Emptiness forces a subsequent nonwrapping death to remove a strictly larger
northeast row. These are local consequences of the actual rectangles, not a
confinement or cancellation assumption on whole correction paths.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable {n m : ℕ}

/-- A point before the first southwest column blocks a nonwrapping death
if its row exceeds the northeast row that the death removes. -/
theorem seamMatchingDeath_nonwrap_prefix_rows_le
    (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hd : (seamNortheastColumns x.val.val).card =
      (seamNortheastColumns y.val.val).card + 1)
    (hl : r.left.val < n) (c : Fin (n + m + 1))
    (hcn : n ≤ c.val) (hcp : c < seamComplementFirst x.val) :
    (x.val.val c).val ≤ r.bottom.val := by
  have hr := seamMatchingDeath_right_eq_first_of_left_lt x y r he hd hl
  have hrows : r.top.val ≤ n ∧ n < r.bottom.val := by
    rcases seamMatchingDeath_ranges r hd with h | h
    · exact h.2.2
    · omega
  have hc : c ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_pos (by omega)]
    refine ⟨?_, by omega, ?_⟩
    · intro h
      have := congrArg Fin.val h
      omega
    · rw [hr]
      exact hcp
  by_contra h
  have hhigh : r.bottom.val < (x.val.val c).val := by omega
  apply ((isEmpty_iff_forall_notMem_cIoo r).mp he c hc)
  rw [Grid.mem_cIoo, if_neg (by omega)]
  exact ⟨fun hh => by have := congrArg Fin.val hh; omega, Or.inl hhigh⟩

/-- The deleted southwest column retains the removed northeast row after
the matching inverse, and lies before the next first southwest column. -/
theorem seamMatchingDeath_nonwrap_markedPoint
    (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hd : (seamNortheastColumns x.val.val).card =
      (seamNortheastColumns y.val.val).card + 1)
    (hl : r.left.val < n) :
    n ≤ r.right.val ∧ r.right < seamComplementFirst y.val ∧
      y.val.val r.right = r.bottom := by
  obtain ⟨hr, _, hf, _, _, _, _⟩ := seamMatchingDeath_nonwrap x y r he hd hl
  have hn : n ≤ r.right.val := by
    rw [hr]
    exact ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hlt : r.right < seamComplementFirst y.val := by
    rw [hr, hf]
    exact seamComplementFirst_lt_second x.val
  have hn1 : r.right ≠ seamComplementFirst y.val := ne_of_lt hlt
  have hn2 : r.right ≠ seamComplementSecond y.val :=
    ne_of_lt (hlt.trans (seamComplementFirst_lt_second y.val))
  have hrow := r.map_right
  change y.val.val.swapColumns (seamComplementFirst y.val)
    (seamComplementSecond y.val) r.right = r.bottom at hrow
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hn1 hn2] at hrow
  exact ⟨hn, hlt, hrow⟩

/-- The high point left by one nonwrapping death obstructs a second death
with a smaller removed row. Equality is excluded by state injectivity. -/
theorem seamMatchingDeath_nonwrap_consecutive_rows_lt
    (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (s : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (her : r.IsEmpty) (hes : s.IsEmpty)
    (hdr : (seamNortheastColumns x.val.val).card =
      (seamNortheastColumns y.val.val).card + 1)
    (hds : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1)
    (hlr : r.left.val < n) (hls : s.left.val < n) :
    r.bottom.val < s.bottom.val := by
  obtain ⟨hn, hlt, hrow⟩ := seamMatchingDeath_nonwrap_markedPoint x y r her hdr hlr
  have hle := seamMatchingDeath_nonwrap_prefix_rows_le y z s hes hds hls r.right hn hlt
  rw [hrow] at hle
  apply lt_of_le_of_ne hle
  intro heq
  have hroweq : y.val.val r.right = y.val.val s.left := by
    rw [hrow, ← s.bottom_def]
    exact Fin.ext heq
  have hcol := y.val.val.toPerm.injective hroweq
  have hh := congrArg Fin.val hcol
  omega

end OnLeConjecture.KnotFloer.GridFull
