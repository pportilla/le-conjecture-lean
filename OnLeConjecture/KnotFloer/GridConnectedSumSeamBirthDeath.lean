/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamInternalDeath

/-!
# Geometry of a birth followed by a death

Starting with exactly two southwest points, an empty internal birth
followed by an empty internal death can use only the nonwrapping cut
orientations. The middle third southwest column is the old second
column, and its row lies strictly between the first two middle rows.
No bound on the lengths of arbitrary complete paths is assumed.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- For a birth from two southwest points, the old second point becomes the third. -/
theorem seamTwoStep_birth_third (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2)
    (hthree : 3 ≤ (seamSouthwestColumns y.val.val).card) :
    seamComplementThird y.val hthree = seamComplementSecond x.val := by
  have hpair := seamComplement_southwest_eq_pair_of_card_two x.val hx
  have hpq := seamComplementFirst_lt_second x.val
  rcases seamMatchingBirth_endpoints x y r he hb with h | h
  · have hcp := h.2.2.1
    have hcq := hcp.trans hpq
    have hs := h.2.2.2.1
    have hf := h.2.2.2.2.1
    have hsecond := h.2.2.2.2.2.1
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hf, hsecond, hs, hpair]
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨⟨hpq.ne.symm, hcq.ne.symm, Or.inr (Or.inr True.intro)⟩, ?_⟩
    intro b hh
    obtain ⟨hbP, hbC, hb⟩ := hh
    rcases hb with h | h | rfl
    · exact False.elim (hbC h)
    · exact False.elim (hbP h)
    · exact le_rfl
  · have hpc := h.2.1
    have hcq := h.2.2.1
    have hs := h.2.2.2.1
    have hf := h.2.2.2.2.1
    have hsecond := h.2.2.2.2.2.1
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hf, hsecond, hs, hpair]
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨⟨hcq.ne.symm, hpq.ne.symm, Or.inr (Or.inr True.intro)⟩, ?_⟩
    intro b hh
    obtain ⟨hbC, hbP, hb⟩ := hh
    rcases hb with h | h | rfl
    · exact False.elim (hbC h)
    · exact False.elim (hbP h)
    · exact le_rfl

/-- The third point's row is unchanged by this birth. -/
theorem seamTwoStep_birth_third_row (x y : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2)
    (hthree : 3 ≤ (seamSouthwestColumns y.val.val).card) :
    y.val.val (seamComplementThird y.val hthree) = x.val.val (seamComplementSecond x.val) := by
  have ht := seamTwoStep_birth_third x y r he hb hx hthree
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

/-- A birth followed by a death from a two-point southwest set uses only nonwrapping cut sides. -/
theorem seamTwoStep_birth_death_nonwrap (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) :
    r.left.val < n ∧ t.left.val < n := by
  let hthree := seamMatchingDeath_three_le_southwest y z hd
  have hv := seamTwoStep_birth_third_row x y r he hb hx hthree
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

/-- The selected columns after the two internal rectangles recover their initial values. -/
theorem seamTwoStep_birth_death_columns (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) :
    r.right = t.right ∧ seamComplementFirst y.val = r.right ∧
      seamComplementSecond y.val = seamComplementFirst x.val ∧
      seamComplementFirst z.val = seamComplementFirst x.val ∧
      seamComplementSecond z.val = seamComplementSecond x.val ∧
      seamSouthwestColumns z.val.val = seamSouthwestColumns x.val.val ∧
      seamSouthwestColumns y.val.val =
        {r.right, seamComplementFirst x.val, seamComplementSecond x.val} := by
  have hor := seamTwoStep_birth_death_nonwrap x y z r t he ht hb hd hx
  obtain ⟨_, _, hsB, hfB, hsecondB, _⟩ := seamMatchingBirth_nonwrap x y r he hb hor.1
  obtain ⟨hrD, _, hfD, hsecondD, _, _, _⟩ := seamMatchingDeath_nonwrap y z t ht hd hor.2
  have hthird := seamTwoStep_birth_third x y r he hb hx
    (seamMatchingDeath_three_le_southwest y z hd)
  have hf : seamComplementFirst z.val = seamComplementFirst x.val := hfD.trans hsecondB
  have hsecond : seamComplementSecond z.val = seamComplementSecond x.val :=
    hsecondD.trans hthird
  have hz : (seamSouthwestColumns z.val.val).card = 2 := by
    have hcardX := seamSouthwestColumns_card x.val.val
    have hcardZ := seamSouthwestColumns_card z.val.val
    omega
  refine ⟨hfB.symm.trans hrD.symm, hfB, hsecondB, hf, hsecond, ?_, ?_⟩
  · rw [seamComplement_southwest_eq_pair_of_card_two z.val hz,
      seamComplement_southwest_eq_pair_of_card_two x.val hx, hf, hsecond]
  · rw [hsB, seamComplement_southwest_eq_pair_of_card_two x.val hx]

/-- The middle southwest rows have the strict order first, third, second. -/
theorem seamTwoStep_birth_death_row_order (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) :
    let R := seamComplementThird y.val (seamMatchingDeath_three_le_southwest y z hd)
    (y.val.val (seamComplementFirst y.val)).val < (y.val.val R).val ∧
      (y.val.val R).val < (y.val.val (seamComplementSecond y.val)).val := by
  dsimp only
  have hor := seamTwoStep_birth_death_nonwrap x y z r t he ht hb hd hx
  have hB := seamMatchingBirth_nonwrap x y r he hb hor.1
  have hD := seamMatchingDeath_nonwrap y z t ht hd hor.2
  refine ⟨?_, hD.2.2.2.2.2.2⟩
  rw [seamTwoStep_birth_third_row x y r he hb hx, hB.2.2.2.2.2]
  exact x.property

/-- Exact low-row transport between the initial and final matching sources. -/
theorem seamTwoStep_birth_death_final_rows (x y z : SeamMatchingSource n m)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (he : r.IsEmpty) (ht : t.IsEmpty)
    (hb : (seamNortheastColumns y.val.val).card = (seamNortheastColumns x.val.val).card + 1)
    (hd : (seamNortheastColumns y.val.val).card = (seamNortheastColumns z.val.val).card + 1)
    (hx : (seamSouthwestColumns x.val.val).card = 2) :
    z.val.val (seamComplementFirst z.val) = x.val.val (seamComplementSecond x.val) ∧
      z.val.val (seamComplementSecond z.val) = r.bottom := by
  have hor := seamTwoStep_birth_death_nonwrap x y z r t he ht hb hd hx
  have hD := seamMatchingDeath_nonwrap y z t ht hd hor.2
  refine ⟨hD.2.2.2.2.1.trans (seamTwoStep_birth_third_row x y r he hb hx _), ?_⟩
  rw [hD.2.2.2.2.2.1]
  rcases seamMatchingBirth_endpoints x y r he hb with h | h
  · exact h.2.2.2.2.2.2.2.1
  · have hh := seamMatchingBirth_ranges r hb
    have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
    have hside := h.2.1
    omega

end OnLeConjecture.KnotFloer.GridFull
