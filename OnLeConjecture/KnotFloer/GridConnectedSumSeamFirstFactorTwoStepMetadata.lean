/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorTwoStepProjection

/-!
# Boundary and obstruction data for the two-transition projection

These statements concern a specified entry, birth, death and exit with
fixed retained second factor. They identify the recovered first-factor
rectangle and the interior position of the second-factor zero preimage.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section Complete
variable (p q : SeamRetainedIndex n m) (x y z : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (f : GridRectangleBetween z.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns y.val.val).card = 2) (hpq : p.2 = q.2)

include he hr ht hf hmid hpq in
/-- The recovered rectangle retains its first-block endpoint values,
and neither endpoint is last. -/
theorem seamTwoStepFirstRectangle_columns :
    let R := seamTwoStepFirstRectangle p q x y z e r t f he hr ht hf hmid hpq
    R.left.val = r.left.val ∧ R.right.val = e.right.val ∧
      R.left ≠ Fin.last n ∧ R.right ≠ Fin.last n := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hi := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd
    (seamMatchingEntry_southwest_card p x e)
  dsimp only
  simp only [seamTwoStepFirstRectangle, seamRetainedFirstRectangle_left,
    seamRetainedFirstRectangle_right, seamTwoStepFirstFullRectangle, ofSwapColumns_left,
    ofSwapColumns_right, seamFirstFactorIndex, dif_pos hi.1, dif_pos ho.1]
  refine ⟨trivial, trivial, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;>
    simp only [Fin.val_last] at this <;> omega

include he hr ht hf hmid hpq in
/-- The second-factor zero preimage lies strictly between its first and last columns. -/
theorem seamTwoStep_zero_preimage_interior :
    0 < (p.2.toPerm.symm 0).val ∧ (p.2.toPerm.symm 0).val < m := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hP := seamTwoStep_entry_southwest_of_right p x e he ho.1
  have hQ := seamTwoStep_complete_outer_last p q x y z e r t f he hr ht hf hmid hpq
  have hcut := seamTwoStep_complete_inner_cut p q x y z e r t f he hr ht hf hmid hpq
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hi := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd
    (seamMatchingEntry_southwest_card p x e)
  have hCP := (seamMatchingBirth_nonwrap x y r hr hb hi.1).2.1
  have hPQ := seamComplementFirst_lt_second x.val
  change r.right.val < (seamComplementFirst x.val).val at hCP
  change (seamComplementFirst x.val).val < (seamComplementSecond x.val).val at hPQ
  rw [hP, seamRight_val] at hCP hPQ
  omega

include he hr ht hf hmid hpq in
/-- The last first-factor source row lies strictly between the two wrapped rectangle rows. -/
theorem seamTwoStepFirstRectangle_rows :
    let R := seamTwoStepFirstRectangle p q x y z e r t f he hr ht hf hmid hpq
    R.top.val < (p.1 (Fin.last n)).val ∧ (p.1 (Fin.last n)).val < R.bottom.val := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hP := seamTwoStep_entry_southwest_of_right p x e he ho.1
  obtain ⟨hVA, hVB, hVP, _⟩ :=
    seamTwoStepFirst_source_values p q x y z e r t f he hr ht hf hmid hpq
  obtain ⟨_, _, _, _, _, _, hlow1, hlow2, _, _, _⟩ :=
    seamTwoStep_complete_rows p q x y z e r t f he hr ht hf hmid hpq
  let R := seamTwoStepFirstFullRectangle p q x y z e r t f he hr ht hf hmid hpq
  have hside : R.left.val < n ∨ R.right.val < n := Or.inr (by
    simpa only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_right] using ho.1)
  have hbot := congrArg Fin.val (seamRetainedFirstRectangle_bottom_recovery p q R hside)
  have htop := congrArg Fin.val (seamRetainedFirstRectangle_top_recovery p q R hside)
  have hlast := congrArg Fin.val hVP
  rw [hP, seamState_right_of_zero p.1 p.2 (p.2.toPerm.symm 0)
    (p.2.toPerm.apply_symm_apply 0)] at hlast
  simp only [seamLeft_val] at hlast
  simp only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_bottom, ofSwapColumns_top,
    hVA, hVB, seamLeft_val] at hbot htop
  dsimp only
  change (seamRetainedFirstRectangle p q R hside).top.val < _ ∧
    _ < (seamRetainedFirstRectangle p q R hside).bottom.val
  exact ⟨htop.trans_lt (hlow1.trans_eq hlast.symm), hlast.trans_lt (hlow2.trans_eq hbot.symm)⟩

include he hr ht hf hmid hpq in
/-- The seam column obstructs the unique full lift of the recovered empty factor rectangle. -/
theorem seamTwoStepFirstRectangle_lift_not_isEmpty :
    ¬ (seamFirstFactorRectangle
      (seamTwoStepFirstRectangle p q x y z e r t f he hr ht hf hmid hpq) p.2).IsEmpty := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hcut := seamTwoStep_complete_inner_cut p q x y z e r t f he hr ht hf hmid hpq
  have hAB := seamTwoStep_complete_first_columns_lt p q x y z e r t f he hr ht hf hmid hpq
  obtain ⟨hVA, hVB, _, hVC⟩ :=
    seamTwoStepFirst_source_values p q x y z e r t f he hr ht hf hmid hpq
  obtain ⟨_, _, _, _, _, _, hlow1, hlow2, hlow, _, hhigh⟩ :=
    seamTwoStep_complete_rows p q x y z e r t f he hr ht hf hmid hpq
  let R := seamTwoStepFirstFullRectangle p q x y z e r t f he hr ht hf hmid hpq
  have hside : R.left.val < n ∨ R.right.val < n := Or.inr (by
    simpa only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_right] using ho.1)
  let L := seamFirstFactorRectangle (seamRetainedFirstRectangle p q R hside) p.2
  have hLleft : L.left = r.left := by
    calc
      L.left = seamFirstFactorColumn p.2 (seamFirstFactorIndex R.left) := by
        simp only [L, seamFirstFactorRectangle_left, seamRetainedFirstRectangle_left]
      _ = R.left := seamRetainedRectangle_left_recovery p q R hside
      _ = r.left := by simp only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_left]
  have hLright : L.right = e.right := by
    calc
      L.right = seamFirstFactorColumn p.2 (seamFirstFactorIndex R.right) := by
        simp only [L, seamFirstFactorRectangle_right, seamRetainedFirstRectangle_right]
      _ = R.right := seamRetainedRectangle_right_recovery p q R hside
      _ = e.right := by simp only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_right]
  have hLbottom : L.bottom = r.bottom := by rw [bottom_def, hLleft, hVA]
  have hLtop : L.top = e.top := by rw [top_def, hLright, hVB]
  intro hEmpty
  have hh := (isEmpty_iff_forall_notMem_cIoo L).mp hEmpty r.right
  apply hh
  · rw [hLleft, hLright, Grid.mem_cIoo, if_neg (by omega)]
    refine ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl ?_⟩
    have hb : (seamNortheastColumns y.val.val).card =
        (seamNortheastColumns x.val.val).card + 1 := by
      rw [hmid, seamMatchingEntry_northeast_card p x e]
    rcases seamMatchingBirth_ranges r hb with h | h
    · omega
    · omega
  · rw [hVC, hLbottom, hLtop, Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩

end Complete
end OnLeConjecture.KnotFloer.GridFull
