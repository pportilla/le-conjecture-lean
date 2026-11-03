/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepRectangle
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepLift

/-! # Endpoint data for the second one-step rectangle projection -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section LowSecond
variable (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = C))
include he hr hf hCn hCv hsides

/-- Both projected columns precede the final first-factor column, with their original values. -/
theorem seamOneStepSecondRectangle_columns :
    let R := seamOneStepSecondRectangle u v z x y e r f he hr hf C hCn hCv hsides
    R.left.val = e.left.val ∧ R.right.val = C.val ∧
      R.left ≠ Fin.last n ∧ R.right ≠ Fin.last n := by
  have heL := (seamOneStep_same_second_low_second_orientations
    u v z x y e r f he hr hf C hCn hCv hsides).1
  dsimp only
  simp only [seamOneStepSecondRectangle, seamRetainedFirstRectangle_left,
    seamRetainedFirstRectangle_right, seamOneStepSecondFullRectangle, ofSwapColumns_left,
    ofSwapColumns_right, seamFirstFactorIndex, dif_pos hCn, dif_pos heL]
  refine ⟨trivial, trivial, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;>
    simp only [Fin.val_last] at this <;> omega

/-- The final first-factor row again lies strictly between the wrapped endpoint rows. -/
theorem seamOneStepSecondRectangle_rows :
    let R := seamOneStepSecondRectangle u v z x y e r f he hr hf C hCn hCv hsides
    R.top.val < (u (Fin.last n)).val ∧ (u (Fin.last n)).val < R.bottom.val := by
  have hrow := (seamOneStep_low_second r hr C hCn hCv hsides).2.2.1
  have hlast := seamOneStep_low_second_last r hr
    (seamMatchingEntry_southwest_card (u, z) x e) C hCn hCv hsides
  have hzlast := seamOneStep_same_second_low_second_zero
    u v z x y e r f he hr hf C hCn hCv hsides
  obtain ⟨hVC, hVA, hVQ⟩ := seamOneStepSecond_source_values
    u v z x y e r f he hr hf C hCn hCv hsides
  let R := seamOneStepSecondFullRectangle u v z x y e r f he hr hf C hCn hCv hsides
  have hside : R.left.val < n ∨ R.right.val < n := Or.inr (by
    simpa only [R, seamOneStepSecondFullRectangle, ofSwapColumns_right] using hCn)
  have hbot := congrArg Fin.val (seamRetainedFirstRectangle_bottom_recovery (u, z) (v, z) R hside)
  have htop := congrArg Fin.val (seamRetainedFirstRectangle_top_recovery (u, z) (v, z) R hside)
  have hrightlast : seamRight n m (Fin.last m) = Fin.last (n + m) := Fin.ext rfl
  have hlastrow := congrArg Fin.val hVQ
  rw [hlast, ← hrightlast, seamState_right_of_zero u z _ hzlast] at hlastrow
  simp only [seamLeft_val] at hlastrow
  simp only [R, seamOneStepSecondFullRectangle, ofSwapColumns_bottom, ofSwapColumns_top,
    hVC, hVA, seamLeft_val] at hbot htop
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  change _ < _ ∧ _ < _
  change (seamOneStepSecondRectangle
    u v z x y e r f he hr hf C hCn hCv hsides).bottom.val = _ at hbot
  change (seamOneStepSecondRectangle
    u v z x y e r f he hr hf C hCn hCv hsides).top.val = _ at htop
  omega

/-- The recovered rectangle in the second alternative also has an obstructed direct lift. -/
theorem seamOneStepSecondRectangle_blocked :
    ¬ (seamFirstFactorRectangle
      (seamOneStepSecondRectangle u v z x y e r f he hr hf C hCn hCv hsides) z).IsEmpty := by
  have hcut := seamOneStep_same_second_low_second_cut
    u v z x y e r f he hr hf C hCn hCv hsides
  have hlast := seamOneStep_low_second_last r hr
    (seamMatchingEntry_southwest_card (u, z) x e) C hCn hCv hsides
  have hpq := seamComplementFirst_lt_second x.val
  rw [hcut, hlast] at hpq
  have hm : 0 < m := by
    simp only [Fin.lt_def, seamRight_val, Fin.val_zero, Fin.val_last, Nat.add_zero] at hpq
    omega
  have hzlast := seamOneStep_same_second_low_second_zero
    u v z x y e r f he hr hf C hCn hCv hsides
  have hz0 : z 0 ≠ 0 := by
    intro hh
    have hh' := z.toPerm.injective (hh.trans hzlast.symm)
    have := congrArg Fin.val hh'
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  let R := seamOneStepSecondFullRectangle u v z x y e r f he hr hf C hCn hCv hsides
  have hside : R.left.val < n ∨ R.right.val < n := Or.inr (by
    simpa only [R, seamOneStepSecondFullRectangle, ofSwapColumns_right] using hCn)
  change ¬ (seamFirstFactorRectangle (seamRetainedFirstRectangle (u, z) (v, z) R hside) z).IsEmpty
  rw [seamFirstFactorRectangle_lift_project]
  intro hempty
  obtain ⟨heL, _, _, hCA⟩ := seamOneStep_same_second_low_second_orientations
    u v z x y e r f he hr hf C hCn hCv hsides
  obtain ⟨hVC, hVA, _⟩ := seamOneStepSecond_source_values
    u v z x y e r f he hr hf C hCn hCv hsides
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).2
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hrow := (seamOneStep_low_second r hr C hCn hCv hsides).2.2.1
  apply (isEmpty_iff_forall_notMem_cIoo R).mp hempty (seamRight n m 0)
  · simp only [R, seamOneStepSecondFullRectangle, ofSwapColumns_left, ofSwapColumns_right,
      Grid.mem_cIoo, seamRight_val, Fin.val_zero, Nat.add_zero]
    rw [if_neg (by omega)]
    exact ⟨hCA.ne.symm, Or.inl (by omega)⟩
  · simp only [R, seamOneStepSecondFullRectangle, ofSwapColumns_bottom, ofSwapColumns_top,
      hVC, hVA, seamState_right_of_ne_zero u z _ hz0, Grid.mem_cIoo, seamRight_val]
    rw [if_neg (by omega)]
    have hzpos : 0 < (z 0).val := Fin.pos_iff_ne_zero.mpr hz0
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩

end LowSecond
end OnLeConjecture.KnotFloer.GridFull
