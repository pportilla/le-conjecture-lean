/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepBoundary

/-! # First-factor rectangles recovered from one-step corrections

The two surviving low-point alternatives recover a retained transposition
between their two first-block columns. Projection then gives a first-factor
rectangle. Its emptiness is checked using the actual three path rectangles.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section LowFirst
variable (u v : GridState (n + 1)) (z : GridState (m + 1)) (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState u z) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState v z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty)
    (C : Fin (n + m + 1)) (hCn : C.val < n) (hCv : (x.val.val C).val ≤ n)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = C))
include he hr hf hCn hCv hsides

/-- The three path rectangles recover the retained transposition on the two first-block columns. -/
theorem seamOneStepFirst_target_eq_swap :
    seamState v z = (seamState u z).swapColumns C e.right := by
  obtain ⟨hrL, hrR, _, hYfirst, hYsecond, _, _, _⟩ :=
    seamOneStep_low_first r hr C hCn hCv hsides
  obtain ⟨heR, hfR, hAeq, hAC⟩ :=
    seamOneStep_same_second_low_first_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hCP : C ≠ seamComplementFirst x.val := by intro h; have := congrArg Fin.val h; omega
  have hCQ : C ≠ seamComplementSecond x.val := by intro h; have := congrArg Fin.val h; omega
  have heQ := seamMatchingEntry_left_eq_second_of_right_lt (u, z) x e he heR
  have hfQ := (seamMatchingExit_left_eq_second_of_right_lt (v, z) y f hf hfR).trans hYsecond
  have hpY : (seamComplementPartner y.val).val =
      y.val.val.swapColumns (seamComplementFirst x.val) (seamComplementSecond x.val) := by
    change y.val.val.swapColumns (seamComplementFirst y.val) (seamComplementSecond y.val) = _
    rw [hYfirst, hYsecond]
  have hY : y.val.val = (x.val.val.swapColumns C (seamComplementFirst x.val)).swapColumns
      (seamComplementFirst x.val) (seamComplementSecond x.val) := by
    have hh := r.target_eq_swapColumns
    simp only [hpY, hrL, hrR] at hh
    calc
      _ = (y.val.val.swapColumns (seamComplementFirst x.val)
          (seamComplementSecond x.val)).swapColumns (seamComplementFirst x.val)
          (seamComplementSecond x.val) := (GridState.swapColumns_swapColumns _ _ _).symm
      _ = _ := congrArg (fun w => w.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val)) hh
  have hV := seamMatchingEntry_source_eq_swaps (u, z) x e
  rw [heQ] at hV
  calc
    seamState v z = ((x.val.val.swapColumns C (seamComplementFirst x.val)).swapColumns
        (seamComplementFirst x.val) (seamComplementSecond x.val)).swapColumns
        (seamComplementSecond x.val) e.right := by
      rw [f.target_eq_swapColumns, hfQ, ← hAeq, hY]
    _ = ((x.val.val.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val)).swapColumns
        (seamComplementSecond x.val) e.right).swapColumns C e.right := by
      rw [GridState.swapColumns_swapColumns_conj x.val.val C (seamComplementFirst x.val)
          (seamComplementFirst x.val) (seamComplementSecond x.val),
        Equiv.swap_apply_of_ne_of_ne hCP hCQ, Equiv.swap_apply_left,
        GridState.swapColumns_swapColumns_conj
          (x.val.val.swapColumns (seamComplementFirst x.val) (seamComplementSecond x.val))
          C (seamComplementSecond x.val) (seamComplementSecond x.val) e.right,
        Equiv.swap_apply_of_ne_of_ne hCQ hAC.ne.symm, Equiv.swap_apply_left]
    _ = _ := congrArg (fun w => w.swapColumns C e.right) hV.symm

/-- The retained rectangle determined by the first-southwest low exchange. -/
def seamOneStepFirstFullRectangle : GridRectangleBetween (seamState u z) (seamState v z) :=
  ofSwapColumns _ _ C e.right
    (seamOneStep_same_second_low_first_orientations
      u v z x y e r f he hr hf C hCn hCv hsides).2.2.2.ne.symm
    (seamOneStepFirst_target_eq_swap u v z x y e r f he hr hf C hCn hCv hsides)

/-- Its concrete first-factor projection. -/
def seamOneStepFirstRectangle : GridRectangleBetween u v :=
  seamRetainedFirstRectangle (u, z) (v, z)
    (seamOneStepFirstFullRectangle u v z x y e r f he hr hf C hCn hCv hsides)
    (Or.inl (by simpa only [seamOneStepFirstFullRectangle, ofSwapColumns_left] using hCn))

/-- The source rows at the two projected endpoints and the shared column. -/
theorem seamOneStepFirst_source_values :
    seamState u z C = x.val.val C ∧
      seamState u z e.right = x.val.val (seamComplementFirst x.val) ∧
      seamState u z (seamComplementFirst x.val) = x.val.val (seamComplementSecond x.val) := by
  obtain ⟨heR, _, _, hAC⟩ :=
    seamOneStep_same_second_low_first_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have heQ := seamMatchingEntry_left_eq_second_of_right_lt (u, z) x e he heR
  refine ⟨?_, ?_, ?_⟩
  · have hh := e.map_of_ne C
      (by rw [heQ]; intro h; have := congrArg Fin.val h; omega) hAC.ne.symm
    rw [seamComplementPartner_firstBlock_apply x.val C hCn] at hh
    exact hh.symm
  · have hh := e.map_left
    rw [heQ, seamComplementPartner_apply_second] at hh
    exact hh.symm
  · have hh := e.map_of_ne (seamComplementFirst x.val)
      (by rw [heQ]; exact seamComplementFirst_ne_second x.val)
      (by intro h; have := congrArg Fin.val h; omega)
    rw [seamComplementPartner_apply_first] at hh
    exact hh.symm

/-- The three path emptiness conditions imply emptiness of the first-factor projection. -/
theorem seamOneStepFirstRectangle_isEmpty :
    (seamOneStepFirstRectangle u v z x y e r f he hr hf C hCn hCv hsides).IsEmpty := by
  obtain ⟨hrL, hrR, hrow, hYfirst, hYsecond, _, hyQ, _⟩ :=
    seamOneStep_low_first r hr C hCn hCv hsides
  obtain ⟨heR, hfR, hAeq, hAC⟩ :=
    seamOneStep_same_second_low_first_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hcut := seamOneStep_low_first_cut r hr C hCn hCv hsides
  have hz0 := seamOneStep_same_second_low_first_zero u v z x y e r f he hr hf C hCn hCv hsides
  have hzpre : z.toPerm.symm 0 = 0 := z.toPerm.symm_apply_eq.mpr hz0.symm
  have heQ := seamMatchingEntry_left_eq_second_of_right_lt (u, z) x e he heR
  have hfQ := (seamMatchingExit_left_eq_second_of_right_lt (v, z) y f hf hfR).trans hYsecond
  obtain ⟨heTop, heBot, heHigh⟩ :
      e.top = x.val.val (seamComplementFirst x.val) ∧
      e.bottom = x.val.val e.right ∧ n < e.bottom.val := by
    rcases seamMatchingEntry_endpoints (u, z) x e he with h | h
    · have hh := congrArg Fin.val h.2.1; omega
    · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hhighA : n < (x.val.val e.right).val := by rwa [heBot] at heHigh
  have hyA := seamOneStep_low_high_point r
    (by simpa only [bottom_def, hrL] using hCv)
    (by simpa only [top_def, hrR] using hp.2) e.right heR hhighA
  obtain ⟨hVC, hVA, hVP⟩ := seamOneStepFirst_source_values u v z x y e r f he hr hf C hCn hCv hsides
  let R := seamOneStepFirstFullRectangle u v z x y e r f he hr hf C hCn hCv hsides
  have hside : R.left.val < n ∨ R.right.val < n := Or.inl (by
    simpa only [R, seamOneStepFirstFullRectangle, ofSwapColumns_left] using hCn)
  apply (isEmpty_iff_forall_notMem_cIoo _).mpr
  intro a ha hrowa
  have hcol : seamFirstFactorColumn z a ∈ Grid.cIoo C e.right := by
    have hh : seamFirstFactorColumn z a ∈ Grid.cIoo R.left R.right := by
      rw [← seamRetainedRectangle_left_recovery (u, z) (v, z) R hside,
        ← seamRetainedRectangle_right_recovery (u, z) (v, z) R hside,
        seamFirstFactorColumn_mem_cIoo_iff]
      exact ha
    simpa only [R, seamOneStepFirstFullRectangle, ofSwapColumns_left, ofSwapColumns_right] using hh
  have hval : seamState u z (seamFirstFactorColumn z a) ∈
      Grid.cIoo (x.val.val C) (x.val.val (seamComplementFirst x.val)) := by
    have hh : seamState u z (seamFirstFactorColumn z a) ∈ Grid.cIoo R.bottom R.top := by
      rw [seamState_firstFactorColumn,
        ← seamRetainedFirstRectangle_bottom_recovery (u, z) (v, z) R hside,
        ← seamRetainedFirstRectangle_top_recovery (u, z) (v, z) R hside,
        seamLeft_mem_cIoo_iff]
      exact hrowa
    simpa only [R, seamOneStepFirstFullRectangle, ofSwapColumns_bottom,
      ofSwapColumns_top, hVC, hVA] using hh
  induction a using Fin.lastCases with
  | last =>
    rw [seamFirstFactorColumn_last, hzpre, ← hcut, hVP, Grid.mem_cIoo,
      if_neg (by omega)] at hval
    omega
  | cast d =>
    let c := seamLeft n m d.castSucc
    have hcn : c.val < n := d.isLt
    rw [seamFirstFactorColumn_castSucc] at hcol hval
    change c ∈ Grid.cIoo C e.right at hcol
    change seamState u z c ∈ _ at hval
    have hcols := (Grid.mem_cIoo _ _ _).mp hcol
    rw [if_neg (by omega)] at hcols
    have hcA : c ≠ e.right := by intro hh; have := congrArg Fin.val hh; omega
    have hcC : c ≠ C := by intro hh; have := congrArg Fin.val hh; omega
    have hcP : c ≠ seamComplementFirst x.val := by intro hh; have := congrArg Fin.val hh; omega
    have hcQ : c ≠ seamComplementSecond x.val := by intro hh; have := congrArg Fin.val hh; omega
    have hxc : seamState u z c = x.val.val c := by
      have hh := e.map_of_ne c (by rw [heQ]; exact hcQ) hcA
      rw [seamComplementPartner_firstBlock_apply x.val c hcn] at hh
      exact hh.symm
    have hyc : y.val.val c = x.val.val c := by
      have hh := r.map_of_ne c (by rw [hrL]; exact hcC) (by rw [hrR]; exact hcP)
      rwa [seamComplementPartner_firstBlock_apply y.val c hcn] at hh
    have hvlow : (x.val.val c).val ≤ n := by
      rw [← hxc]
      exact seamPairSector_row_le (seamState_mem_pairSector u z) c hcn
    rcases hcols.2 with hCc | hcA'
    · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr c
      · rw [Grid.mem_cIoo, hrL, hrR, if_pos (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hCc, by omega⟩
      · simpa only [bottom_def, top_def, hrL, hrR, hxc] using hval
    · rw [hxc, Grid.mem_cIoo, if_neg (by omega)] at hval
      rcases hval.2 with hvhigh | hvlow'
      · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c
        · rw [Grid.mem_cIoo, hfQ, ← hAeq, if_neg (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hcA'⟩
        · rw [Grid.mem_cIoo, bottom_def, top_def, hfQ, ← hAeq, hyQ, hyA, hyc,
            if_pos (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hvhigh, by omega⟩
      · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c
        · rw [Grid.mem_cIoo, heQ, if_neg (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hcA'⟩
        · rw [Grid.mem_cIoo, heBot, heTop, hxc, if_neg (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hvlow'⟩


/-- Both projected columns precede the final first-factor column, with their original values. -/
theorem seamOneStepFirstRectangle_columns :
    let R := seamOneStepFirstRectangle u v z x y e r f he hr hf C hCn hCv hsides
    R.left.val = C.val ∧ R.right.val = e.right.val ∧
      R.left ≠ Fin.last n ∧ R.right ≠ Fin.last n := by
  have heR := (seamOneStep_same_second_low_first_orientations
    u v z x y e r f he hr hf C hCn hCv hsides).1
  dsimp only
  simp only [seamOneStepFirstRectangle, seamRetainedFirstRectangle_left,
    seamRetainedFirstRectangle_right, seamOneStepFirstFullRectangle, ofSwapColumns_left,
    ofSwapColumns_right, seamFirstFactorIndex, dif_pos hCn, dif_pos heR]
  refine ⟨trivial, trivial, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;>
    simp only [Fin.val_last] at this <;> omega

/-- The final first-factor row lies strictly between the wrapped endpoint rows. -/
theorem seamOneStepFirstRectangle_rows :
    let R := seamOneStepFirstRectangle u v z x y e r f he hr hf C hCn hCv hsides
    R.top.val < (u (Fin.last n)).val ∧ (u (Fin.last n)).val < R.bottom.val := by
  have hrow := (seamOneStep_low_first r hr C hCn hCv hsides).2.2.1
  have hcut := seamOneStep_low_first_cut r hr C hCn hCv hsides
  have hz0 := seamOneStep_same_second_low_first_zero u v z x y e r f he hr hf C hCn hCv hsides
  obtain ⟨hVC, hVA, hVP⟩ := seamOneStepFirst_source_values u v z x y e r f he hr hf C hCn hCv hsides
  let R := seamOneStepFirstFullRectangle u v z x y e r f he hr hf C hCn hCv hsides
  have hside : R.left.val < n ∨ R.right.val < n := Or.inl (by
    simpa only [R, seamOneStepFirstFullRectangle, ofSwapColumns_left] using hCn)
  have hbot := congrArg Fin.val (seamRetainedFirstRectangle_bottom_recovery (u, z) (v, z) R hside)
  have htop := congrArg Fin.val (seamRetainedFirstRectangle_top_recovery (u, z) (v, z) R hside)
  have hlast := congrArg Fin.val hVP
  rw [hcut, seamState_right_of_zero u z 0 hz0] at hlast
  simp only [seamLeft_val] at hlast
  simp only [R, seamOneStepFirstFullRectangle, ofSwapColumns_bottom, ofSwapColumns_top,
    hVC, hVA, seamLeft_val] at hbot htop
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  change _ < _ ∧ _ < _
  change (seamOneStepFirstRectangle
    u v z x y e r f he hr hf C hCn hCv hsides).bottom.val = _ at hbot
  change (seamOneStepFirstRectangle u v z x y e r f he hr hf C hCn hCv hsides).top.val = _ at htop
  omega

/-- The recovered empty rectangle has an obstructed direct retained lift. -/
theorem seamOneStepFirstRectangle_blocked :
    ¬ (seamFirstFactorRectangle
      (seamOneStepFirstRectangle u v z x y e r f he hr hf C hCn hCv hsides) z).IsEmpty := by
  have hcut := seamOneStep_low_first_cut r hr C hCn hCv hsides
  have hlast := seamOneStep_same_second_low_first_last
    u v z x y e r f he hr hf C hCn hCv hsides
  have hpq := seamComplementFirst_lt_second x.val
  rw [hcut, hlast] at hpq
  have hm : 0 < m := by
    simp only [Fin.lt_def, seamRight_val, Fin.val_zero, Fin.val_last, Nat.add_zero] at hpq
    omega
  have hz0 := seamOneStep_same_second_low_first_zero u v z x y e r f he hr hf C hCn hCv hsides
  have hzlast : z (Fin.last m) ≠ 0 := by
    intro hh
    have hh' := z.toPerm.injective (hh.trans hz0.symm)
    have := congrArg Fin.val hh'
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  let R := seamOneStepFirstFullRectangle u v z x y e r f he hr hf C hCn hCv hsides
  have hside : R.left.val < n ∨ R.right.val < n := Or.inl (by
    simpa only [R, seamOneStepFirstFullRectangle, ofSwapColumns_left] using hCn)
  change ¬ (seamFirstFactorRectangle (seamRetainedFirstRectangle (u, z) (v, z) R hside) z).IsEmpty
  rw [seamFirstFactorRectangle_lift_project]
  intro hempty
  obtain ⟨_, _, _, hAC⟩ := seamOneStep_same_second_low_first_orientations
    u v z x y e r f he hr hf C hCn hCv hsides
  obtain ⟨hVC, hVA, _⟩ := seamOneStepFirst_source_values u v z x y e r f he hr hf C hCn hCv hsides
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).2
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hrow := (seamOneStep_low_first r hr C hCn hCv hsides).2.2.1
  apply (isEmpty_iff_forall_notMem_cIoo R).mp hempty (seamRight n m (Fin.last m))
  · simp only [R, seamOneStepFirstFullRectangle, ofSwapColumns_left, ofSwapColumns_right,
      Grid.mem_cIoo, seamRight_val, Fin.val_last]
    rw [if_neg (by omega)]
    exact ⟨hAC.ne.symm, Or.inl (by omega)⟩
  · simp only [R, seamOneStepFirstFullRectangle, ofSwapColumns_bottom, ofSwapColumns_top,
      hVC, hVA, seamState_right_of_ne_zero u z _ hzlast, Grid.mem_cIoo, seamRight_val]
    rw [if_neg (by omega)]
    have hzpos : 0 < (z (Fin.last m)).val := Fin.pos_iff_ne_zero.mpr hzlast
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inl (by omega)⟩

end LowFirst

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

/-- The second-southwest low exchange recovers the other retained transposition. -/
theorem seamOneStepSecond_target_eq_swap :
    seamState v z = (seamState u z).swapColumns e.left C := by
  obtain ⟨hrL, hrR, _, hYfirst, hYsecond, _, _, _⟩ :=
    seamOneStep_low_second r hr C hCn hCv hsides
  obtain ⟨heL, hfL, hAeq, hCA⟩ :=
    seamOneStep_same_second_low_second_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hCP : C ≠ seamComplementFirst x.val := by intro h; have := congrArg Fin.val h; omega
  have hCQ : C ≠ seamComplementSecond x.val := by intro h; have := congrArg Fin.val h; omega
  have heP := seamMatchingEntry_right_eq_first_of_left_lt (u, z) x e he heL
  have hfP := (seamMatchingExit_right_eq_first_of_left_lt (v, z) y f hf hfL).trans hYfirst
  have hpY : (seamComplementPartner y.val).val =
      y.val.val.swapColumns (seamComplementFirst x.val) (seamComplementSecond x.val) := by
    change y.val.val.swapColumns (seamComplementFirst y.val) (seamComplementSecond y.val) = _
    rw [hYfirst, hYsecond]
  have hY : y.val.val = (x.val.val.swapColumns (seamComplementSecond x.val) C).swapColumns
      (seamComplementFirst x.val) (seamComplementSecond x.val) := by
    have hh := r.target_eq_swapColumns
    simp only [hpY, hrL, hrR] at hh
    calc
      _ = (y.val.val.swapColumns (seamComplementFirst x.val)
          (seamComplementSecond x.val)).swapColumns (seamComplementFirst x.val)
          (seamComplementSecond x.val) := (GridState.swapColumns_swapColumns _ _ _).symm
      _ = _ := congrArg (fun w => w.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val)) hh
  have hV := seamMatchingEntry_source_eq_swaps (u, z) x e
  rw [heP] at hV
  calc
    seamState v z = ((x.val.val.swapColumns (seamComplementSecond x.val) C).swapColumns
        (seamComplementFirst x.val) (seamComplementSecond x.val)).swapColumns
        e.left (seamComplementFirst x.val) := by
      rw [f.target_eq_swapColumns, hfP, ← hAeq, hY]
    _ = ((x.val.val.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val)).swapColumns
        e.left (seamComplementFirst x.val)).swapColumns e.left C := by
      rw [GridState.swapColumns_swapColumns_conj x.val.val (seamComplementSecond x.val) C
          (seamComplementFirst x.val) (seamComplementSecond x.val),
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hCP hCQ,
        GridState.swapColumns_swapColumns_conj
          (x.val.val.swapColumns (seamComplementFirst x.val) (seamComplementSecond x.val))
          (seamComplementFirst x.val) C e.left (seamComplementFirst x.val),
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hCA.ne hCP]
    _ = _ := congrArg (fun w => w.swapColumns e.left C) hV.symm

/-- The retained rectangle determined by the second-southwest low exchange. -/
def seamOneStepSecondFullRectangle : GridRectangleBetween (seamState u z) (seamState v z) :=
  ofSwapColumns _ _ e.left C
    (seamOneStep_same_second_low_second_orientations
      u v z x y e r f he hr hf C hCn hCv hsides).2.2.2.ne.symm
    (seamOneStepSecond_target_eq_swap u v z x y e r f he hr hf C hCn hCv hsides)

/-- Its concrete first-factor projection. -/
def seamOneStepSecondRectangle : GridRectangleBetween u v :=
  seamRetainedFirstRectangle (u, z) (v, z)
    (seamOneStepSecondFullRectangle u v z x y e r f he hr hf C hCn hCv hsides)
    (Or.inr (by simpa only [seamOneStepSecondFullRectangle, ofSwapColumns_right] using hCn))

/-- The source rows at the two projected endpoints and the final full-grid column. -/
theorem seamOneStepSecond_source_values :
    seamState u z C = x.val.val C ∧
      seamState u z e.left = x.val.val (seamComplementSecond x.val) ∧
      seamState u z (seamComplementSecond x.val) = x.val.val (seamComplementFirst x.val) := by
  obtain ⟨heL, _, _, hCA⟩ :=
    seamOneStep_same_second_low_second_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have heP := seamMatchingEntry_right_eq_first_of_left_lt (u, z) x e he heL
  refine ⟨?_, ?_, ?_⟩
  · have hh := e.map_of_ne C hCA.ne
      (by rw [heP]; intro h; have := congrArg Fin.val h; omega)
    rw [seamComplementPartner_firstBlock_apply x.val C hCn] at hh
    exact hh.symm
  · have hh := e.map_right
    rw [heP, seamComplementPartner_apply_first] at hh
    exact hh.symm
  · have hh := e.map_of_ne (seamComplementSecond x.val)
      (by intro h; have := congrArg Fin.val h; omega)
      (by rw [heP]; exact (seamComplementFirst_ne_second x.val).symm)
    rw [seamComplementPartner_apply_second] at hh
    exact hh.symm

/-- The three path emptiness conditions imply emptiness of this first-factor projection. -/
theorem seamOneStepSecondRectangle_isEmpty :
    (seamOneStepSecondRectangle u v z x y e r f he hr hf C hCn hCv hsides).IsEmpty := by
  obtain ⟨hrL, hrR, hrow, hYfirst, hYsecond, hyP, _, _⟩ :=
    seamOneStep_low_second r hr C hCn hCv hsides
  obtain ⟨heL, hfL, hAeq, hCA⟩ :=
    seamOneStep_same_second_low_second_orientations u v z x y e r f he hr hf C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hlast := seamOneStep_low_second_last r hr
    (seamMatchingEntry_southwest_card (u, z) x e) C hCn hCv hsides
  have hzlast := seamOneStep_same_second_low_second_zero
    u v z x y e r f he hr hf C hCn hCv hsides
  have hzpre : z.toPerm.symm 0 = Fin.last m := z.toPerm.symm_apply_eq.mpr hzlast.symm
  have heP := seamMatchingEntry_right_eq_first_of_left_lt (u, z) x e he heL
  have hfP := (seamMatchingExit_right_eq_first_of_left_lt (v, z) y f hf hfL).trans hYfirst
  obtain ⟨heBot, heTop, heHigh⟩ :
      e.bottom = x.val.val (seamComplementSecond x.val) ∧
      e.top = x.val.val e.left ∧ n < e.top.val := by
    rcases seamMatchingEntry_endpoints (u, z) x e he with h | h
    · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · have hh := congrArg Fin.val h.2.1; omega
  have hhighA : n < (x.val.val e.left).val := by rwa [heTop] at heHigh
  have hyA := seamOneStep_low_high_point r
    (by simpa only [bottom_def, hrL] using hq.2)
    (by simpa only [top_def, hrR] using hCv) e.left heL hhighA
  obtain ⟨hVC, hVA, hVQ⟩ := seamOneStepSecond_source_values
    u v z x y e r f he hr hf C hCn hCv hsides
  let R := seamOneStepSecondFullRectangle u v z x y e r f he hr hf C hCn hCv hsides
  have hside : R.left.val < n ∨ R.right.val < n := Or.inr (by
    simpa only [R, seamOneStepSecondFullRectangle, ofSwapColumns_right] using hCn)
  apply (isEmpty_iff_forall_notMem_cIoo _).mpr
  intro a ha hrowa
  have hcol : seamFirstFactorColumn z a ∈ Grid.cIoo e.left C := by
    have hh : seamFirstFactorColumn z a ∈ Grid.cIoo R.left R.right := by
      rw [← seamRetainedRectangle_left_recovery (u, z) (v, z) R hside,
        ← seamRetainedRectangle_right_recovery (u, z) (v, z) R hside,
        seamFirstFactorColumn_mem_cIoo_iff]
      exact ha
    simpa only [R, seamOneStepSecondFullRectangle, ofSwapColumns_left, ofSwapColumns_right] using hh
  have hval : seamState u z (seamFirstFactorColumn z a) ∈
      Grid.cIoo (x.val.val (seamComplementSecond x.val)) (x.val.val C) := by
    have hh : seamState u z (seamFirstFactorColumn z a) ∈ Grid.cIoo R.bottom R.top := by
      rw [seamState_firstFactorColumn,
        ← seamRetainedFirstRectangle_bottom_recovery (u, z) (v, z) R hside,
        ← seamRetainedFirstRectangle_top_recovery (u, z) (v, z) R hside,
        seamLeft_mem_cIoo_iff]
      exact hrowa
    simpa only [R, seamOneStepSecondFullRectangle, ofSwapColumns_bottom,
      ofSwapColumns_top, hVC, hVA] using hh
  induction a using Fin.lastCases with
  | last =>
    have hrightlast : seamRight n m (Fin.last m) = Fin.last (n + m) := Fin.ext rfl
    rw [seamFirstFactorColumn_last, hzpre, hrightlast, ← hlast, hVQ,
      Grid.mem_cIoo, if_neg (by omega)] at hval
    omega
  | cast d =>
    let c := seamLeft n m d.castSucc
    have hcn : c.val < n := d.isLt
    rw [seamFirstFactorColumn_castSucc] at hcol hval
    change c ∈ Grid.cIoo e.left C at hcol
    change seamState u z c ∈ _ at hval
    have hcols := (Grid.mem_cIoo _ _ _).mp hcol
    rw [if_neg (by omega)] at hcols
    have hcA : c ≠ e.left := by intro hh; have := congrArg Fin.val hh; omega
    have hcC : c ≠ C := by intro hh; have := congrArg Fin.val hh; omega
    have hcP : c ≠ seamComplementFirst x.val := by intro hh; have := congrArg Fin.val hh; omega
    have hcQ : c ≠ seamComplementSecond x.val := by intro hh; have := congrArg Fin.val hh; omega
    have hxc : seamState u z c = x.val.val c := by
      have hh := e.map_of_ne c hcA (by rw [heP]; exact hcP)
      rw [seamComplementPartner_firstBlock_apply x.val c hcn] at hh
      exact hh.symm
    have hyc : y.val.val c = x.val.val c := by
      have hh := r.map_of_ne c (by rw [hrL]; exact hcQ) (by rw [hrR]; exact hcC)
      rwa [seamComplementPartner_firstBlock_apply y.val c hcn] at hh
    have hvlow : (x.val.val c).val ≤ n := by
      rw [← hxc]
      exact seamPairSector_row_le (seamState_mem_pairSector u z) c hcn
    rcases hcols.2 with hAc | hcC'
    · rw [hxc, Grid.mem_cIoo, if_neg (by omega)] at hval
      rcases hval.2 with hvhigh | hvlow'
      · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c
        · rw [Grid.mem_cIoo, heP, if_pos (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hAc, by omega⟩
        · rw [Grid.mem_cIoo, heBot, heTop, hxc, if_pos (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hvhigh, by omega⟩
      · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c
        · rw [Grid.mem_cIoo, hfP, ← hAeq, if_pos (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hAc, by omega⟩
        · rw [Grid.mem_cIoo, bottom_def, top_def, hfP, ← hAeq, hyP, hyA, hyc,
            if_neg (by omega)]
          exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hvlow'⟩
    · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr c
      · rw [Grid.mem_cIoo, hrL, hrR, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hcC'⟩
      · simpa only [bottom_def, top_def, hrL, hrR, hxc] using hval

end LowSecond

end OnLeConjecture.KnotFloer.GridFull
