/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTwoStepOuterBoundary

/-!
# First-factor rectangles recovered from two internal transitions

The hypotheses describe an empty entry, an empty birth, an empty death,
and an empty exit, with two northeast points at the intermediate state
and the same retained second factor. No bound on arbitrary path lengths
is assumed or concluded.
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
/-- The low and high row endpoints of the four rectangles agree in the required pairs. -/
theorem seamTwoStep_complete_rows :
    e.top = x.val.val (seamComplementFirst x.val) ∧
    e.bottom = x.val.val e.right ∧
    t.top = e.top ∧ t.bottom = r.top ∧
    f.bottom = r.bottom ∧ f.top = e.bottom ∧
    e.top.val < (x.val.val (seamComplementSecond x.val)).val ∧
    (x.val.val (seamComplementSecond x.val)).val < r.bottom.val ∧
    r.bottom.val ≤ n ∧ n < e.bottom.val ∧ n < r.top.val := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hsame := seamTwoStep_complete_inner_left_eq p q x y z e r t f he hr ht hf hmid hpq
  have houter := seamTwoStep_complete_outer_right_eq p q x y z e r t f he hr ht hf hmid hpq
  have hx := seamMatchingEntry_southwest_card p x e
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hi := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  have hc := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hbcols := seamMatchingBirth_nonwrap x y r hr hb hi.1
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e he ho.1
  have hF := seamMatchingExit_left_eq_second_of_right_lt q z f hf ho.2
  rw [hc.2.2.2.2.1] at hF
  have hrows := seamTwoStep_birth_death_final_rows x y z r t hr ht hb hd hx
  have hEt : e.top = x.val.val (seamComplementFirst x.val) := by
    have hh := e.map_left
    rw [hE, seamComplementPartner_apply_second] at hh
    exact hh.symm
  have hEb : e.bottom = x.val.val e.right := by
    have hh := e.map_right
    rw [seamComplementPartner_firstBlock_apply x.val e.right ho.1] at hh
    exact hh.symm
  have hTt : t.top = e.top := by
    rw [top_def, ← hc.1, ← hc.2.1, hbcols.2.2.2.2.2, hEt]
  have hTb := seamTwoStep_inner_high_eq x y z r t hr ht hb hd hx hsame
  have hFb : f.bottom = r.bottom := by
    rw [bottom_def, hF, ← hc.2.2.2.2.1, hrows.2]
  have hlow : r.bottom.val ≤ n := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.1
    · omega
  have hrhigh : n < r.top.val := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.2
    · omega
  have hehigh : n < e.bottom.val := by
    rcases seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
        (seamComplementPartner x.val).property e with h | h
    · have hh := h.2.1; omega
    · exact h.2.2.2
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hA : e.right ≠ r.left := by
    intro hh
    rw [hEb, hh] at hehigh
    change (x.val.val r.left).val ≤ n at hlow
    omega
  have hC : e.right ≠ r.right := by
    intro hh
    have := congrArg Fin.val hh
    have hh := hbcols.1
    omega
  have hPne : e.right ≠ seamComplementFirst x.val := by
    intro hh; have := congrArg Fin.val hh; omega
  have hQne : e.right ≠ seamComplementSecond x.val := by
    intro hh; have := congrArg Fin.val hh; omega
  have hFt : f.top = e.bottom := by
    rw [top_def, ← houter,
      seamTwoStep_values_away x y z r t hr ht hb hd hx hsame e.right hA hC hPne hQne,
      ← hEb]
  have horder := z.property
  change (z.val.val (seamComplementFirst z.val)).val <
    (z.val.val (seamComplementSecond z.val)).val at horder
  rw [hrows.1, hrows.2] at horder
  have hxorder := x.property
  change (x.val.val (seamComplementFirst x.val)).val <
    (x.val.val (seamComplementSecond x.val)).val at hxorder
  exact ⟨hEt, hEb, hTt, hTb, hFb, hFt, by simpa only [hEt] using hxorder,
    horder, hlow, hehigh, hrhigh⟩

include he hr ht hf hmid hpq in
/-- The first-block side of the outer rectangles precedes that of the internal rectangles. -/
theorem seamTwoStep_complete_first_columns_lt : e.right.val < r.left.val := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hs := seamTwoStep_complete_inner_left_eq p q x y z e r t f he hr ht hf hmid hpq
  have hcut := seamTwoStep_complete_inner_cut p q x y z e r t f he hr ht hf hmid hpq
  have hrow := seamTwoStep_complete_rows p q x y z e r t f he hr ht hf hmid hpq
  obtain ⟨hEt, hEb, hTt, hTb, hFb, hFt, hlow1, hlow2, hlow, hehigh, hrhigh⟩ := hrow
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hi := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd
    (seamMatchingEntry_southwest_card p x e)
  have hA : e.right ≠ r.left := by
    intro hh
    rw [hEb, hh] at hehigh
    change (x.val.val r.left).val ≤ n at hlow
    omega
  have hC : e.right ≠ r.right := by intro hh; have := congrArg Fin.val hh; omega
  have hY : y.val.val e.right = x.val.val e.right := by
    have hh := r.map_of_ne e.right hA hC
    rw [seamComplementPartner_firstBlock_apply y.val e.right ho.1] at hh
    exact hh
  have hrowsne : e.bottom ≠ r.top := by
    rw [hEb, top_def]
    exact fun hh => hC (x.val.val.toPerm.injective hh)
  by_contra hlt
  have hAB : r.left.val < e.right.val := by
    have hh : e.right.val ≠ r.left.val := fun hh => hA (Fin.ext hh)
    omega
  have hcolr : e.right ∈ Grid.cIoo r.left r.right := by
    rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨r.left_ne_right, hAB, by omega⟩
  have hcolt : e.right ∈ Grid.cIoo t.left t.right := by
    rw [Grid.mem_cIoo, if_pos (by rw [← hs]; omega)]
    exact ⟨t.left_ne_right, by rw [← hs]; exact hAB, by omega⟩
  by_cases hh : e.bottom.val < r.top.val
  · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr e.right hcolr
    rw [← hEb, Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨r.bottom_ne_top, by omega, hh⟩
  · have hgt : r.top.val < e.bottom.val := by
      have hv : e.bottom.val ≠ r.top.val := fun hh => hrowsne (Fin.ext hh)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo t).mp ht e.right hcolt
    rw [hY, ← hEb, hTt, hTb, Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨by simpa only [hTt, hTb] using t.bottom_ne_top, Or.inl hgt⟩

include he hr ht hf hmid hpq in
/-- The retained endpoints differ by the transposition on the two first-block sides. -/
theorem seamTwoStepFirst_target_eq_swap :
    seamState q.1 q.2 = (seamState p.1 p.2).swapColumns r.left e.right := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hs := seamTwoStep_complete_inner_left_eq p q x y z e r t f he hr ht hf hmid hpq
  have houter := seamTwoStep_complete_outer_right_eq p q x y z e r t f he hr ht hf hmid hpq
  have hAB := seamTwoStep_complete_first_columns_lt p q x y z e r t f he hr ht hf hmid hpq
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hx := seamMatchingEntry_southwest_card p x e
  have hi := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  have hc := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hbirth := seamMatchingBirth_nonwrap x y r hr hb hi.1
  have hP := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hQ := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hAP : r.left ≠ seamComplementFirst x.val := by
    intro hh; have := congrArg Fin.val hh; omega
  have hAQ : r.left ≠ seamComplementSecond x.val := by
    intro hh; have := congrArg Fin.val hh; omega
  have hABne : r.left ≠ e.right := by intro hh; have := congrArg Fin.val hh; omega
  have hCP : r.right ≠ seamComplementFirst x.val := hbirth.2.1.ne
  have hY : y.val.val = (x.val.val.swapColumns r.left r.right).swapColumns
      r.right (seamComplementFirst x.val) := by
    have hh := r.target_eq_swapColumns
    change y.val.val.swapColumns (seamComplementFirst y.val)
      (seamComplementSecond y.val) = _ at hh
    rw [hc.2.1, hc.2.2.1] at hh
    calc
      _ = (y.val.val.swapColumns r.right (seamComplementFirst x.val)).swapColumns
        r.right (seamComplementFirst x.val) := (GridState.swapColumns_swapColumns _ _ _).symm
      _ = _ := congrArg (fun w => w.swapColumns r.right (seamComplementFirst x.val)) hh
  have hZ : z.val.val = (x.val.val.swapColumns r.left (seamComplementFirst x.val)).swapColumns
      (seamComplementFirst x.val) (seamComplementSecond x.val) := by
    have hh := t.target_eq_swapColumns
    change z.val.val.swapColumns (seamComplementFirst z.val)
      (seamComplementSecond z.val) = _ at hh
    rw [hc.2.2.2.1, hc.2.2.2.2.1, ← hs, ← hc.1, hY] at hh
    rw [GridState.swapColumns_swapColumns_conj (x.val.val.swapColumns r.left r.right)
        r.right (seamComplementFirst x.val) r.left r.right,
      GridState.swapColumns_swapColumns, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hAP.symm hCP.symm] at hh
    calc
      _ = (z.val.val.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val)).swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val) := (GridState.swapColumns_swapColumns _ _ _).symm
      _ = _ := congrArg (fun w => w.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val)) hh
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e he ho.1
  have hF := (seamMatchingExit_left_eq_second_of_right_lt q z f hf ho.2).trans hc.2.2.2.2.1
  have hV := seamMatchingEntry_source_eq_swaps p x e
  rw [hE] at hV
  calc
    _ = ((x.val.val.swapColumns r.left (seamComplementFirst x.val)).swapColumns
        (seamComplementFirst x.val) (seamComplementSecond x.val)).swapColumns
        (seamComplementSecond x.val) e.right := by
      rw [f.target_eq_swapColumns, hF, ← houter, hZ]
    _ = ((x.val.val.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val)).swapColumns
        (seamComplementSecond x.val) e.right).swapColumns r.left e.right := by
      rw [GridState.swapColumns_swapColumns_conj x.val.val r.left (seamComplementFirst x.val)
          (seamComplementFirst x.val) (seamComplementSecond x.val),
        Equiv.swap_apply_of_ne_of_ne hAP hAQ, Equiv.swap_apply_left,
        GridState.swapColumns_swapColumns_conj
          (x.val.val.swapColumns (seamComplementFirst x.val) (seamComplementSecond x.val))
          r.left (seamComplementSecond x.val) (seamComplementSecond x.val) e.right,
        Equiv.swap_apply_of_ne_of_ne hAQ hABne, Equiv.swap_apply_left]
    _ = _ := congrArg (fun w => w.swapColumns r.left e.right) hV.symm

/-- The retained rectangle determined by the complete two-transition path. -/
def seamTwoStepFirstFullRectangle :
    GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2) :=
  ofSwapColumns _ _ r.left e.right
    (by have hh := seamTwoStep_complete_first_columns_lt p q x y z e r t f he hr ht hf hmid hpq
        intro h; have := congrArg Fin.val h; omega)
    (seamTwoStepFirst_target_eq_swap p q x y z e r t f he hr ht hf hmid hpq)

/-- Its first-factor projection. Both endpoints are strictly before the last first-factor column. -/
def seamTwoStepFirstRectangle : GridRectangleBetween p.1 q.1 :=
  seamRetainedFirstRectangle p q
    (seamTwoStepFirstFullRectangle p q x y z e r t f he hr ht hf hmid hpq)
    (Or.inr (by
      simpa only [seamTwoStepFirstFullRectangle, ofSwapColumns_right] using
        (seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq).1))

include he hr ht hf hmid hpq in
/-- The retained source values at the recovered factor sides, zero-preimage column and seam. -/
theorem seamTwoStepFirst_source_values :
    seamState p.1 p.2 r.left = r.bottom ∧
    seamState p.1 p.2 e.right = e.top ∧
    seamState p.1 p.2 (seamComplementFirst x.val) =
      x.val.val (seamComplementSecond x.val) ∧
    seamState p.1 p.2 r.right = r.top := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hAB := seamTwoStep_complete_first_columns_lt p q x y z e r t f he hr ht hf hmid hpq
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hi := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd
    (seamMatchingEntry_southwest_card p x e)
  have hbirth := seamMatchingBirth_nonwrap x y r hr hb hi.1
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hpq' := seamComplementFirst_lt_second x.val
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e he ho.1
  refine ⟨?_, rfl, ?_, ?_⟩
  · have hh := e.map_of_ne r.left
      (by rw [hE]; intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)
    rw [seamComplementPartner_firstBlock_apply x.val r.left hi.1] at hh
    exact hh.symm
  · have hh := e.map_of_ne (seamComplementFirst x.val)
      (by rw [hE]; exact seamComplementFirst_ne_second x.val)
      (by intro h; have := congrArg Fin.val h; omega)
    rw [seamComplementPartner_apply_first] at hh
    exact hh.symm
  · have hh := e.map_of_ne r.right
      (by rw [hE]; exact (hbirth.2.1.trans hpq').ne)
      (by intro h; have := congrArg Fin.val h; have hn := hbirth.1; omega)
    change x.val.val.swapColumns (seamComplementFirst x.val)
      (seamComplementSecond x.val) r.right = _ at hh
    rw [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hbirth.2.1.ne (hbirth.2.1.trans hpq').ne] at hh
    exact hh.symm

include he hr ht hf hmid hpq in
/-- All four emptiness conditions imply emptiness of the recovered first-factor rectangle. -/
theorem seamTwoStepFirstRectangle_isEmpty :
    (seamTwoStepFirstRectangle p q x y z e r t f he hr ht hf hmid hpq).IsEmpty := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hs := seamTwoStep_complete_inner_left_eq p q x y z e r t f he hr ht hf hmid hpq
  have houter := seamTwoStep_complete_outer_right_eq p q x y z e r t f he hr ht hf hmid hpq
  have hcut := seamTwoStep_complete_inner_cut p q x y z e r t f he hr ht hf hmid hpq
  have hAB := seamTwoStep_complete_first_columns_lt p q x y z e r t f he hr ht hf hmid hpq
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hx := seamMatchingEntry_southwest_card p x e
  have hi := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  have hc := seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e he ho.1
  have hF := (seamMatchingExit_left_eq_second_of_right_lt q z f hf ho.2).trans hc.2.2.2.2.1
  have hP := seamTwoStep_entry_southwest_of_right p x e he ho.1
  obtain ⟨hEt, hEb, hTt, hTb, hFb, hFt, hlow1, hlow2, hlow, hehigh, hrhigh⟩ :=
    seamTwoStep_complete_rows p q x y z e r t f he hr ht hf hmid hpq
  obtain ⟨hVA, hVB, hVP, hVC⟩ :=
    seamTwoStepFirst_source_values p q x y z e r t f he hr ht hf hmid hpq
  let R := seamTwoStepFirstFullRectangle p q x y z e r t f he hr ht hf hmid hpq
  have hside : R.left.val < n ∨ R.right.val < n := Or.inl (by
    simpa only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_left] using hi.1)
  apply (isEmpty_iff_forall_notMem_cIoo _).mpr
  intro a ha hrowa
  have hcol : seamFirstFactorColumn p.2 a ∈ Grid.cIoo r.left e.right := by
    have hh : seamFirstFactorColumn p.2 a ∈ Grid.cIoo R.left R.right := by
      rw [← seamRetainedRectangle_left_recovery p q R hside,
        ← seamRetainedRectangle_right_recovery p q R hside,
        seamFirstFactorColumn_mem_cIoo_iff]
      exact ha
    simpa only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_left, ofSwapColumns_right] using hh
  have hval : seamState p.1 p.2 (seamFirstFactorColumn p.2 a) ∈
      Grid.cIoo r.bottom e.top := by
    have hh : seamState p.1 p.2 (seamFirstFactorColumn p.2 a) ∈ Grid.cIoo R.bottom R.top := by
      rw [seamState_firstFactorColumn,
        ← seamRetainedFirstRectangle_bottom_recovery p q R hside,
        ← seamRetainedFirstRectangle_top_recovery p q R hside,
        seamLeft_mem_cIoo_iff]
      exact hrowa
    simpa only [R, seamTwoStepFirstFullRectangle, ofSwapColumns_bottom,
      ofSwapColumns_top, hVA, hVB] using hh
  induction a using Fin.lastCases with
  | last =>
    rw [seamFirstFactorColumn_last, ← hP, hVP, Grid.mem_cIoo, if_neg (by omega)] at hval
    omega
  | cast d =>
    let c := seamLeft n m d.castSucc
    have hcn : c.val < n := d.isLt
    rw [seamFirstFactorColumn_castSucc] at hcol hval
    change c ∈ Grid.cIoo r.left e.right at hcol
    change seamState p.1 p.2 c ∈ _ at hval
    have hcols := (Grid.mem_cIoo _ _ _).mp hcol
    rw [if_neg (by omega)] at hcols
    have hcA : c ≠ r.left := by intro hh; have := congrArg Fin.val hh; omega
    have hcB : c ≠ e.right := by intro hh; have := congrArg Fin.val hh; omega
    have hcC : c ≠ r.right := by intro hh; have := congrArg Fin.val hh; omega
    have hcP : c ≠ seamComplementFirst x.val := by intro hh; have := congrArg Fin.val hh; omega
    have hcQ : c ≠ seamComplementSecond x.val := by intro hh; have := congrArg Fin.val hh; omega
    have hxc : seamState p.1 p.2 c = x.val.val c := by
      have hh := e.map_of_ne c (by rw [hE]; exact hcQ) hcB
      rw [seamComplementPartner_firstBlock_apply x.val c hcn] at hh
      exact hh.symm
    have hyc : y.val.val c = x.val.val c := by
      have hh := r.map_of_ne c hcA hcC
      rwa [seamComplementPartner_firstBlock_apply y.val c hcn] at hh
    have hzc := seamTwoStep_values_away x y z r t hr ht hb hd hx hs c hcA hcC hcP hcQ
    have hvlow : (x.val.val c).val ≤ n := by
      rw [← hxc]
      exact seamPairSector_row_le (seamState_mem_pairSector p.1 p.2) c hcn
    rw [hxc, Grid.mem_cIoo, if_neg (by omega)] at hval
    rcases hcols.2 with hAc | hcB'
    · have hcr : c ∈ Grid.cIoo r.left r.right := by
        rw [Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨r.left_ne_right, hAc, by omega⟩
      have hct : c ∈ Grid.cIoo t.left t.right := by
        rw [Grid.mem_cIoo, if_pos (by rw [← hs]; omega)]
        exact ⟨t.left_ne_right, by rw [← hs]; exact hAc, by omega⟩
      rcases hval.2 with hhigh | hlow'
      · apply (isEmpty_iff_forall_notMem_cIoo r).mp hr c hcr
        rw [Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨r.bottom_ne_top, hhigh, by omega⟩
      · apply (isEmpty_iff_forall_notMem_cIoo t).mp ht c hct
        rw [hyc, hTt, hTb, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨by simpa only [hTt, hTb] using t.bottom_ne_top, Or.inr hlow'⟩
    · have hce : c ∈ Grid.cIoo e.left e.right := by
        rw [Grid.mem_cIoo, hE, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hcB'⟩
      have hcf : c ∈ Grid.cIoo f.left f.right := by
        rw [Grid.mem_cIoo, hF, ← houter, if_neg (by omega)]
        exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hcB'⟩
      rcases hval.2 with hhigh | hlow'
      · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c hcf
        rw [hzc, hFb, hFt, Grid.mem_cIoo, if_pos (by omega)]
        exact ⟨by simpa only [hFb, hFt] using f.bottom_ne_top, hhigh, by omega⟩
      · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c hce
        rw [hxc, Grid.mem_cIoo, if_neg (by omega)]
        exact ⟨e.bottom_ne_top, Or.inr hlow'⟩

end Complete
end OnLeConjecture.KnotFloer.GridFull
