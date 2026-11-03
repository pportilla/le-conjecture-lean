/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamOneStepFactorSeparation
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondRectanglePartition

/-! # Boundary row values for one-step second-factor corrections -/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A high exchange of the first southwest point forces its row to be zero. -/
theorem seamSecondOneStep_high_first_row_zero {a b : SeamMatchingSource n m}
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (hr : r.IsEmpty) (hcard : (seamSouthwestColumns a.val.val).card = 2)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementFirst a.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = C)) :
    a.val.val (seamComplementFirst a.val) = seamLeft n m 0 := by
  obtain ⟨hrL, hrR, hQC, _, _, _, _⟩ := seamOneStep_high_first r hr hcard C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hpq := seamComplementFirst_lt_second a.val
  have hsource : (a.val.val (seamComplementFirst a.val)).val <
      (a.val.val (seamComplementSecond a.val)).val := a.property
  apply Fin.ext
  change (a.val.val (seamComplementFirst a.val)).val = 0
  by_contra hz
  let D := a.val.val.toPerm.symm (seamLeft n m 0)
  have hD : a.val.val D = seamLeft n m 0 := a.val.val.toPerm.apply_symm_apply _
  have hDP : D ≠ seamComplementFirst a.val := by
    intro hh
    have hv := congrArg Fin.val hD
    rw [hh] at hv
    change (a.val.val (seamComplementFirst a.val)).val = 0 at hv
    exact hz hv
  have hDQ : D ≠ seamComplementSecond a.val := by
    intro hh
    have hv := congrArg Fin.val hD
    rw [hh] at hv
    change (a.val.val (seamComplementSecond a.val)).val = 0 at hv
    omega
  have hDn : D.val < n := by
    by_contra hh
    have hm : D ∈ seamSouthwestColumns a.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by rw [hD]; exact Nat.zero_le n⟩
    rw [seamComplement_southwest_eq_pair_of_card_two a.val hcard] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton, hDP, hDQ, or_self] at hm
  apply (isEmpty_iff_forall_notMem_cIoo r).mp hr D
  · rw [Grid.mem_cIoo, hrL, hrR, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr (by omega)⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, hD, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr (by
      change 0 < (a.val.val (seamComplementFirst a.val)).val
      omega)⟩

/-- A high exchange of the second southwest point forces its row to be n. -/
theorem seamSecondOneStep_high_second_row_last {a b : SeamMatchingSource n m}
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (hr : r.IsEmpty) (hcard : (seamSouthwestColumns a.val.val).card = 2)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementSecond a.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = C)) :
    a.val.val (seamComplementSecond a.val) = seamLeft n m (Fin.last n) := by
  obtain ⟨hrL, hrR, hCP, _, _, _, _⟩ := seamOneStep_high_second r hr hcard C hCn hCv hsides
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hpq := seamComplementFirst_lt_second a.val
  have hsource : (a.val.val (seamComplementFirst a.val)).val <
      (a.val.val (seamComplementSecond a.val)).val := a.property
  apply Fin.ext
  change (a.val.val (seamComplementSecond a.val)).val = n
  by_contra hz
  let D := a.val.val.toPerm.symm (seamLeft n m (Fin.last n))
  have hD : a.val.val D = seamLeft n m (Fin.last n) := a.val.val.toPerm.apply_symm_apply _
  have hDP : D ≠ seamComplementFirst a.val := by
    intro hh
    have hv := congrArg Fin.val hD
    rw [hh] at hv
    change (a.val.val (seamComplementFirst a.val)).val = n at hv
    omega
  have hDQ : D ≠ seamComplementSecond a.val := by
    intro hh
    have hv := congrArg Fin.val hD
    rw [hh] at hv
    change (a.val.val (seamComplementSecond a.val)).val = n at hv
    exact hz hv
  have hDn : D.val < n := by
    by_contra hh
    have hm : D ∈ seamSouthwestColumns a.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by rw [hD]; exact le_rfl⟩
    rw [seamComplement_southwest_eq_pair_of_card_two a.val hcard] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton, hDP, hDQ, or_self] at hm
  apply (isEmpty_iff_forall_notMem_cIoo r).mp hr D
  · rw [Grid.mem_cIoo, hrL, hrR, if_neg (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr (by omega)⟩
  · rw [Grid.mem_cIoo, bottom_def, top_def, hrL, hrR, hD, if_pos (by omega)]
    exact ⟨by intro hh; have := congrArg Fin.val hh; omega, by
      change (a.val.val (seamComplementSecond a.val)).val < n
      omega, hCv⟩

/-- Every low row in the second column block of a retained state is the last
row value of its first factor. -/
theorem seamSecondOneStep_retained_low_row (x : GridState (n + 1)) (z : GridState (m + 1))
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : (seamState x z C).val ≤ n) :
    seamState x z C = seamLeft n m (x (Fin.last n)) := by
  let c := seamSecondFactorIndex C hCn
  have hC : seamRight n m c = C := seamRight_secondFactorIndex C hCn
  rw [← hC, seamState_secondFactorRow] at hCv ⊢
  have hz := seamSecondFactorRow_eq_zero_of_le x (z c) hCv
  rw [hz, seamSecondFactorRow_zero]

/-- An entry-left high-first correction requires the zero boundary value of
the first retained state. -/
theorem seamSecondOneStep_high_first_boundary (p : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (he : e.IsEmpty) (hr : r.IsEmpty) (heL : e.left.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementFirst a.val ∧ r.right = C) ∨
      (r.right = seamComplementFirst a.val ∧ r.left = C)) : p.1 (Fin.last n) = 0 := by
  have hcard := seamMatchingEntry_southwest_card p a e
  have hzero := seamSecondOneStep_high_first_row_zero r hr hcard C hCn hCv hsides
  have heR := seamMatchingEntry_right_eq_first_of_left_lt p a e he heL
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hv : seamState p.1 p.2 (seamComplementSecond a.val) =
      a.val.val (seamComplementFirst a.val) := by
    have hh := e.map_of_ne (seamComplementSecond a.val)
      (by intro hh; have := congrArg Fin.val hh; omega)
      (by rw [heR]; exact (seamComplementFirst_lt_second a.val).ne.symm)
    rw [seamComplementPartner_apply_second] at hh
    exact hh.symm
  have hl := seamSecondOneStep_retained_low_row p.1 p.2 (seamComplementSecond a.val) hq.1
    (by rw [hv]; exact hp.2)
  rw [hv, hzero] at hl
  exact (seamLeft_injective hl).symm

/-- An entry-right high-second correction requires the last boundary value of
the first retained state. -/
theorem seamSecondOneStep_high_second_boundary (p : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (he : e.IsEmpty) (hr : r.IsEmpty) (heR : e.right.val < n)
    (C : Fin (n + m + 1)) (hCn : n ≤ C.val) (hCv : n < (a.val.val C).val)
    (hsides : (r.left = seamComplementSecond a.val ∧ r.right = C) ∨
      (r.right = seamComplementSecond a.val ∧ r.left = C)) :
    p.1 (Fin.last n) = Fin.last n := by
  have hcard := seamMatchingEntry_southwest_card p a e
  have hlast := seamSecondOneStep_high_second_row_last r hr hcard C hCn hCv hsides
  have heL := seamMatchingEntry_left_eq_second_of_right_lt p a e he heR
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hv : seamState p.1 p.2 (seamComplementFirst a.val) =
      a.val.val (seamComplementSecond a.val) := by
    have hh := e.map_of_ne (seamComplementFirst a.val)
      (by rw [heL]; exact (seamComplementFirst_lt_second a.val).ne)
      (by intro hh; have := congrArg Fin.val hh; omega)
    rw [seamComplementPartner_apply_first] at hh
    exact hh.symm
  have hl := seamSecondOneStep_retained_low_row p.1 p.2 (seamComplementFirst a.val) hp.1
    (by rw [hv]; exact hq.2)
  rw [hv, hlast] at hl
  exact (seamLeft_injective hl).symm

/-- The proved one-step orientation data determine the retained transposition
with its explicit two columns. -/
theorem seamSecondOneStep_target_eq_swap (p q : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState q.1 q.2))
    (i : FlatKind) (C A : Fin (n + m + 1))
    (hAn : A.val < n) (hAv : n < (a.val.val A).val)
    (hi : flatRange i n a.val.val (seamComplementFirst a.val) (seamComplementSecond a.val) C)
    (hrL : r.left = flatLeft i (seamComplementFirst a.val) (seamComplementSecond a.val) C)
    (hrR : r.right = flatRight i (seamComplementFirst a.val) (seamComplementSecond a.val) C)
    (hbP : seamComplementFirst b.val = flatFirst i
      (seamComplementFirst a.val) (seamComplementSecond a.val) C)
    (hbQ : seamComplementSecond b.val = flatSecond i
      (seamComplementFirst a.val) (seamComplementSecond a.val) C)
    (heL : e.left = if seamOneStepEntryLeft i then A else seamComplementSecond a.val)
    (heR : e.right = if seamOneStepEntryLeft i then seamComplementFirst a.val else A)
    (hfL : f.left = if seamOneStepExitLeft i then A else seamComplementSecond b.val)
    (hfR : f.right = if seamOneStepExitLeft i then seamComplementFirst b.val else A) :
    seamState q.1 q.2 = (seamState p.1 p.2).swapColumns
      (seamOneStepNetLeft i (seamComplementFirst a.val) (seamComplementSecond a.val) C)
      (seamOneStepNetRight i C A) := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hpq := seamComplementFirst_lt_second a.val
  have hAP : A ≠ seamComplementFirst a.val := by intro h; have := congrArg Fin.val h; omega
  have hAQ : A ≠ seamComplementSecond a.val := by intro h; have := congrArg Fin.val h; omega
  have hPC : seamComplementFirst a.val ≠ C := by
    intro h; subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hQC : seamComplementSecond a.val ≠ C := by
    intro h; subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hAC : A ≠ C := by
    intro h; subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hsource := seamMatchingEntry_source_eq_swaps p a e
  rw [heL, heR] at hsource
  have htarget := f.target_eq_swapColumns
  rw [hfL, hfR, hbP, hbQ] at htarget
  have hswap := seamOneStep_target_swap a.val.val b.val.val i
    (seamComplementFirst a.val) (seamComplementSecond a.val) C A
    hpq.ne hPC hQC hAP hAQ hAC (flatStep_apply r i C hi hrL hrR hbP hbQ)
  exact htarget.trans (hswap.trans (congrArg (fun v => v.swapColumns
    (seamOneStepNetLeft i (seamComplementFirst a.val) (seamComplementSecond a.val) C)
    (seamOneStepNetRight i C A)) hsource.symm))

/-- If the second retained factor changes, the actual neutral type is high. -/
theorem seamSecondOneStep_kind_high (p q : SeamRetainedIndex n m)
    (a : SeamMatchingSource n m) (i : FlatKind) (C A : Fin (n + m + 1))
    (hi : flatRange i n a.val.val (seamComplementFirst a.val) (seamComplementSecond a.val) C)
    (hfinal : seamState q.1 q.2 = (seamState p.1 p.2).swapColumns
      (seamOneStepNetLeft i (seamComplementFirst a.val) (seamComplementSecond a.val) C)
      (seamOneStepNetRight i C A)) (hne : p.2 ≠ q.2) :
    i = .highFirst ∨ i = .highSecond := by
  have hlow (hC : C.val < n)
      (hh : seamState q.1 q.2 = (seamState p.1 p.2).swapColumns C A) : False := by
    have hCA : C ≠ A := by
      intro h
      have hself : (seamState p.1 p.2).swapColumns A A = seamState p.1 p.2 := by
        apply GridState.ext
        intro c
        simp [GridState.swapColumns_apply]
      rw [h, hself] at hh
      have hpq := seamState_injective hh
      exact hne (congrArg Prod.snd hpq).symm
    let R := ofSwapColumns (seamState p.1 p.2) (seamState q.1 q.2) C A hCA hh
    exact hne (seamRetainedRectangle_second_eq_of_side_lt p q R
      (Or.inl (by simpa only [R, ofSwapColumns_left] using hC)))
  cases i with
  | lowFirst => exact False.elim (hlow hi.1 hfinal)
  | lowSecond => exact False.elim (hlow hi.1 hfinal)
  | highFirst => exact Or.inl rfl
  | highSecond => exact Or.inr rfl

/-- A one-transition correction changing the second factor requires a boundary
last-row value of the first state. -/
theorem seamSecondOneStep_boundary (p q : SeamRetainedIndex n m)
    (a b : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (f : GridRectangleBetween b.val.val (seamState q.1 q.2))
    (hab : a ≠ b) (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) (hne : p.2 ≠ q.2) :
    p.1 (Fin.last n) = 0 ∨ p.1 (Fin.last n) = Fin.last n := by
  obtain ⟨i, C, A, hAn, hAv, hi, hrL, hrR, hbP, hbQ, heL, heR, hfL, hfR⟩ :=
    seamOneStep_all_orientations p q a b e r f hab he hr hf
  have hfinal := seamSecondOneStep_target_eq_swap p q a b e r f i C A hAn hAv hi
    hrL hrR hbP hbQ heL heR hfL hfR
  rcases seamSecondOneStep_kind_high p q a i C A hi hfinal hne with rfl | rfl
  · left
    simp only [flatRange, flatLeft, flatRight, seamOneStepEntryLeft, if_true] at hi hrL hrR heL
    exact seamSecondOneStep_high_first_boundary p a b e r he hr (by rwa [heL])
      C hi.1 hi.2.1 (Or.inr ⟨hrR, hrL⟩)
  · right
    simp only [flatRange, flatLeft, flatRight, seamOneStepEntryLeft,
      Bool.false_eq_true, if_false] at hi hrL hrR heR
    exact seamSecondOneStep_high_second_boundary p a b e r he hr (by rwa [heR])
      C hi.1 hi.2.1 (Or.inl ⟨hrL, hrR⟩)

/-- Native one-transition corrections changing the second factor cannot occur
at an interior last-row value of the first state. -/
theorem seamCorrectionOne_second_boundary {p q : SeamRetainedIndex n m}
    (path : SeamCorrectionPath 1 p q) (hne : p.2 ≠ q.2) :
    p.1 (Fin.last n) = 0 ∨ p.1 (Fin.last n) = Fin.last n := by
  rcases path with ⟨a, b, e, ⟨b', r, tail⟩, f⟩
  have hh : b' = b := tail.property
  subst b'
  exact seamSecondOneStep_boundary p q a b e.val r.val f.val
    r.property.1 e.property r.property.2 f.property hne

/-- At an interior last-row value, the native one-transition type changing
the second factor is empty. -/
theorem seamCorrectionOne_second_interior_isEmpty (p q : SeamRetainedIndex n m)
    (hne : p.2 ≠ q.2) (hzero : p.1 (Fin.last n) ≠ 0)
    (hlast : p.1 (Fin.last n) ≠ Fin.last n) : IsEmpty (SeamCorrectionPath 1 p q) :=
  ⟨fun path => (seamCorrectionOne_second_boundary path hne).elim hzero hlast⟩

end OnLeConjecture.KnotFloer.GridFull
