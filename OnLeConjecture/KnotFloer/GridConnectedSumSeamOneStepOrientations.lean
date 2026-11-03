/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFlatTwoStepBarrier
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamRetainedRectangles

/-!
# Entry and exit orientations of an arbitrary one-transition correction

The retained factors are not assumed equal. Testing the exchanged point
and the unique northeast point against the three actual empty rectangles
determines both outer cut orientations from the neutral transition type.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m k : ℕ}

private theorem oneInside_inc {a b c : Fin k} (hac : a.val < c.val) (hcb : c.val < b.val) :
    flatInside a b c := by
  rw [flatInside, if_pos (by omega)]
  exact ⟨hac, hcb⟩

private theorem oneInside_high {a b c : Fin k} (hba : b.val < a.val) (hac : a.val < c.val) :
    flatInside a b c := by
  rw [flatInside, if_neg (by omega)]
  exact Or.inl hac

private theorem oneInside_low {a b c : Fin k} (hba : b.val < a.val) (hcb : c.val < b.val) :
    flatInside a b c := by
  rw [flatInside, if_neg (by omega)]
  exact Or.inr hcb

private theorem oneStep_numeric_orientations
    (n : ℕ) (x : Fin k → Fin k) (hx : Function.Injective x)
    (A P Q C : Fin k) (i : FlatKind) (eLeft fLeft : Bool)
    (hA : A.val < n) (hP : n ≤ P.val) (hPQ : P < Q)
    (hrows : (x P).val < (x Q).val) (hQrow : (x Q).val ≤ n)
    (hAH : n < (x A).val) (hi : flatRange i n x P Q C)
    (he : flatEmpty x (if eLeft then A else Q) (if eLeft then P else A)
      (if eLeft then x Q else x A) (if eLeft then x A else x P))
    (hr : flatEmpty x (flatLeft i P Q C) (flatRight i P Q C)
      (x (flatLeft i P Q C)) (x (flatRight i P Q C)))
    (hf : flatEmpty (flatApply i x P Q C)
      (if fLeft then A else flatSecond i P Q C)
      (if fLeft then flatFirst i P Q C else A)
      (if fLeft then x A else flatApply i x P Q C (flatSecond i P Q C))
      (if fLeft then flatApply i x P Q C (flatFirst i P Q C) else x A)) :
    match i with
    | .lowFirst => eLeft = false ∧ fLeft = false
    | .lowSecond => eLeft = true ∧ fLeft = true
    | .highFirst => eLeft = true ∧ fLeft = false
    | .highSecond => eLeft = false ∧ fLeft = true := by
  have hAP : A ≠ P := by intro hh; have := congrArg Fin.val hh; omega
  have hAQ : A ≠ Q := by intro hh; have := congrArg Fin.val hh; omega
  have hPC : P ≠ C := by
    intro hh
    subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hQC : Q ≠ C := by
    intro hh
    subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hAC : A ≠ C := by
    intro hh
    subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hvAC : (x A).val ≠ (x C).val := by
    intro hh
    exact hAC (hx (Fin.ext hh))
  have hACval : A.val ≠ C.val := fun hh => hAC (Fin.ext hh)
  cases i with
  | lowFirst =>
    obtain ⟨hCn, hCv, hQCrow⟩ := hi
    have hAC' : A.val < C.val := by
      by_contra hh
      apply hr A
      change flatInside C P A ∧ flatInside (x C) (x P) (x A)
      exact ⟨oneInside_inc (by omega) (by omega), oneInside_high (by omega) (by omega)⟩
    constructor
    · cases eLeft with
      | false => rfl
      | true =>
        apply False.elim
        apply he C
        change flatInside A P C ∧ flatInside (x Q) (x A) (x C)
        exact ⟨oneInside_inc hAC' (by omega), oneInside_inc hQCrow (by omega)⟩
    · cases fLeft with
      | false => rfl
      | true =>
        apply False.elim
        apply hf C
        simp only [flatFirst, flatApply, hPC.symm, hQC.symm, ↓reduceIte]
        exact ⟨oneInside_inc hAC' (by omega), oneInside_low (by omega) hrows⟩
  | lowSecond =>
    obtain ⟨hCn, hCv, hCProw⟩ := hi
    have hCA' : C.val < A.val := by
      by_contra hh
      apply hr A
      change flatInside Q C A ∧ flatInside (x Q) (x C) (x A)
      exact ⟨oneInside_low (by omega) (by omega), oneInside_high (by omega) (by omega)⟩
    constructor
    · cases eLeft with
      | true => rfl
      | false =>
        apply False.elim
        apply he C
        change flatInside Q A C ∧ flatInside (x A) (x P) (x C)
        exact ⟨oneInside_low (by omega) hCA', oneInside_low (by omega) hCProw⟩
    · cases fLeft with
      | true => rfl
      | false =>
        apply False.elim
        apply hf C
        simp only [flatSecond, flatApply, hPC.symm, hQC.symm,
          hPQ.ne.symm, ↓reduceIte, Bool.false_eq_true]
        exact ⟨oneInside_low (by omega) hCA', oneInside_inc hrows (by omega)⟩
  | highFirst =>
    obtain ⟨hCn, hCv, hQC'⟩ := hi
    have hrow : (x A).val < (x C).val := by
      by_contra hh
      apply hr A
      change flatInside C P A ∧ flatInside (x C) (x P) (x A)
      exact ⟨oneInside_low (by omega) (by omega), oneInside_high (by omega) (by omega)⟩
    constructor
    · cases eLeft with
      | true => rfl
      | false =>
        apply False.elim
        apply he C
        change flatInside Q A C ∧ flatInside (x A) (x P) (x C)
        exact ⟨oneInside_high (by omega) hQC', oneInside_high (by omega) hrow⟩
    · cases fLeft with
      | false => rfl
      | true =>
        apply False.elim
        apply hf P
        simp only [flatFirst, flatApply, hPQ.ne.symm, ↓reduceIte]
        exact ⟨oneInside_inc (by omega) hPQ, oneInside_high (by omega) hrow⟩
  | highSecond =>
    obtain ⟨hCn, hCv, hCP'⟩ := hi
    have hrow : (x C).val < (x A).val := by
      by_contra hh
      apply hr A
      change flatInside Q C A ∧ flatInside (x Q) (x C) (x A)
      exact ⟨oneInside_low (by omega) (by omega), oneInside_inc (by omega) (by omega)⟩
    constructor
    · cases eLeft with
      | false => rfl
      | true =>
        apply False.elim
        apply he C
        change flatInside A P C ∧ flatInside (x Q) (x A) (x C)
        exact ⟨oneInside_inc (by omega) hCP', oneInside_inc (by omega) hrow⟩
    · cases fLeft with
      | true => rfl
      | false =>
        apply False.elim
        apply hf Q
        simp only [flatSecond, flatApply, hPQ.ne.symm,
          ↓reduceIte, Bool.false_eq_true]
        exact ⟨oneInside_high (by omega) hPQ, oneInside_inc (by omega) hrow⟩

private theorem oneStep_empty_target {x y : GridState k} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) : flatEmpty y r.left r.right r.bottom r.top := by
  intro c h
  apply (isEmpty_iff_forall_notMem_cIoo_target r).mp he c
  · exact (Grid.mem_cIoo _ _ _).mpr ⟨r.left_ne_right, h.1⟩
  · have hh := (Grid.mem_cIoo _ _ _).mpr ⟨r.bottom_ne_top, h.2⟩
    simpa only [r.map_right, r.map_left, bottom_def, top_def] using hh

private theorem oneStep_entry_data (p : SeamRetainedIndex n m) (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : e.IsEmpty) :
    ∃ A : Fin (n + m + 1), ∃ left : Bool, A.val < n ∧ n < (x.val.val A).val ∧
      e.left = (if left then A else seamComplementSecond x.val) ∧
      e.right = (if left then seamComplementFirst x.val else A) ∧
      flatEmpty x.val.val (if left then A else seamComplementSecond x.val)
        (if left then seamComplementFirst x.val else A)
        (if left then x.val.val (seamComplementSecond x.val) else x.val.val A)
        (if left then x.val.val A else x.val.val (seamComplementFirst x.val)) := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  rcases seamMatchingEntry_endpoints p x e he with h | h
  · obtain ⟨hA, hP, hbot, htop, hhigh⟩ := h
    have hAH : n < (x.val.val e.left).val := by rwa [htop] at hhigh
    refine ⟨e.left, true, hA, hAH, rfl, hP, ?_⟩
    intro c hh
    simp only [if_true] at hh
    change flatInside e.left (seamComplementFirst x.val) c ∧ _ at hh
    have hcP : c ≠ seamComplementFirst x.val := by
      have hh' := hh.1
      simp only [flatInside] at hh'
      intro h; have := congrArg Fin.val h
      split_ifs at hh' <;> omega
    have hcQ : c ≠ seamComplementSecond x.val := by
      have hh' := hh.1
      simp only [flatInside] at hh'
      intro h; have := congrArg Fin.val h
      split_ifs at hh' <;> omega
    have hempty := oneStep_empty_target e he c
    rw [hP, hbot, htop] at hempty
    apply hempty
    refine ⟨hh.1, ?_⟩
    change flatInside _ _ (x.val.val.swapColumns _ _ c)
    simpa only [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hcP hcQ] using hh.2
  · obtain ⟨hA, hQ, htop, hbot, hhigh⟩ := h
    have hAH : n < (x.val.val e.right).val := by rwa [hbot] at hhigh
    refine ⟨e.right, false, hA, hAH, hQ, rfl, ?_⟩
    intro c hh
    simp only [Bool.false_eq_true, if_false] at hh
    change flatInside (seamComplementSecond x.val) e.right c ∧ _ at hh
    have hcP : c ≠ seamComplementFirst x.val := by
      have hh' := hh.1
      simp only [flatInside] at hh'
      intro h; have := congrArg Fin.val h
      split_ifs at hh' <;> omega
    have hcQ : c ≠ seamComplementSecond x.val := by
      have hh' := hh.1
      simp only [flatInside] at hh'
      intro h; have := congrArg Fin.val h
      split_ifs at hh' <;> omega
    have hempty := oneStep_empty_target e he c
    rw [hQ, hbot, htop] at hempty
    apply hempty
    refine ⟨hh.1, ?_⟩
    change flatInside _ _ (x.val.val.swapColumns _ _ c)
    simpa only [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hcP hcQ] using hh.2

private theorem oneStep_exit_data (q : SeamRetainedIndex n m) (x : SeamMatchingSource n m)
    (f : GridRectangleBetween x.val.val (seamState q.1 q.2)) (hf : f.IsEmpty)
    (A : Fin (n + m + 1)) (hA : A.val < n) (hAH : n < (x.val.val A).val) :
    ∃ left : Bool,
      f.left = (if left then A else seamComplementSecond x.val) ∧
      f.right = (if left then seamComplementFirst x.val else A) ∧
      flatEmpty x.val.val (if left then A else seamComplementSecond x.val)
        (if left then seamComplementFirst x.val else A)
        (if left then x.val.val A else x.val.val (seamComplementSecond x.val))
        (if left then x.val.val (seamComplementFirst x.val) else x.val.val A) := by
  have hAm : A ∈ seamNortheastColumns x.val.val :=
    (mem_seamNortheastColumns _ _).mpr ⟨hA, hAH⟩
  rcases seamMatchingExit_endpoints q x f hf with h | h
  · have hAc : A = f.left := by
      rwa [seamMatchingExit_northeast_eq_singleton q x f, if_pos h.1,
        Finset.mem_singleton] at hAm
    refine ⟨true, hAc.symm, h.2.1, ?_⟩
    simpa only [bottom_def, top_def, h.2.1, ← hAc,
      if_true] using flatEmpty_source f hf
  · have hnot : ¬ f.left.val < n := by
      rw [h.2.1]
      exact Nat.not_lt.mpr ((mem_seamSouthwestColumns _ _).mp
        (seamComplementSecond_mem x.val)).1
    have hAc : A = f.right := by
      rwa [seamMatchingExit_northeast_eq_singleton q x f, if_neg hnot,
        Finset.mem_singleton] at hAm
    refine ⟨false, h.2.1, hAc.symm, ?_⟩
    simpa only [bottom_def, top_def, h.2.1, ← hAc,
      Bool.false_eq_true, if_false] using flatEmpty_source f hf

/-- Whether the first-block endpoint is on the left in a complete one-transition entry. -/
def seamOneStepEntryLeft : FlatKind → Bool
  | .lowFirst | .highSecond => false
  | .lowSecond | .highFirst => true

/-- Whether the first-block endpoint is on the left in a complete one-transition exit. -/
def seamOneStepExitLeft : FlatKind → Bool
  | .lowFirst | .highFirst => false
  | .lowSecond | .highSecond => true

/-- All actual one-transition paths have the stated four orientation alternatives,
without assuming equality of either retained factor. -/
theorem seamOneStep_all_orientations (p q : SeamRetainedIndex n m)
    (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState q.1 q.2))
    (hne : x ≠ y) (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) :
    ∃ (i : FlatKind) (C A : Fin (n + m + 1)),
      A.val < n ∧ n < (x.val.val A).val ∧
      flatRange i n x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      r.left = flatLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      r.right = flatRight i (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      seamComplementFirst y.val = flatFirst i
        (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      seamComplementSecond y.val = flatSecond i
        (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      e.left = (if seamOneStepEntryLeft i then A else seamComplementSecond x.val) ∧
      e.right = (if seamOneStepEntryLeft i then seamComplementFirst x.val else A) ∧
      f.left = (if seamOneStepExitLeft i then A else seamComplementSecond y.val) ∧
      f.right = (if seamOneStepExitLeft i then seamComplementFirst y.val else A) := by
  have hx := seamMatchingEntry_southwest_card p x e
  have hy := seamMatchingExit_southwest_card q y f
  obtain ⟨i, C, hi, hrL, hrR, hyP, hyQ⟩ := flatStep_cases r hne hr hx hy
  have hyApply := flatStep_apply r i C hi hrL hrR hyP hyQ
  obtain ⟨A, eb, hA, hAH, heL, heR, heData⟩ := oneStep_entry_data p x e he
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hyA : y.val.val A = x.val.val A := by
    rw [congrFun hyApply A]
    exact flatApply_high n x.val.val i _ _ C A hp.1 (seamComplementFirst_lt_second x.val)
      hA hAH hi
  obtain ⟨fb, hfL, hfR, hfData⟩ := oneStep_exit_data q y f hf A hA (by rwa [hyA])
  have hrData := flatEmpty_source r hr
  simp only [bottom_def, top_def, hrL, hrR] at hrData
  simp only [hyP, hyQ, hyApply, hyA] at hfData
  have hh := oneStep_numeric_orientations n x.val.val x.val.val.toPerm.injective A
    (seamComplementFirst x.val) (seamComplementSecond x.val) C i eb fb
    hA hp.1 (seamComplementFirst_lt_second x.val) x.property hq.2 hAH hi heData hrData hfData
  have hbool : eb = seamOneStepEntryLeft i ∧ fb = seamOneStepExitLeft i := by
    cases i <;> exact hh
  refine ⟨i, C, A, hA, hAH, hi, hrL, hrR, hyP, hyQ, ?_, ?_, ?_, ?_⟩
  · rwa [← hbool.1]
  · rwa [← hbool.1]
  · rwa [← hbool.2]
  · rwa [← hbool.2]

end OnLeConjecture.KnotFloer.GridFull
