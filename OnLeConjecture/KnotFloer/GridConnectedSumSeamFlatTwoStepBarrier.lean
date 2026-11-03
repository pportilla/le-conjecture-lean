/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepProjection

/-! # Two consecutive neutral seam transitions

The four neutral transitions are expressed by their actual point permutations.
The local exclusion below tests the exchanged points against the empty rectangles.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m k : ℕ}

inductive FlatKind | lowFirst | lowSecond | highFirst | highSecond

def flatFirst (i : FlatKind) (P Q C : Fin k) : Fin k :=
  match i with
  | .lowFirst | .lowSecond => P
  | .highFirst => Q
  | .highSecond => C

def flatSecond (i : FlatKind) (P Q C : Fin k) : Fin k :=
  match i with
  | .lowFirst | .lowSecond => Q
  | .highFirst => C
  | .highSecond => P

def flatLeft (i : FlatKind) (_P Q C : Fin k) : Fin k :=
  match i with
  | .lowFirst | .highFirst => C
  | .lowSecond | .highSecond => Q

def flatRight (i : FlatKind) (P _Q C : Fin k) : Fin k :=
  match i with
  | .lowFirst | .highFirst => P
  | .lowSecond | .highSecond => C

def flatApply (i : FlatKind) (x : Fin k → Fin k) (P Q C j : Fin k) : Fin k :=
  match i with
  | .lowFirst | .highSecond =>
    if j = P then x Q else if j = Q then x C else if j = C then x P else x j
  | .lowSecond | .highFirst =>
    if j = P then x C else if j = Q then x P else if j = C then x Q else x j

def flatRange (i : FlatKind) (n : ℕ) (x : Fin k → Fin k) (P Q C : Fin k) : Prop :=
  match i with
  | .lowFirst => C.val < n ∧ (x C).val ≤ n ∧ (x Q).val < (x C).val
  | .lowSecond => C.val < n ∧ (x C).val ≤ n ∧ (x C).val < (x P).val
  | .highFirst => n ≤ C.val ∧ n < (x C).val ∧ Q < C
  | .highSecond => n ≤ C.val ∧ n < (x C).val ∧ C < P

def flatInside (a b c : Fin k) : Prop :=
  if a.val < b.val then a.val < c.val ∧ c.val < b.val else a.val < c.val ∨ c.val < b.val

def flatEmpty (x : Fin k → Fin k) (l r b t : Fin k) : Prop :=
  ∀ c, ¬ (flatInside l r c ∧ flatInside b t (x c))

private theorem flatVal_injective (x : Fin k → Fin k) (hx : Function.Injective x) (a b : Fin k) :
    (x a).val = (x b).val → a.val = b.val := fun h =>
  congrArg Fin.val (hx (Fin.ext h))


theorem flatEmpty_source {x y : GridState k} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) : flatEmpty x r.left r.right r.bottom r.top := by
  intro c h
  apply (isEmpty_iff_forall_notMem_cIoo r).mp he c
  · exact (Grid.mem_cIoo _ _ _).mpr ⟨r.left_ne_right, h.1⟩
  · exact (Grid.mem_cIoo _ _ _).mpr ⟨r.bottom_ne_top, h.2⟩

private theorem flatEmpty_target {x y : GridState k} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) : flatEmpty y r.left r.right r.bottom r.top := by
  intro c h
  apply (isEmpty_iff_forall_notMem_cIoo_target r).mp he c
  · exact (Grid.mem_cIoo _ _ _).mpr ⟨r.left_ne_right, h.1⟩
  · have hh := (Grid.mem_cIoo _ _ _).mpr ⟨r.bottom_ne_top, h.2⟩
    simpa only [r.map_right, r.map_left, bottom_def, top_def] using hh

theorem flatStep_cases {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hne : x ≠ y) (he : r.IsEmpty)
    (hx : (seamSouthwestColumns x.val.val).card = 2)
    (hy : (seamSouthwestColumns y.val.val).card = 2) :
    ∃ i : FlatKind, ∃ C : Fin (n + m + 1),
      flatRange i n x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      r.left = flatLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      r.right = flatRight i (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      seamComplementFirst y.val = flatFirst i
        (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      seamComplementSecond y.val = flatSecond i
        (seamComplementFirst x.val) (seamComplementSecond x.val) C := by
  obtain ⟨S, C, hS, hC, hsides⟩ := seamOneStep_internal_one_southwest hne r hx hy
  have hSm : S ∈ seamSouthwestColumns x.val.val := by
    rcases hS with rfl | rfl
    · exact seamComplementFirst_mem x.val
    · exact seamComplementSecond_mem x.val
  have htype := seamOneStep_internal_other_ranges r hx hy S C hSm hC hsides
  rcases hS with rfl | rfl <;> rcases htype with ⟨hCn, hCv⟩ | ⟨hCn, hCv⟩
  · obtain ⟨hL, hR, hrow, hP, hQ, _, _, _⟩ := seamOneStep_low_first r he C hCn hCv hsides
    exact ⟨.lowFirst, C, ⟨hCn, hCv, hrow⟩, hL, hR, hP, hQ⟩
  · obtain ⟨hL, hR, hcol, hP, hQ, _, _⟩ := seamOneStep_high_first r he hx C hCn hCv hsides
    exact ⟨.highFirst, C, ⟨hCn, hCv, hcol⟩, hL, hR, hP, hQ⟩
  · obtain ⟨hL, hR, hrow, hP, hQ, _, _, _⟩ := seamOneStep_low_second r he C hCn hCv hsides
    exact ⟨.lowSecond, C, ⟨hCn, hCv, hrow⟩, hL, hR, hP, hQ⟩
  · obtain ⟨hL, hR, hcol, hP, hQ, _, _⟩ := seamOneStep_high_second r he hx C hCn hCv hsides
    exact ⟨.highSecond, C, ⟨hCn, hCv, hcol⟩, hL, hR, hP, hQ⟩

private theorem flatSwap_formula (i : FlatKind) (x : GridState k) (P Q C a : Fin k)
    (hPQ : P ≠ Q) (hPC : P ≠ C) (hQC : Q ≠ C) :
    ((x.swapColumns (flatLeft i P Q C) (flatRight i P Q C)).swapColumns
      (flatFirst i P Q C) (flatSecond i P Q C)) a = flatApply i x P Q C a := by
  cases i <;> by_cases haP : a = P
  all_goals first
    | subst a; simp [flatFirst, flatSecond, flatLeft, flatRight, flatApply,
        GridState.swapColumns_apply, Equiv.swap_apply_def, hPQ, hPC, hQC,
        hPQ.symm]
    | skip
  all_goals by_cases haQ : a = Q
  all_goals first
    | subst a; simp [flatFirst, flatSecond, flatLeft, flatRight, flatApply,
        GridState.swapColumns_apply, Equiv.swap_apply_def, hPQ, hPC, hQC,
        hPQ.symm]
    | skip
  all_goals by_cases haC : a = C
  all_goals first
    | subst a; simp [flatFirst, flatSecond, flatLeft, flatRight, flatApply,
        GridState.swapColumns_apply, Equiv.swap_apply_def, hPQ, hPC, hQC,
        hPQ.symm, hPC.symm, hQC.symm]
    | simp [flatFirst, flatSecond, flatLeft, flatRight, flatApply,
        GridState.swapColumns_apply, Equiv.swap_apply_def, haP, haQ, haC]

theorem flatStep_apply {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (i : FlatKind) (C : Fin (n + m + 1))
    (hi : flatRange i n x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) C)
    (hL : r.left = flatLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C)
    (hR : r.right = flatRight i (seamComplementFirst x.val) (seamComplementSecond x.val) C)
    (hP : seamComplementFirst y.val = flatFirst i
      (seamComplementFirst x.val) (seamComplementSecond x.val) C)
    (hQ : seamComplementSecond y.val = flatSecond i
      (seamComplementFirst x.val) (seamComplementSecond x.val) C) :
    (y.val.val : Fin (n + m + 1) → Fin (n + m + 1)) =
      flatApply i x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) C := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hrows : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hCP : C ≠ seamComplementFirst x.val := by
    cases i <;> simp only [flatRange, Fin.lt_def] at hi <;> intro h <;> subst C <;> omega
  have hCQ : C ≠ seamComplementSecond x.val := by
    cases i <;> simp only [flatRange, Fin.lt_def] at hi <;> intro h <;> subst C <;> omega
  have hh := congrArg (fun s : GridState (n + m + 1) =>
    s.swapColumns (seamComplementFirst y.val) (seamComplementSecond y.val)) r.target_eq_swapColumns
  change (y.val.val.swapColumns _ _).swapColumns _ _ = _ at hh
  rw [GridState.swapColumns_swapColumns] at hh
  rw [hL, hR, hP, hQ] at hh
  funext a
  exact (congrArg (fun s : GridState (n + m + 1) => s a) hh).trans
    (flatSwap_formula i x.val.val _ _ C a hpq.ne hCP.symm hCQ.symm)

theorem flatApply_high (n : ℕ) (x : Fin k → Fin k) (i : FlatKind)
    (P Q C A : Fin k) (hP : n ≤ P.val) (hPQ : P < Q)
    (hA : A.val < n) (hAH : n < (x A).val) (hi : flatRange i n x P Q C) :
    flatApply i x P Q C A = x A := by
  have hAP : A ≠ P := by intro h; have := congrArg Fin.val h; omega
  have hAQ : A ≠ Q := by intro h; have := congrArg Fin.val h; omega
  have hAC : A ≠ C := by
    cases i <;> simp only [flatRange, Fin.lt_def] at hi <;> intro h <;> subst A <;> omega
  cases i <;> simp only [flatApply, if_neg hAP, if_neg hAQ, if_neg hAC]

set_option maxHeartbeats 12000000 in
-- The universal order proof separates four neutral types and all endpoint coincidences.
private theorem flatTwoStep_numeric
    (n : ℕ) (x : Fin k → Fin k) (hx : Function.Injective x)
    (A P Q C D : Fin k) (i j : FlatKind) (entryLeft exitLeft : Bool)
    (hA : A.val < n) (hP : n ≤ P.val) (hPQ : P < Q)
    (hrows : (x P).val < (x Q).val) (hQ : (x Q).val ≤ n) (hAH : n < (x A).val)
    (hi : flatRange i n x P Q C)
    (hj : flatRange j n (flatApply i x P Q C) (flatFirst i P Q C) (flatSecond i P Q C) D)
    (he : flatEmpty x (if entryLeft then A else Q) (if entryLeft then P else A)
      (if entryLeft then x Q else x A) (if entryLeft then x A else x P))
    (hr : flatEmpty x (flatLeft i P Q C) (flatRight i P Q C)
      (x (flatLeft i P Q C)) (x (flatRight i P Q C)))
    (ht : let y := flatApply i x P Q C
      flatEmpty y (flatLeft j (flatFirst i P Q C) (flatSecond i P Q C) D)
        (flatRight j (flatFirst i P Q C) (flatSecond i P Q C) D)
        (y (flatLeft j (flatFirst i P Q C) (flatSecond i P Q C) D))
        (y (flatRight j (flatFirst i P Q C) (flatSecond i P Q C) D)))
    (hf : let y := flatApply i x P Q C
      let z := flatApply j y (flatFirst i P Q C) (flatSecond i P Q C) D
      let P' := flatFirst j (flatFirst i P Q C) (flatSecond i P Q C) D
      let Q' := flatSecond j (flatFirst i P Q C) (flatSecond i P Q C) D
      flatEmpty z (if exitLeft then A else Q') (if exitLeft then P' else A)
        (if exitLeft then z A else z Q') (if exitLeft then z P' else z A)) : False := by
  have hAP : A ≠ P := by intro h; have := congrArg Fin.val h; omega
  have hAQ : A ≠ Q := by intro h; have := congrArg Fin.val h; omega
  have hCP : C ≠ P := by
    cases i <;> simp only [flatRange, Fin.lt_def] at hi <;>
      intro h <;> subst C <;> omega
  have hCQ : C ≠ Q := by
    cases i <;> simp only [flatRange, Fin.lt_def] at hi <;>
      intro h <;> subst C <;> omega
  have hCA : C ≠ A := by
    cases i <;> simp only [flatRange, Fin.lt_def] at hi <;>
      intro h <;> subst C <;> omega
  have hPC := hCP.symm
  have hQC := hCQ.symm
  have hAC := hCA.symm
  have hPA := hAP.symm
  have hQA := hAQ.symm
  have hQP := hPQ.ne.symm
  have hpq := hPQ.ne
  have hCAV := flatVal_injective x hx C A
  have hCAVne : C.val ≠ A.val := fun h => hCA (Fin.ext h)
  have hDC := flatVal_injective x hx D C
  have hDP := flatVal_injective x hx D P
  have hDQ := flatVal_injective x hx D Q
  have hDA := flatVal_injective x hx D A
  have eC := he C; have eD := he D
  have rA := hr A; have rD := hr D
  have tA := ht A; have tP := ht P; have tQ := ht Q; have tC := ht C
  have fP := hf P; have fQ := hf Q; have fC := hf C; have fD := hf D
  clear he hr ht hf hx
  cases i <;> cases j <;> cases entryLeft <;> cases exitLeft <;>
    simp only [flatRange, flatApply, flatFirst, flatSecond, flatLeft, flatRight,
      Bool.false_eq_true, hAP, hAQ, hCP, hCQ, 
      hPC, hQC, hAC, hQP, hpq, ↓reduceIte, Fin.lt_def] at *
  all_goals
    by_cases hdP : D = P
    · subst D
      simp only [hAP, hCP, hPC, hQP, hpq,
        ↓reduceIte, flatInside] at *
      all_goals (try split_ifs at eC) <;> try omega
      all_goals (try split_ifs at rA) <;> try omega
      all_goals (try split_ifs at tA) <;> try omega
    · by_cases hdQ : D = Q
      · subst D
        simp only [hAQ, hCQ, hQC, hQP, hpq,
          ↓reduceIte, flatInside] at *
        all_goals (try split_ifs at eC) <;> try omega
        all_goals (try split_ifs at rA) <;> try omega
        all_goals (try split_ifs at tA) <;> try omega
      · by_cases hdC : D = C
        · subst D
          simp only [hCP, hCQ, hPC, hQC, hAC, 
            ↓reduceIte, flatInside] at *
          all_goals (try split_ifs at eC) <;> try omega
          all_goals (try split_ifs at rA) <;> try omega
          all_goals (try split_ifs at tA) <;> try omega
        · by_cases hdA : D = A
          · subst D
            simp only [hAP, hAQ, hCA, hAC, hPA, hQA, 
              ↓reduceIte, flatInside] at *
            all_goals (try split_ifs at eC) <;> try omega
          · have hpD : P ≠ D := Ne.symm hdP
            have hqD : Q ≠ D := Ne.symm hdQ
            have hcD : C ≠ D := Ne.symm hdC
            have haD : A ≠ D := Ne.symm hdA
            have hvP : D.val ≠ P.val := fun h => hdP (Fin.ext h)
            have hvQ : D.val ≠ Q.val := fun h => hdQ (Fin.ext h)
            have hvC : D.val ≠ C.val := fun h => hdC (Fin.ext h)
            have hvA : D.val ≠ A.val := fun h => hdA (Fin.ext h)
            simp only [hdP, hdQ, hdC, hdA, hpD, hqD, hcD, haD, ↓reduceIte, flatInside] at *
            all_goals (try split_ifs at eC) <;> try omega
            all_goals (try split_ifs at rA) <;> try omega
            all_goals (try split_ifs at tA) <;> try omega
            all_goals (try split_ifs at rD) ; try omega
            all_goals (try split_ifs at tP) ; try omega
            all_goals (try split_ifs at tQ) ; try omega
            all_goals (try split_ifs at tC) ; try omega
            all_goals (try split_ifs at fD) <;> try omega
            all_goals (try split_ifs at eD) ; try omega
            all_goals (try split_ifs at fC) ; try omega
            all_goals (try split_ifs at fP) ; try omega
            all_goals (try split_ifs at fQ) ; omega


theorem flatEntry_data (p : SeamRetainedIndex n m) (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : e.IsEmpty) :
    ∃ A : Fin (n + m + 1), ∃ left : Bool, A.val < n ∧ n < (x.val.val A).val ∧
      flatEmpty x.val.val (if left then A else seamComplementSecond x.val)
        (if left then seamComplementFirst x.val else A)
        (if left then x.val.val (seamComplementSecond x.val) else x.val.val A)
        (if left then x.val.val A else x.val.val (seamComplementFirst x.val)) := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  rcases seamMatchingEntry_endpoints p x e he with h | h
  · obtain ⟨hA, hP, hbot, htop, hhigh⟩ := h
    have hAH : n < (x.val.val e.left).val := by rwa [htop] at hhigh
    refine ⟨e.left, true, hA, hAH, ?_⟩
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
    have hempty := flatEmpty_target e he c
    rw [hP, hbot, htop] at hempty
    apply hempty
    refine ⟨hh.1, ?_⟩
    change flatInside _ _ (x.val.val.swapColumns _ _ c)
    simpa only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcP hcQ] using hh.2
  · obtain ⟨hA, hQ, htop, hbot, hhigh⟩ := h
    have hAH : n < (x.val.val e.right).val := by rwa [hbot] at hhigh
    refine ⟨e.right, false, hA, hAH, ?_⟩
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
    have hempty := flatEmpty_target e he c
    rw [hQ, hbot, htop] at hempty
    apply hempty
    refine ⟨hh.1, ?_⟩
    change flatInside _ _ (x.val.val.swapColumns _ _ c)
    simpa only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcP hcQ] using hh.2

theorem flatExit_data (q : SeamRetainedIndex n m) (x : SeamMatchingSource n m)
    (f : GridRectangleBetween x.val.val (seamState q.1 q.2)) (hf : f.IsEmpty)
    (A : Fin (n + m + 1)) (hA : A.val < n) (hAH : n < (x.val.val A).val) :
    ∃ left : Bool,
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
    refine ⟨true, ?_⟩
    simpa only [bottom_def, top_def, h.2.1, ← hAc,
      Bool.false_eq_true, Bool.true_eq, if_false, if_true] using flatEmpty_source f hf
  · have hnot : ¬ f.left.val < n := by
      rw [h.2.1]
      exact Nat.not_lt.mpr ((mem_seamSouthwestColumns _ _).mp
        (seamComplementSecond_mem x.val)).1
    have hAc : A = f.right := by
      rwa [seamMatchingExit_northeast_eq_singleton q x f, if_neg hnot,
        Finset.mem_singleton] at hAm
    refine ⟨false, ?_⟩
    simpa only [bottom_def, top_def, h.2.1, ← hAc,
      Bool.false_eq_true, Bool.true_eq, if_false, if_true] using flatEmpty_source f hf

/-- A complete correction cannot have two consecutive internal transitions with
one northeast point at all three matching sources. The retained factors are arbitrary. -/
theorem seamFlatTwoStep_false (p q : SeamRetainedIndex n m) (a b c : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (f : GridRectangleBetween c.val.val (seamState q.1 q.2))
    (hab : a ≠ b) (hbc : b ≠ c) (he : e.IsEmpty) (hr : r.IsEmpty)
    (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns b.val.val).card = 1) : False := by
  have haSW := seamMatchingEntry_southwest_card p a e
  have hcSW := seamMatchingExit_southwest_card q c f
  have hbSW : (seamSouthwestColumns b.val.val).card = 2 := by
    rw [seamSouthwestColumns_card, hmid]
  obtain ⟨i, C, hi, hrL, hrR, hbP, hbQ⟩ := flatStep_cases r hab hr haSW hbSW
  obtain ⟨j, D, hj, htL, htR, hcP, hcQ⟩ := flatStep_cases t hbc ht hbSW hcSW
  have hbApply := flatStep_apply r i C hi hrL hrR hbP hbQ
  have hcApply := flatStep_apply t j D hj htL htR hcP hcQ
  obtain ⟨A, eLeft, hA, hAH, heData⟩ := flatEntry_data p a e he
  have haP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have haQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hbPmem := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem b.val)
  have hbA : b.val.val A = a.val.val A := by
    rw [congrFun hbApply A]
    exact flatApply_high n a.val.val i _ _ C A haP.1 (seamComplementFirst_lt_second a.val)
      hA hAH hi
  have hcA : c.val.val A = b.val.val A := by
    rw [congrFun hcApply A]
    exact flatApply_high n b.val.val j _ _ D A hbPmem.1 (seamComplementFirst_lt_second b.val)
      hA (by rwa [hbA]) hj
  obtain ⟨fLeft, hfData⟩ := flatExit_data q c f hf A hA (by rwa [hcA, hbA])
  apply flatTwoStep_numeric n a.val.val a.val.val.toPerm.injective A
    (seamComplementFirst a.val) (seamComplementSecond a.val) C D i j eLeft fLeft
    hA haP.1 (seamComplementFirst_lt_second a.val) a.property haQ.2 hAH hi
  · simpa only [hbApply, hbP, hbQ] using hj
  · exact heData
  · simpa only [bottom_def, top_def, hrL, hrR] using flatEmpty_source r hr
  · simpa only [bottom_def, top_def, htL, htR, hbP, hbQ, hbApply] using flatEmpty_source t ht
  · simpa only [hcP, hcQ, hcApply, hbP, hbQ, hbApply] using hfData


/-- The middle matching source of an actual two-step correction cannot have one northeast point. -/
theorem seamCorrectionTwo_middle_ne_one (p q : SeamRetainedIndex n m)
    (path : SeamCorrectionPath 2 p q) :
    (seamNortheastColumns path.2.2.2.1.1.val.val).card ≠ 1 := by
  rcases path with ⟨a, c, e, ⟨b, r, ⟨c', t, tail⟩⟩, f⟩
  have hlast : c' = c := tail.property
  subst c'
  intro hmid
  exact seamFlatTwoStep_false p q a b c e.val r.val t.val f.val r.property.1 t.property.1
    e.property r.property.2 t.property.2 f.property hmid

end OnLeConjecture.KnotFloer.GridFull
