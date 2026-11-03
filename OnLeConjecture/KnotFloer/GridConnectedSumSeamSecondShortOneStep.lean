/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondShortFrame

/-!
# One-transition corrections for remaining second-factor rectangles

Let `R`, `C`, `L` be the right side column, the zero preimage column and the
left side column of a remaining second-factor rectangle, embedded in the
second block. If the last first-factor row is zero, the path with rectangle
sides `(B, R)`, `(L, R)`, `(L, B)` is a correction, where `B` carries the row
`n`. If the last first-factor row is `n`, the path with sides `(L, A)`,
`(L, R)`, `(A, R)` is a correction, where `A` carries the row zero.

Conversely, every one-transition correction with equal first factors is of
this form. Hence one-transition corrections correspond bijectively to
remaining rectangles when the last first-factor row is `0` or `n`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section Construction
variable {x : GridState (n + 1)} {z w : GridState (m + 1)}

/-- The explicit one-transition correction of a remaining rectangle at the zero last row. -/
theorem seamSecondShortZero_exists (ρ : SeamSecondRemainingRectangle x z w)
    (ht : x (Fin.last n) = 0) :
    ∃ d : SeamCorrectionPath 1 (x, z) (x, w),
      d.2.2.1.val.left = seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
      d.2.2.1.val.right = seamRight n m ρ.val.right ∧
      d.2.2.2.1.2.1.val.left = seamRight n m ρ.val.left ∧
      d.2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
      d.2.2.2.2.val.left = seamRight n m ρ.val.left ∧
      d.2.2.2.2.val.right = seamLeft n m (x.toPerm.symm (Fin.last n)) := by
  obtain ⟨hn, hR, hRC, hCL, htop, hlt, hpR, hpL, hpC, htame, hlow, hq⟩ :=
    seamSecondShort_frame x z w ρ
  have hxl : x (Fin.last n) ≠ Fin.last n := by
    rw [ht]
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  obtain ⟨hBn, hpB⟩ := seamSecondShort_pivot_value x z (Fin.last n) hxl
  have hpBv : (seamState x z (seamLeft n m (x.toPerm.symm (Fin.last n)))).val = n := by
    rw [hpB, seamLeft_val, Fin.val_last]
  have hpCv : (seamState x z (seamRight n m (z.toPerm.symm 0))).val = 0 := by
    rw [hpC, ht, Fin.val_zero]
  clear hpB hpC
  generalize seamLeft n m (x.toPerm.symm (Fin.last n)) = B at *
  generalize seamRight n m ρ.val.right = R at *
  generalize seamRight n m (z.toPerm.symm 0) = C at *
  generalize seamRight n m ρ.val.left = L at *
  have hBR : B ≠ R := fun h => by have := congrArg Fin.val h; omega
  have hBC : B ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hBL : B ≠ L := fun h => by have := congrArg Fin.val h; omega
  have hRC' : R ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hRL : R ≠ L := fun h => by have := congrArg Fin.val h; omega
  have hLC : L ≠ C := fun h => by have := congrArg Fin.val h; omega
  obtain ⟨s₀, hs₀⟩ : ∃ s : GridState (n + m + 1),
      s = ((seamState x z).swapColumns B R).swapColumns R C := ⟨_, rfl⟩
  have hv₀ := seamSecondShort_cycle_apply (seamState x z) hBR hBC hRC'
  rw [← hs₀] at hv₀
  obtain ⟨h0B, h0R, h0C, h0o⟩ := hv₀
  have h0L := h0o L hBL.symm hRL.symm hLC
  obtain ⟨s₁, hs₁⟩ : ∃ s : GridState (n + m + 1),
      s = (s₀.swapColumns R L).swapColumns L C := ⟨_, rfl⟩
  have hv₁ := seamSecondShort_cycle_apply s₀ hRL hRC' hLC
  rw [← hs₁] at hv₁
  obtain ⟨h1R, h1L, h1C, h1o⟩ := hv₁
  have h1B := h1o B hBR hBL hBC
  have hsw₀ : seamSouthwestColumns s₀ = {R, C} := by
    ext c
    simp only [mem_seamSouthwestColumns, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hv⟩
      by_cases hcR : c = R
      · exact Or.inl hcR
      by_cases hcC : c = C
      · exact Or.inr hcC
      exfalso
      have hcB : c ≠ B := fun h => by rw [h] at hc; omega
      by_cases hcL : c = L
      · rw [hcL, h0L] at hv
        omega
      · rw [h0o c hcB hcR hcC] at hv
        exact hcC (hlow c hc hv)
    · rintro (h | h) <;> subst h
      · exact ⟨hR, by rw [h0R]; omega⟩
      · exact ⟨by omega, by rw [h0C]; omega⟩
  have hsw₁ : seamSouthwestColumns s₁ = {C, L} := by
    ext c
    simp only [mem_seamSouthwestColumns, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hv⟩
      by_cases hcC : c = C
      · exact Or.inl hcC
      by_cases hcL : c = L
      · exact Or.inr hcL
      exfalso
      have hcB : c ≠ B := fun h => by rw [h] at hc; omega
      by_cases hcR : c = R
      · rw [hcR, h1R, h0L] at hv
        omega
      · rw [h1o c hcR hcL hcC, h0o c hcB hcR hcC] at hv
        exact hcC (hlow c hc hv)
    · rintro (h | h) <;> subst h
      · exact ⟨by omega, by rw [h1C, h0R]; omega⟩
      · exact ⟨by omega, by rw [h1L, h0C]; omega⟩
  have hrows₀ : (s₀ R).val < (s₀ C).val := by rw [h0R, h0C]; omega
  have hrows₁ : (s₁ C).val < (s₁ L).val := by rw [h1C, h1L, h0R, h0C]; omega
  let a₀ := seamShortLift_matchingSourceOfPair s₀ R C hsw₀ hRC hrows₀
  let a₁ := seamShortLift_matchingSourceOfPair s₁ C L hsw₁ hCL hrows₁
  have hpart₀ : (seamComplementPartner a₀.val).val = (seamState x z).swapColumns B R := by
    rw [seamShortLift_matchingSourceOfPair_partner, hs₀, GridState.swapColumns_swapColumns]
  have hpart₁ : (seamComplementPartner a₁.val).val = s₀.swapColumns L R := by
    rw [seamShortLift_matchingSourceOfPair_partner, hs₁,
      GridState.swapColumns_comm C L ((s₀.swapColumns R L).swapColumns L C),
      GridState.swapColumns_swapColumns, GridState.swapColumns_comm R L s₀]
  have hexit : seamState x w = s₁.swapColumns L B := by
    rw [hq]
    apply GridState.ext
    intro c
    rw [GridState.swapColumns_apply, GridState.swapColumns_apply]
    by_cases hcL : c = L
    · subst hcL
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left, h1B, h0B]
    by_cases hcR : c = R
    · subst hcR
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hRL hBR.symm, h1R, h0L]
    by_cases hcB : c = B
    · subst hcB
      rw [Equiv.swap_apply_of_ne_of_ne hBL hBR, Equiv.swap_apply_right, h1L, h0C]
    by_cases hcC : c = C
    · subst hcC
      rw [Equiv.swap_apply_of_ne_of_ne hLC.symm hRC'.symm,
        Equiv.swap_apply_of_ne_of_ne hLC.symm hBC.symm, h1C, h0R]
    rw [Equiv.swap_apply_of_ne_of_ne hcL hcR, Equiv.swap_apply_of_ne_of_ne hcL hcB,
      h1o c hcR hcL hcC, h0o c hcB hcR hcC]
  let e := seamSecondShortRect (u := seamState x z) (v := (seamComplementPartner a₀.val).val)
    B R hBR hpart₀
  let r := seamSecondShortRect (u := s₀) (v := (seamComplementPartner a₁.val).val)
    L R hRL.symm hpart₁
  let f := seamSecondShortRect (u := s₁) (v := seamState x w) L B hBL.symm hexit
  have he : e.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) e (n + ρ.val.top.val) (n + ρ.val.bottom.val)
      (by omega) (by omega) (Or.inr ⟨hpBv, hpR⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo B R := hc
    rw [Grid.mem_cIoo, if_pos (by omega)] at hc'
    have := htame c (Or.inl hc'.2.2)
    omega
  have hr : r.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) r (n + ρ.val.top.val) (n + ρ.val.bottom.val)
      (by omega) (by omega)
      (Or.inl ⟨by change (s₀ L).val = _; rw [h0L]; exact hpL,
        by change (s₀ R).val = _; rw [h0R]; exact hpCv⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo L R := hc
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc'
    by_cases hcB : c = B
    · rw [hcB, h0B]
      omega
    · have hcR : c ≠ R := fun h => by rw [h] at hc'; omega
      have hcC : c ≠ C := fun h => by rw [h] at hc'; omega
      rw [h0o c hcB hcR hcC]
      have := htame c (by omega)
      omega
  have hf : f.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) f (n + ρ.val.top.val) (n + ρ.val.bottom.val)
      (by omega) (by omega)
      (Or.inr ⟨by change (s₁ L).val = _; rw [h1L, h0C]; exact hpBv,
        by change (s₁ B).val = _; rw [h1B, h0B]; exact hpR⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo L B := hc
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc'
    have hcB : c ≠ B := fun h => by rw [h] at hc'; omega
    have hcR : c ≠ R := fun h => by rw [h] at hc'; omega
    have hcC : c ≠ C := fun h => by rw [h] at hc'; omega
    have hcL : c ≠ L := fun h => by rw [h] at hc'; omega
    rw [h1o c hcR hcL hcC, h0o c hcB hcR hcC]
    have := htame c (by omega)
    omega
  have hne : a₀ ≠ a₁ := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => (s.val.val R).val) h
    change (s₀ R).val = (s₁ R).val at hh
    rw [h0R, h1R, h0L] at hh
    omega
  exact ⟨seamSecondShortPathOne a₀ a₁ e he r hne hr f hf, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The explicit one-transition correction of a remaining rectangle at the last row `n`. -/
theorem seamSecondShortLast_exists (ρ : SeamSecondRemainingRectangle x z w)
    (ht : x (Fin.last n) = Fin.last n) :
    ∃ d : SeamCorrectionPath 1 (x, z) (x, w),
      d.2.2.1.val.left = seamRight n m ρ.val.left ∧
      d.2.2.1.val.right = seamLeft n m (x.toPerm.symm 0) ∧
      d.2.2.2.1.2.1.val.left = seamRight n m ρ.val.left ∧
      d.2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
      d.2.2.2.2.val.left = seamLeft n m (x.toPerm.symm 0) ∧
      d.2.2.2.2.val.right = seamRight n m ρ.val.right := by
  obtain ⟨hn, hR, hRC, hCL, htop, hlt, hpR, hpL, hpC, htame, hlow, hq⟩ :=
    seamSecondShort_frame x z w ρ
  have hx0 : x (Fin.last n) ≠ 0 := by
    rw [ht]
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  obtain ⟨hAn, hpA⟩ := seamSecondShort_pivot_value x z 0 hx0
  have hpAv : (seamState x z (seamLeft n m (x.toPerm.symm 0))).val = 0 := by
    rw [hpA, seamLeft_val, Fin.val_zero]
  have hpCv : (seamState x z (seamRight n m (z.toPerm.symm 0))).val = n := by
    rw [hpC, ht, Fin.val_last]
  clear hpA hpC
  generalize seamLeft n m (x.toPerm.symm 0) = A at *
  generalize seamRight n m ρ.val.right = R at *
  generalize seamRight n m (z.toPerm.symm 0) = C at *
  generalize seamRight n m ρ.val.left = L at *
  have hAR : A ≠ R := fun h => by have := congrArg Fin.val h; omega
  have hAC : A ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hAL : A ≠ L := fun h => by have := congrArg Fin.val h; omega
  have hRC' : R ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hRL : R ≠ L := fun h => by have := congrArg Fin.val h; omega
  have hLC : L ≠ C := fun h => by have := congrArg Fin.val h; omega
  obtain ⟨s₀, hs₀⟩ : ∃ s : GridState (n + m + 1),
      s = ((seamState x z).swapColumns A L).swapColumns L C := ⟨_, rfl⟩
  have hv₀ := seamSecondShort_cycle_apply (seamState x z) hAL hAC hLC
  rw [← hs₀] at hv₀
  obtain ⟨h0A, h0L, h0C, h0o⟩ := hv₀
  have h0R := h0o R hAR.symm hRL hRC'
  obtain ⟨s₁, hs₁⟩ : ∃ s : GridState (n + m + 1),
      s = (s₀.swapColumns L R).swapColumns R C := ⟨_, rfl⟩
  have hv₁ := seamSecondShort_cycle_apply s₀ hRL.symm hLC hRC'
  rw [← hs₁] at hv₁
  obtain ⟨h1L, h1R, h1C, h1o⟩ := hv₁
  have h1A := h1o A hAL hAR hAC
  have hsw₀ : seamSouthwestColumns s₀ = {C, L} := by
    ext c
    simp only [mem_seamSouthwestColumns, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hv⟩
      by_cases hcC : c = C
      · exact Or.inl hcC
      by_cases hcL : c = L
      · exact Or.inr hcL
      exfalso
      have hcA : c ≠ A := fun h => by rw [h] at hc; omega
      by_cases hcR : c = R
      · rw [hcR, h0R] at hv
        omega
      · rw [h0o c hcA hcL hcC] at hv
        exact hcC (hlow c hc hv)
    · rintro (h | h) <;> subst h
      · exact ⟨by omega, by rw [h0C]; omega⟩
      · exact ⟨by omega, by rw [h0L]; omega⟩
  have hsw₁ : seamSouthwestColumns s₁ = {R, C} := by
    ext c
    simp only [mem_seamSouthwestColumns, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hv⟩
      by_cases hcR : c = R
      · exact Or.inl hcR
      by_cases hcC : c = C
      · exact Or.inr hcC
      exfalso
      have hcA : c ≠ A := fun h => by rw [h] at hc; omega
      by_cases hcL : c = L
      · rw [hcL, h1L, h0R] at hv
        omega
      · rw [h1o c hcL hcR hcC, h0o c hcA hcL hcC] at hv
        exact hcC (hlow c hc hv)
    · rintro (h | h) <;> subst h
      · exact ⟨hR, by rw [h1R, h0C]; omega⟩
      · exact ⟨by omega, by rw [h1C, h0L]; omega⟩
  have hrows₀ : (s₀ C).val < (s₀ L).val := by rw [h0C, h0L]; omega
  have hrows₁ : (s₁ R).val < (s₁ C).val := by rw [h1R, h1C, h0C, h0L]; omega
  let a₀ := seamShortLift_matchingSourceOfPair s₀ C L hsw₀ hCL hrows₀
  let a₁ := seamShortLift_matchingSourceOfPair s₁ R C hsw₁ hRC hrows₁
  have hpart₀ : (seamComplementPartner a₀.val).val = (seamState x z).swapColumns L A := by
    rw [seamShortLift_matchingSourceOfPair_partner, hs₀,
      GridState.swapColumns_comm C L (((seamState x z).swapColumns A L).swapColumns L C),
      GridState.swapColumns_swapColumns, GridState.swapColumns_comm A L]
  have hpart₁ : (seamComplementPartner a₁.val).val = s₀.swapColumns L R := by
    rw [seamShortLift_matchingSourceOfPair_partner, hs₁, GridState.swapColumns_swapColumns]
  have hexit : seamState x w = s₁.swapColumns A R := by
    rw [hq]
    apply GridState.ext
    intro c
    rw [GridState.swapColumns_apply, GridState.swapColumns_apply]
    by_cases hcL : c = L
    · subst hcL
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hAL.symm hRL.symm, h1L, h0R]
    by_cases hcR : c = R
    · subst hcR
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right, h1A, h0A]
    by_cases hcA : c = A
    · subst hcA
      rw [Equiv.swap_apply_of_ne_of_ne hAL hAR, Equiv.swap_apply_left, h1R, h0C]
    by_cases hcC : c = C
    · subst hcC
      rw [Equiv.swap_apply_of_ne_of_ne hLC.symm hRC'.symm,
        Equiv.swap_apply_of_ne_of_ne hAC.symm hRC'.symm, h1C, h0L]
    rw [Equiv.swap_apply_of_ne_of_ne hcL hcR, Equiv.swap_apply_of_ne_of_ne hcA hcR,
      h1o c hcL hcR hcC, h0o c hcA hcL hcC]
  let e := seamSecondShortRect (u := seamState x z) (v := (seamComplementPartner a₀.val).val)
    L A hAL.symm hpart₀
  let r := seamSecondShortRect (u := s₀) (v := (seamComplementPartner a₁.val).val)
    L R hRL.symm hpart₁
  let f := seamSecondShortRect (u := s₁) (v := seamState x w) A R hAR hexit
  have he : e.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) e (n + ρ.val.top.val) (n + ρ.val.bottom.val)
      (by omega) (by omega) (Or.inl ⟨hpL, hpAv⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo L A := hc
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc'
    have := htame c (by omega)
    omega
  have hr : r.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) r (n + ρ.val.top.val) (n + ρ.val.bottom.val)
      (by omega) (by omega)
      (Or.inr ⟨by change (s₀ L).val = _; rw [h0L]; exact hpCv,
        by change (s₀ R).val = _; rw [h0R]; exact hpR⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo L R := hc
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc'
    by_cases hcA : c = A
    · rw [hcA, h0A]
      omega
    · have hcL : c ≠ L := fun h => by rw [h] at hc'; omega
      have hcC : c ≠ C := fun h => by rw [h] at hc'; omega
      rw [h0o c hcA hcL hcC]
      have := htame c (by omega)
      omega
  have hf : f.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) f (n + ρ.val.top.val) (n + ρ.val.bottom.val)
      (by omega) (by omega)
      (Or.inl ⟨by change (s₁ A).val = _; rw [h1A, h0A]; exact hpL,
        by change (s₁ R).val = _; rw [h1R, h0C]; exact hpAv⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo A R := hc
    rw [Grid.mem_cIoo, if_pos (by omega)] at hc'
    have hcA : c ≠ A := fun h => by rw [h] at hc'; omega
    have hcR : c ≠ R := fun h => by rw [h] at hc'; omega
    have hcC : c ≠ C := fun h => by rw [h] at hc'; omega
    have hcL : c ≠ L := fun h => by rw [h] at hc'; omega
    rw [h1o c hcL hcR hcC, h0o c hcA hcL hcC]
    have := htame c (by omega)
    omega
  have hne : a₀ ≠ a₁ := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => (s.val.val R).val) h
    change (s₀ R).val = (s₁ R).val at hh
    rw [h0R, h1R, h0C] at hh
    omega
  exact ⟨seamSecondShortPathOne a₀ a₁ e he r hne hr f hf, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Construction

section Projection
variable {x : GridState (n + 1)} {z w : GridState (m + 1)}

/-- There is no one-transition correction from a retained state to itself. -/
theorem seamSecondShortOne_self_isEmpty : IsEmpty (SeamCorrectionPath 1 (x, z) (x, z)) :=
  ⟨fun d => (seamFirstFactorOneStepEquiv x x z d).val.source_ne_target rfl⟩

/-- Every one-transition correction with equal first factors is the explicit path of a
remaining rectangle, of the zero type or of the last type according to the last row. -/
theorem seamSecondShortOne_projection (d : SeamCorrectionPath 1 (x, z) (x, w)) :
    ∃ ρ : SeamSecondRemainingRectangle x z w,
      (x (Fin.last n) = 0 ∧
        d.2.2.1.val.left = seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
        d.2.2.1.val.right = seamRight n m ρ.val.right ∧
        d.2.2.2.1.2.1.val.left = seamRight n m ρ.val.left ∧
        d.2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
        d.2.2.2.2.val.left = seamRight n m ρ.val.left ∧
        d.2.2.2.2.val.right = seamLeft n m (x.toPerm.symm (Fin.last n))) ∨
      (x (Fin.last n) = Fin.last n ∧
        d.2.2.1.val.left = seamRight n m ρ.val.left ∧
        d.2.2.1.val.right = seamLeft n m (x.toPerm.symm 0) ∧
        d.2.2.2.1.2.1.val.left = seamRight n m ρ.val.left ∧
        d.2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
        d.2.2.2.2.val.left = seamLeft n m (x.toPerm.symm 0) ∧
        d.2.2.2.2.val.right = seamRight n m ρ.val.right) := by
  by_cases hzw : z = w
  · subst hzw
    exact (seamSecondShortOne_self_isEmpty.false d).elim
  rcases d with ⟨a, b, e, ⟨b', r, ⟨⟨⟩, hb'⟩⟩, f⟩
  have hbb : b' = b := hb'
  subst hbb
  obtain ⟨i, C, A, hAn, hAv, hi, hrL, hrR, hbP, hbQ, heL, heR, hfL, hfR⟩ :=
    seamOneStep_all_orientations (x, z) (x, w) a b' e.val r.val f.val r.property.1
      e.property r.property.2 f.property
  have hfinal := seamSecondOneStep_target_eq_swap (x, z) (x, w) a b' e.val r.val f.val i C A
    hAn hAv hi hrL hrR hbP hbQ heL heR hfL hfR
  rcases seamSecondOneStep_kind_high (x, z) (x, w) a i C A hi hfinal hzw with rfl | rfl
  · simp only [flatRange, flatLeft, flatRight, flatSecond, seamOneStepEntryLeft,
      seamOneStepExitLeft, if_true, Bool.false_eq_true, if_false]
      at hi hrL hrR hbQ heL heR hfL hfR
    have heL' : e.val.left.val < n := by rw [heL]; exact hAn
    have hsides : (r.val.left = seamComplementFirst a.val ∧ r.val.right = C) ∨
        (r.val.right = seamComplementFirst a.val ∧ r.val.left = C) := Or.inr ⟨hrR, hrL⟩
    have hfL' : f.val.left = C := hfL.trans hbQ
    have hfR' : f.val.right = e.val.left := hfR.trans heL.symm
    have ht := seamSecondOneStep_high_first_boundary (x, z) a b' e.val r.val e.property
      r.property.2 heL' C hi.1 hi.2.1 hsides
    have hpiv : e.val.left = seamLeft n m (x.toPerm.symm (Fin.last n)) :=
      seamSecondOneStep_high_first_pivot (x, z) (x, w) a b' e.val r.val f.val
        e.property r.property.2 f.property heL' C hi.1 hi.2.1 hsides hfL' hfR'
    let ρ := seamSecondOneStepHighFirstRemaining x z w a b' e.val r.val f.val e.property
      r.property.2 f.property heL' C hi.1 hi.2.1 hsides hfL' hfR'
    have hρL : seamRight n m ρ.val.left = C := by
      simp only [ρ, seamSecondOneStepHighFirstRemaining, seamSecondOneStepHighFirstRectangle,
        seamRetainedSecondRectangle_left, seamRight_secondFactorIndex,
        seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_left]
    have hρR : seamRight n m ρ.val.right = seamComplementFirst a.val := by
      simp only [ρ, seamSecondOneStepHighFirstRemaining, seamSecondOneStepHighFirstRectangle,
        seamRetainedSecondRectangle_right, seamRight_secondFactorIndex,
        seamSecondOneStepHighFirstFullRectangle, ofSwapColumns_right]
    refine ⟨ρ, Or.inl ⟨ht, hpiv, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact heR.trans hρR.symm
    · exact hrL.trans hρL.symm
    · exact hrR.trans hρR.symm
    · exact hfL'.trans hρL.symm
    · exact hfR'.trans hpiv
  · simp only [flatRange, flatLeft, flatRight, flatFirst, seamOneStepEntryLeft,
      seamOneStepExitLeft, if_true, Bool.false_eq_true, if_false]
      at hi hrL hrR hbP heL heR hfL hfR
    have heR' : e.val.right.val < n := by rw [heR]; exact hAn
    have hsides : (r.val.left = seamComplementSecond a.val ∧ r.val.right = C) ∨
        (r.val.right = seamComplementSecond a.val ∧ r.val.left = C) := Or.inl ⟨hrL, hrR⟩
    have hfL' : f.val.left = e.val.right := hfL.trans heR.symm
    have hfR' : f.val.right = C := hfR.trans hbP
    have ht := seamSecondOneStep_high_second_boundary (x, z) a b' e.val r.val e.property
      r.property.2 heR' C hi.1 hi.2.1 hsides
    have hpiv : e.val.right = seamLeft n m (x.toPerm.symm 0) :=
      seamSecondOneStep_high_second_pivot (x, z) (x, w) a b' e.val r.val f.val
        e.property r.property.2 f.property heR' C hi.1 hi.2.1 hsides hfL' hfR'
    let ρ := seamSecondOneStepHighSecondRemaining x z w a b' e.val r.val f.val e.property
      r.property.2 f.property heR' C hi.1 hi.2.1 hsides hfL' hfR'
    have hρL : seamRight n m ρ.val.left = seamComplementSecond a.val := by
      simp only [ρ, seamSecondOneStepHighSecondRemaining, seamSecondOneStepHighSecondRectangle,
        seamRetainedSecondRectangle_left, seamRight_secondFactorIndex,
        seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_left]
    have hρR : seamRight n m ρ.val.right = C := by
      simp only [ρ, seamSecondOneStepHighSecondRemaining, seamSecondOneStepHighSecondRectangle,
        seamRetainedSecondRectangle_right, seamRight_secondFactorIndex,
        seamSecondOneStepHighSecondFullRectangle, ofSwapColumns_right]
    refine ⟨ρ, Or.inr ⟨ht, ?_, hpiv, ?_, ?_, ?_, ?_⟩⟩
    · exact heL.trans hρL.symm
    · exact hrL.trans hρL.symm
    · exact hrR.trans hρR.symm
    · exact hfL'.trans hpiv
    · exact hfR'.trans hρR.symm

/-- At an interior last row there is no one-transition correction with equal first factors. -/
theorem seamSecondShortOne_isEmpty_interior (h0 : x (Fin.last n) ≠ 0)
    (hl : x (Fin.last n) ≠ Fin.last n) : IsEmpty (SeamCorrectionPath 1 (x, z) (x, w)) :=
  ⟨fun d => by
    obtain ⟨_, h | h⟩ := seamSecondShortOne_projection d
    · exact h0 h.1
    · exact hl h.1⟩

private theorem last_ne_zero_of_pos (hn : 0 < n) : (Fin.last n : Fin (n + 1)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h'
  omega

/-- The chosen explicit correction of a remaining rectangle at the zero last row. -/
def seamSecondShortZeroLift (ht : x (Fin.last n) = 0) (ρ : SeamSecondRemainingRectangle x z w) :
    SeamCorrectionPath 1 (x, z) (x, w) :=
  Classical.choose (seamSecondShortZero_exists ρ ht)

/-- The sides of the chosen correction at the zero last row. -/
theorem seamSecondShortZeroLift_spec (ht : x (Fin.last n) = 0)
    (ρ : SeamSecondRemainingRectangle x z w) :
    (seamSecondShortZeroLift ht ρ).2.2.1.val.left = seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
      (seamSecondShortZeroLift ht ρ).2.2.1.val.right = seamRight n m ρ.val.right ∧
      (seamSecondShortZeroLift ht ρ).2.2.2.1.2.1.val.left = seamRight n m ρ.val.left ∧
      (seamSecondShortZeroLift ht ρ).2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
      (seamSecondShortZeroLift ht ρ).2.2.2.2.val.left = seamRight n m ρ.val.left ∧
      (seamSecondShortZeroLift ht ρ).2.2.2.2.val.right =
        seamLeft n m (x.toPerm.symm (Fin.last n)) :=
  Classical.choose_spec (seamSecondShortZero_exists ρ ht)

/-- At the zero last row, the explicit corrections form a bijection. -/
theorem seamSecondShortZeroLift_bijective (ht : x (Fin.last n) = 0) :
    Function.Bijective (seamSecondShortZeroLift (z := z) (w := w) ht) := by
  constructor
  · intro ρ₁ ρ₂ h
    have hh : (seamSecondShortZeroLift ht ρ₁).2.2.2.1.2.1.val.left =
        (seamSecondShortZeroLift ht ρ₂).2.2.2.1.2.1.val.left := by rw [h]
    rw [(seamSecondShortZeroLift_spec ht ρ₁).2.2.1,
      (seamSecondShortZeroLift_spec ht ρ₂).2.2.1] at hh
    exact Subtype.ext (GridRectangleBetween.left_injective (seamRight_injective hh))
  · intro d
    obtain ⟨ρ, hρ | hρ⟩ := seamSecondShortOne_projection d
    · obtain ⟨_, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hρ
      obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆⟩ := seamSecondShortZeroLift_spec ht ρ
      exact ⟨ρ, seamSecondShortPathOne_ext _ _ (g₁.trans h₁.symm) (g₂.trans h₂.symm)
        (g₃.trans h₃.symm) (g₄.trans h₄.symm) (g₅.trans h₅.symm) (g₆.trans h₆.symm)⟩
    · exact (last_ne_zero_of_pos (seamSecondRemaining_pos x z w ρ) (hρ.1.symm.trans ht)).elim

/-- At the zero last row, one-transition corrections correspond to remaining rectangles. -/
def seamSecondShortZeroEquiv (ht : x (Fin.last n) = 0) :
    SeamCorrectionPath 1 (x, z) (x, w) ≃ SeamSecondRemainingRectangle x z w :=
  (Equiv.ofBijective _ (seamSecondShortZeroLift_bijective ht)).symm

/-- The chosen explicit correction of a remaining rectangle at the last row `n`. -/
def seamSecondShortLastLift (ht : x (Fin.last n) = Fin.last n)
    (ρ : SeamSecondRemainingRectangle x z w) : SeamCorrectionPath 1 (x, z) (x, w) :=
  Classical.choose (seamSecondShortLast_exists ρ ht)

/-- The sides of the chosen correction at the last row `n`. -/
theorem seamSecondShortLastLift_spec (ht : x (Fin.last n) = Fin.last n)
    (ρ : SeamSecondRemainingRectangle x z w) :
    (seamSecondShortLastLift ht ρ).2.2.1.val.left = seamRight n m ρ.val.left ∧
      (seamSecondShortLastLift ht ρ).2.2.1.val.right = seamLeft n m (x.toPerm.symm 0) ∧
      (seamSecondShortLastLift ht ρ).2.2.2.1.2.1.val.left = seamRight n m ρ.val.left ∧
      (seamSecondShortLastLift ht ρ).2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
      (seamSecondShortLastLift ht ρ).2.2.2.2.val.left = seamLeft n m (x.toPerm.symm 0) ∧
      (seamSecondShortLastLift ht ρ).2.2.2.2.val.right = seamRight n m ρ.val.right :=
  Classical.choose_spec (seamSecondShortLast_exists ρ ht)

/-- At the last row `n`, the explicit corrections form a bijection. -/
theorem seamSecondShortLastLift_bijective (ht : x (Fin.last n) = Fin.last n) :
    Function.Bijective (seamSecondShortLastLift (z := z) (w := w) ht) := by
  constructor
  · intro ρ₁ ρ₂ h
    have hh : (seamSecondShortLastLift ht ρ₁).2.2.2.1.2.1.val.left =
        (seamSecondShortLastLift ht ρ₂).2.2.2.1.2.1.val.left := by rw [h]
    rw [(seamSecondShortLastLift_spec ht ρ₁).2.2.1,
      (seamSecondShortLastLift_spec ht ρ₂).2.2.1] at hh
    exact Subtype.ext (GridRectangleBetween.left_injective (seamRight_injective hh))
  · intro d
    obtain ⟨ρ, hρ | hρ⟩ := seamSecondShortOne_projection d
    · exact (last_ne_zero_of_pos (seamSecondRemaining_pos x z w ρ) (ht.symm.trans hρ.1)).elim
    · obtain ⟨_, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hρ
      obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆⟩ := seamSecondShortLastLift_spec ht ρ
      exact ⟨ρ, seamSecondShortPathOne_ext _ _ (g₁.trans h₁.symm) (g₂.trans h₂.symm)
        (g₃.trans h₃.symm) (g₄.trans h₄.symm) (g₅.trans h₅.symm) (g₆.trans h₆.symm)⟩

/-- At the last row `n`, one-transition corrections correspond to remaining rectangles. -/
def seamSecondShortLastEquiv (ht : x (Fin.last n) = Fin.last n) :
    SeamCorrectionPath 1 (x, z) (x, w) ≃ SeamSecondRemainingRectangle x z w :=
  (Equiv.ofBijective _ (seamSecondShortLastLift_bijective ht)).symm

end Projection

end OnLeConjecture.KnotFloer.GridFull
