/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondShortFrame

/-!
# Two-transition corrections for remaining second-factor rectangles

Let `R`, `C`, `L` be the right side column, the zero preimage column and the
left side column of a remaining second-factor rectangle, embedded in the
second block. Let `A` and `B` be the first-block columns of the rows `0` and
`n` of the first factor. If the last first-factor row `t` satisfies
`0 < t < n`, the path with rectangle sides `(L, A)`, `(B, R)`, `(A, R)`,
`(L, B)` is a two-transition correction. Its matching sources have the
southwest columns `{C, L}`, `{R, C, L}` and `{C, L}`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section Construction
variable {x : GridState (n + 1)} {z w : GridState (m + 1)}

/-- The two-transition correction for abstract columns `A`, `B`, `R`, `C`, `L` and rows
`0 < t < n < K < H` satisfying the coordinate description of a remaining rectangle. -/
theorem seamSecondShortInterior_exists_aux (A B R C L : Fin (n + m + 1)) (t K H : ℕ)
    (hn : 0 < n) (hAn : A.val < n) (hBn : B.val < n) (hR : n ≤ R.val) (hRC : R.val < C.val)
    (hCL : C.val < L.val) (ht0 : 0 < t) (htn : t < n) (hnK : n < K) (hKH : K < H)
    (hpAv : (seamState x z A).val = 0) (hpBv : (seamState x z B).val = n)
    (hpR : (seamState x z R).val = K) (hpL : (seamState x z L).val = H)
    (hpC : (seamState x z C).val = t)
    (htame : ∀ c : Fin (n + m + 1), c.val < R.val ∨ L.val < c.val →
      (seamState x z c).val ≤ n ∨ (K < (seamState x z c).val ∧ (seamState x z c).val < H))
    (hlow : ∀ c : Fin (n + m + 1), n ≤ c.val → (seamState x z c).val ≤ n → c = C)
    (hq : seamState x w = (seamState x z).swapColumns L R) :
    ∃ d : SeamCorrectionPath 2 (x, z) (x, w),
      d.2.2.1.val.left = L ∧ d.2.2.1.val.right = A ∧
      d.2.2.2.1.2.1.val.left = B ∧ d.2.2.2.1.2.1.val.right = R ∧
      d.2.2.2.1.2.2.2.1.val.left = A ∧ d.2.2.2.1.2.2.2.1.val.right = R ∧
      d.2.2.2.2.val.left = L ∧ d.2.2.2.2.val.right = B := by
  have hAB : A ≠ B := fun h => by rw [h] at hpAv; omega
  have hAR : A ≠ R := fun h => by have := congrArg Fin.val h; omega
  have hAC : A ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hAL : A ≠ L := fun h => by have := congrArg Fin.val h; omega
  have hBR : B ≠ R := fun h => by have := congrArg Fin.val h; omega
  have hBC : B ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hBL : B ≠ L := fun h => by have := congrArg Fin.val h; omega
  have hRC' : R ≠ C := fun h => by have := congrArg Fin.val h; omega
  have hRL : R ≠ L := fun h => by have := congrArg Fin.val h; omega
  have hLC : L ≠ C := fun h => by have := congrArg Fin.val h; omega
  obtain ⟨s₀, hs₀⟩ : ∃ s : GridState (n + m + 1),
      s = ((seamState x z).swapColumns A L).swapColumns L C := ⟨_, rfl⟩
  have hv₀ := seamSecondShort_cycle_apply (seamState x z) hAL hAC hLC
  rw [← hs₀] at hv₀
  obtain ⟨h0A, h0L, h0C, h0o⟩ := hv₀
  have h0R := h0o R hAR.symm hRL hRC'
  have h0B := h0o B hAB.symm hBL hBC
  obtain ⟨s₁, hs₁⟩ : ∃ s : GridState (n + m + 1),
      s = (s₀.swapColumns B R).swapColumns R C := ⟨_, rfl⟩
  have hv₁ := seamSecondShort_cycle_apply s₀ hBR hBC hRC'
  rw [← hs₁] at hv₁
  obtain ⟨h1B, h1R, h1C, h1o⟩ := hv₁
  have h1A := h1o A hAB hAR hAC
  have h1L := h1o L hBL.symm hRL.symm hLC
  obtain ⟨s₂, hs₂⟩ : ∃ s : GridState (n + m + 1),
      s = (s₁.swapColumns A R).swapColumns C L := ⟨_, rfl⟩
  have hv₂ := seamSecondShort_doubleSwap_apply s₁ hAC hAL hRC' hRL
  rw [← hs₂] at hv₂
  obtain ⟨h2A, h2R, h2C, h2L, h2o⟩ := hv₂
  have h2B := h2o B hAB.symm hBR hBC hBL
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
      rw [h0o c hcA hcL hcC] at hv
      exact hcC (hlow c hc hv)
    · rintro (h | h) <;> subst h
      · exact ⟨by omega, by rw [h0C]; omega⟩
      · exact ⟨by omega, by rw [h0L]; omega⟩
  have hsw₁ : seamSouthwestColumns s₁ = {R, C, L} := by
    ext c
    simp only [mem_seamSouthwestColumns, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hv⟩
      by_cases hcR : c = R
      · exact Or.inl hcR
      by_cases hcC : c = C
      · exact Or.inr (Or.inl hcC)
      by_cases hcL : c = L
      · exact Or.inr (Or.inr hcL)
      exfalso
      have hcA : c ≠ A := fun h => by rw [h] at hc; omega
      have hcB : c ≠ B := fun h => by rw [h] at hc; omega
      rw [h1o c hcB hcR hcC, h0o c hcA hcL hcC] at hv
      exact hcC (hlow c hc hv)
    · rintro (h | h | h) <;> subst h
      · exact ⟨hR, by rw [h1R, h0C]; omega⟩
      · exact ⟨by omega, by rw [h1C, h0B]; omega⟩
      · exact ⟨by omega, by rw [h1L, h0L]; omega⟩
  have hsw₂ : seamSouthwestColumns s₂ = {C, L} := by
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
      have hcB : c ≠ B := fun h => by rw [h] at hc; omega
      by_cases hcR : c = R
      · rw [hcR, h2R, h1A, h0A] at hv
        omega
      · rw [h2o c hcA hcR hcC hcL, h1o c hcB hcR hcC, h0o c hcA hcL hcC] at hv
        exact hcC (hlow c hc hv)
    · rintro (h | h) <;> subst h
      · exact ⟨by omega, by rw [h2C, h1L, h0L]; omega⟩
      · exact ⟨by omega, by rw [h2L, h1C, h0B]; omega⟩
  have hrows₀ : (s₀ C).val < (s₀ L).val := by rw [h0C, h0L]; omega
  have hrows₁ : (s₁ R).val < (s₁ C).val := by rw [h1R, h1C, h0C, h0B]; omega
  have hrows₂ : (s₂ C).val < (s₂ L).val := by rw [h2C, h2L, h1L, h1C, h0L, h0B]; omega
  let a₀ := seamShortLift_matchingSourceOfPair s₀ C L hsw₀ hCL hrows₀
  let a₁ := seamSecondShort_sourceOfTriple s₁ R C L hsw₁ hRC hCL hrows₁
  let a₂ := seamShortLift_matchingSourceOfPair s₂ C L hsw₂ hCL hrows₂
  have hpart₀ : (seamComplementPartner a₀.val).val = (seamState x z).swapColumns L A := by
    rw [seamShortLift_matchingSourceOfPair_partner, hs₀,
      GridState.swapColumns_comm C L (((seamState x z).swapColumns A L).swapColumns L C),
      GridState.swapColumns_swapColumns, GridState.swapColumns_comm A L]
  have hpart₁ : (seamComplementPartner a₁.val).val = s₀.swapColumns B R := by
    rw [seamSecondShort_sourceOfTriple_partner, hs₁, GridState.swapColumns_swapColumns]
  have hpart₂ : (seamComplementPartner a₂.val).val = s₁.swapColumns A R := by
    rw [seamShortLift_matchingSourceOfPair_partner, hs₂, GridState.swapColumns_swapColumns]
  have hexit : seamState x w = s₂.swapColumns L B := by
    rw [hq]
    apply GridState.ext
    intro c
    rw [GridState.swapColumns_apply, GridState.swapColumns_apply]
    by_cases hcL : c = L
    · subst hcL
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left, h2B, h1B, h0R]
    by_cases hcR : c = R
    · subst hcR
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hRL hBR.symm, h2R, h1A, h0A]
    by_cases hcB : c = B
    · subst hcB
      rw [Equiv.swap_apply_of_ne_of_ne hBL hBR, Equiv.swap_apply_right, h2L, h1C, h0B]
    by_cases hcA : c = A
    · subst hcA
      rw [Equiv.swap_apply_of_ne_of_ne hAL hAR, Equiv.swap_apply_of_ne_of_ne hAL hAB, h2A,
        h1R, h0C]
    by_cases hcC : c = C
    · subst hcC
      rw [Equiv.swap_apply_of_ne_of_ne hLC.symm hRC'.symm,
        Equiv.swap_apply_of_ne_of_ne hLC.symm hBC.symm, h2C, h1L, h0L]
    rw [Equiv.swap_apply_of_ne_of_ne hcL hcR, Equiv.swap_apply_of_ne_of_ne hcL hcB,
      h2o c hcA hcR hcC hcL, h1o c hcB hcR hcC, h0o c hcA hcL hcC]
  let e := seamSecondShortRect (u := seamState x z) (v := (seamComplementPartner a₀.val).val)
    L A hAL.symm hpart₀
  let r := seamSecondShortRect (u := s₀) (v := (seamComplementPartner a₁.val).val)
    B R hBR hpart₁
  let t' := seamSecondShortRect (u := s₁) (v := (seamComplementPartner a₂.val).val)
    A R hAR hpart₂
  let f := seamSecondShortRect (u := s₂) (v := seamState x w) L B hBL.symm hexit
  have he : e.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) e K H hnK hKH (Or.inl ⟨hpL, hpAv⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo L A := hc
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc'
    have := htame c (by omega)
    omega
  have hr : r.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) r K H hnK hKH
      (Or.inr ⟨by change (s₀ B).val = _; rw [h0B]; exact hpBv,
        by change (s₀ R).val = _; rw [h0R]; exact hpR⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo B R := hc
    rw [Grid.mem_cIoo, if_pos (by omega)] at hc'
    by_cases hcA : c = A
    · rw [hcA, h0A]
      omega
    · have hcL : c ≠ L := fun h => by rw [h] at hc'; omega
      have hcC : c ≠ C := fun h => by rw [h] at hc'; omega
      rw [h0o c hcA hcL hcC]
      have := htame c (by omega)
      omega
  have ht : t'.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) t' K H hnK hKH
      (Or.inl ⟨by change (s₁ A).val = _; rw [h1A, h0A]; exact hpL,
        by change (s₁ R).val = _; rw [h1R, h0C]; exact hpAv⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo A R := hc
    rw [Grid.mem_cIoo, if_pos (by omega)] at hc'
    by_cases hcB : c = B
    · rw [hcB, h1B, h0R]
      omega
    · have hcA : c ≠ A := fun h => by rw [h] at hc'; omega
      have hcR : c ≠ R := fun h => by rw [h] at hc'; omega
      have hcL : c ≠ L := fun h => by rw [h] at hc'; omega
      have hcC : c ≠ C := fun h => by rw [h] at hc'; omega
      rw [h1o c hcB hcR hcC, h0o c hcA hcL hcC]
      have := htame c (by omega)
      omega
  have hf : f.IsEmpty := by
    apply seamSecondShort_isEmpty (n := n) f K H hnK hKH
      (Or.inr ⟨by change (s₂ L).val = _; rw [h2L, h1C, h0B]; exact hpBv,
        by change (s₂ B).val = _; rw [h2B, h1B, h0R]; exact hpR⟩)
    intro c hc
    have hc' : c ∈ Grid.cIoo L B := hc
    rw [Grid.mem_cIoo, if_neg (by omega)] at hc'
    by_cases hcA : c = A
    · rw [hcA, h2A, h1R, h0C]
      omega
    · have hcB : c ≠ B := fun h => by rw [h] at hc'; omega
      have hcR : c ≠ R := fun h => by rw [h] at hc'; omega
      have hcC : c ≠ C := fun h => by rw [h] at hc'; omega
      have hcL : c ≠ L := fun h => by rw [h] at hc'; omega
      rw [h2o c hcA hcR hcC hcL, h1o c hcB hcR hcC, h0o c hcA hcL hcC]
      have := htame c (by omega)
      omega
  have hne₀₁ : a₀ ≠ a₁ := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => (s.val.val R).val) h
    change (s₀ R).val = (s₁ R).val at hh
    rw [h0R, h1R, h0C] at hh
    omega
  have hne₁₂ : a₁ ≠ a₂ := by
    intro h
    have hh := congrArg (fun s : SeamMatchingSource n m => (s.val.val R).val) h
    change (s₁ R).val = (s₂ R).val at hh
    rw [h1R, h0C, h2R, h1A, h0A] at hh
    omega
  exact ⟨seamSecondShortPathTwo a₀ a₁ a₂ e he r hne₀₁ hr t' hne₁₂ ht f hf,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The explicit two-transition correction of a remaining rectangle at an interior last row. -/
theorem seamSecondShortInterior_exists (ρ : SeamSecondRemainingRectangle x z w)
    (h0 : x (Fin.last n) ≠ 0) (hl : x (Fin.last n) ≠ Fin.last n) :
    ∃ d : SeamCorrectionPath 2 (x, z) (x, w),
      d.2.2.1.val.left = seamRight n m ρ.val.left ∧
      d.2.2.1.val.right = seamLeft n m (x.toPerm.symm 0) ∧
      d.2.2.2.1.2.1.val.left = seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
      d.2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
      d.2.2.2.1.2.2.2.1.val.left = seamLeft n m (x.toPerm.symm 0) ∧
      d.2.2.2.1.2.2.2.1.val.right = seamRight n m ρ.val.right ∧
      d.2.2.2.2.val.left = seamRight n m ρ.val.left ∧
      d.2.2.2.2.val.right = seamLeft n m (x.toPerm.symm (Fin.last n)) := by
  obtain ⟨hn, hR, hRC, hCL, htop, hlt, hpR, hpL, hpC, htame, hlow, hq⟩ :=
    seamSecondShort_frame x z w ρ
  obtain ⟨hAn, hpA⟩ := seamSecondShort_pivot_value x z 0 h0
  obtain ⟨hBn, hpB⟩ := seamSecondShort_pivot_value x z (Fin.last n) hl
  have ht0 : 0 < (x (Fin.last n)).val := by
    have hne : (x (Fin.last n)).val ≠ 0 := fun h => h0 (Fin.ext h)
    omega
  have htn : (x (Fin.last n)).val < n := by
    have hne : (x (Fin.last n)).val ≠ n := fun h => hl (Fin.ext (by rw [h, Fin.val_last]))
    have hlt' := (x (Fin.last n)).isLt
    omega
  exact seamSecondShortInterior_exists_aux _ _ _ _ _ _ _ _ hn hAn hBn hR hRC hCL ht0 htn
    (by omega) (by omega) (by rw [hpA, seamLeft_val, Fin.val_zero])
    (by rw [hpB, seamLeft_val, Fin.val_last]) hpR hpL hpC htame hlow hq

end Construction

end OnLeConjecture.KnotFloer.GridFull
