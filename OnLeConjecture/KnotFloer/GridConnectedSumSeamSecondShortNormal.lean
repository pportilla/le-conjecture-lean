/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondShortFrame

/-!
# Normal form of two-transition corrections with equal first factors

Consider a two-transition correction from `seamState x z` to `seamState x w`,
with matching sources `a₀, a₁, a₂`, entry `e`, birth `r`, death `t` and exit
`f`. Let `P < Q` be the southwest columns of `a₀`, let `A` be its northeast
column, and put `G = r.left` and `D = r.right`. The death has sides `(A, D)`,
since a death with sides `(G, D)` would change the first factor at `G`.
Emptiness then forces the entry sides `(Q, A)` and the exit sides `(Q, G)`.
The retained endpoints differ exactly by exchanging the columns `Q` and `D`.

Emptiness further forces the retained source rows at `A` and `G` to be `0`
and `n`, and the last first-factor row lies strictly between them. The
second-factor projection of the exchange of `Q` and `D` is a remaining
rectangle whose embedded side columns are `Q` and `D`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The matching target swaps the two selected southwest columns. -/
theorem seamSecondShort_partner_apply (s : SeamComplement n m) (c : Fin (n + m + 1)) :
    (seamComplementPartner s).val c =
      s.val (Equiv.swap (seamComplementFirst s) (seamComplementSecond s) c) := by
  change s.val.swapColumns _ _ c = _
  rw [GridState.swapColumns_apply]

private theorem mem_cIoo_inc {k : ℕ} {a b c : Fin k} (h₁ : a.val < c.val) (h₂ : c.val < b.val) :
    c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_pos (by omega)]
  exact ⟨fun h => by rw [h] at h₁; omega, h₁, h₂⟩

private theorem mem_cIoo_wrap {k : ℕ} {a b c : Fin k} (hba : b.val < a.val)
    (h : a.val < c.val ∨ c.val < b.val) : c ∈ Grid.cIoo a b := by
  rw [Grid.mem_cIoo, if_neg (by omega)]
  exact ⟨fun h' => by rw [h'] at hba; omega, h⟩

private theorem false_of_mem {k : ℕ} {u v : GridState k} (R : GridRectangleBetween u v)
    (hR : R.IsEmpty) (c : Fin k) (hc : c ∈ Grid.cIoo R.left R.right)
    (hv : u c ∈ Grid.cIoo (u R.left) (u R.right)) : False :=
  (isEmpty_iff_forall_notMem_cIoo R).mp hR c hc hv

/-- Two retained states with the same first factor agree on the first block. -/
theorem seamSecondShort_firstBlock_eq (x : GridState (n + 1)) (z w : GridState (m + 1))
    (c : Fin (n + m + 1)) (hc : c.val < n) : seamState x z c = seamState x w c := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n, c = seamLeft n m a.castSucc := ⟨⟨c.val, hc⟩, Fin.ext rfl⟩
  rw [seamState_left_castSucc, seamState_left_castSucc]

section Normal
variable {x : GridState (n + 1)} {z w : GridState (m + 1)}

/-- Normal form of a two-transition correction with equal first factors. -/
theorem seamSecondShortTwo_normal (a₀ a₁ a₂ : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState x z) (seamComplementPartner a₀.val).val)
    (r : GridRectangleBetween a₀.val.val (seamComplementPartner a₁.val).val)
    (t : GridRectangleBetween a₁.val.val (seamComplementPartner a₂.val).val)
    (f : GridRectangleBetween a₂.val.val (seamState x w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns a₁.val.val).card = 2) :
    x (Fin.last n) ≠ 0 ∧ x (Fin.last n) ≠ Fin.last n ∧
    ∃ ρ : SeamSecondRemainingRectangle x z w,
      e.left = seamRight n m ρ.val.left ∧ e.right = seamLeft n m (x.toPerm.symm 0) ∧
      r.left = seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
      r.right = seamRight n m ρ.val.right ∧
      t.left = seamLeft n m (x.toPerm.symm 0) ∧ t.right = seamRight n m ρ.val.right ∧
      f.left = seamRight n m ρ.val.left ∧
      f.right = seamLeft n m (x.toPerm.symm (Fin.last n)) := by
  classical
  -- Counts and the birth/death column structure.
  have hNE₀ := seamMatchingEntry_northeast_card (x, z) a₀ e
  have hNE₂ := seamMatchingExit_northeast_card (x, w) a₂ f
  have hb : (seamNortheastColumns a₁.val.val).card =
      (seamNortheastColumns a₀.val.val).card + 1 := by omega
  have hd : (seamNortheastColumns a₁.val.val).card =
      (seamNortheastColumns a₂.val.val).card + 1 := by omega
  have hx := seamMatchingEntry_southwest_card (x, z) a₀ e
  have hor := seamTwoStep_birth_death_nonwrap a₀ a₁ a₂ r t hr ht hb hd hx
  obtain ⟨hDt, hf₁, hs₁, hf₂, hs₂, -, -⟩ :=
    seamTwoStep_birth_death_columns a₀ a₁ a₂ r t hr ht hb hd hx
  have hBn := seamMatchingBirth_nonwrap a₀ a₁ r hr hb hor.1
  have hDn : n ≤ r.right.val := hBn.1
  have hDP : r.right.val < (seamComplementFirst a₀.val).val := hBn.2.1
  have hrr : (a₀.val.val r.left).val ≤ n ∧ n < (a₀.val.val r.right).val := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact ⟨h.2.2.1, h.2.2.2⟩
    · omega
  have htr : n < (a₁.val.val t.left).val := by
    rcases seamMatchingDeath_ranges t hd with h | h
    · exact h.2.2.2
    · rw [← hDt] at h
      omega
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a₀.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a₀.val)
  have hPQ : (seamComplementFirst a₀.val).val < (seamComplementSecond a₀.val).val :=
    seamComplementFirst_lt_second a₀.val
  have hab : (a₀.val.val (seamComplementFirst a₀.val)).val <
      (a₀.val.val (seamComplementSecond a₀.val)).val := a₀.property
  have hab₂ : (a₂.val.val (seamComplementFirst a₂.val)).val <
      (a₂.val.val (seamComplementSecond a₂.val)).val := a₂.property
  rw [hf₂, hs₂] at hab₂
  have hGn : r.left.val < n := hor.1
  have hBtn : t.left.val < n := hor.2
  have hn : 0 < n := by omega
  -- Distinctness of the relevant columns.
  have hGD : r.left ≠ r.right := r.left_ne_right
  have hGP : r.left ≠ seamComplementFirst a₀.val := fun h => by rw [h] at hGn; omega
  have hGQ : r.left ≠ seamComplementSecond a₀.val := fun h => by rw [h] at hGn; omega
  have hDP' : r.right ≠ seamComplementFirst a₀.val := fun h => by rw [h] at hDP; omega
  have hDQ : r.right ≠ seamComplementSecond a₀.val := fun h => by rw [h] at hDP; omega
  have hPQ' : seamComplementFirst a₀.val ≠ seamComplementSecond a₀.val :=
    seamComplementFirst_ne_second a₀.val
  have hBtD : t.left ≠ r.right := by rw [hDt]; exact t.left_ne_right
  have hBtP : t.left ≠ seamComplementFirst a₀.val := fun h => by rw [h] at hBtn; omega
  have hBtQ : t.left ≠ seamComplementSecond a₀.val := fun h => by rw [h] at hBtn; omega
  -- Values of the middle and final matching sources.
  have hpart₀ (c : Fin (n + m + 1)) : (seamComplementPartner a₀.val).val c =
      a₀.val.val (Equiv.swap (seamComplementFirst a₀.val) (seamComplementSecond a₀.val) c) :=
    seamSecondShort_partner_apply a₀.val c
  have hpart₁ (c : Fin (n + m + 1)) : (seamComplementPartner a₁.val).val c =
      a₁.val.val (Equiv.swap r.right (seamComplementFirst a₀.val) c) := by
    rw [seamSecondShort_partner_apply, hf₁, hs₁]
  have hpart₂ (c : Fin (n + m + 1)) : (seamComplementPartner a₂.val).val c =
      a₂.val.val (Equiv.swap (seamComplementFirst a₀.val) (seamComplementSecond a₀.val) c) := by
    rw [seamSecondShort_partner_apply, hf₂, hs₂]
  have h1G : a₁.val.val r.left = a₀.val.val r.right := by
    have h := r.map_left
    rw [hpart₁, Equiv.swap_apply_of_ne_of_ne hGD hGP] at h
    exact h
  have h1P : a₁.val.val (seamComplementFirst a₀.val) = a₀.val.val r.left := by
    have h := r.map_right
    rw [hpart₁, Equiv.swap_apply_left] at h
    exact h
  have h1D : a₁.val.val r.right = a₀.val.val (seamComplementFirst a₀.val) := by
    have h := r.map_of_ne (seamComplementFirst a₀.val) hGP.symm hDP'.symm
    rw [hpart₁, Equiv.swap_apply_right] at h
    exact h
  have h1o (c : Fin (n + m + 1)) (hcG : c ≠ r.left) (hcD : c ≠ r.right)
      (hcP : c ≠ seamComplementFirst a₀.val) : a₁.val.val c = a₀.val.val c := by
    have h := r.map_of_ne c hcG hcD
    rw [hpart₁, Equiv.swap_apply_of_ne_of_ne hcD hcP] at h
    exact h
  have h2Bt : a₂.val.val t.left = a₁.val.val r.right := by
    have h := t.map_left
    rw [hpart₂, Equiv.swap_apply_of_ne_of_ne hBtP hBtQ, ← hDt] at h
    exact h
  have h2D : a₂.val.val r.right = a₁.val.val t.left := by
    have h := t.map_right
    rw [hpart₂, ← hDt, Equiv.swap_apply_of_ne_of_ne hDP' hDQ] at h
    exact h
  have h2Q : a₂.val.val (seamComplementSecond a₀.val) =
      a₁.val.val (seamComplementFirst a₀.val) := by
    have h := t.map_of_ne (seamComplementFirst a₀.val) hBtP.symm
      (by rw [← hDt]; exact hDP'.symm)
    rw [hpart₂, Equiv.swap_apply_left] at h
    exact h
  have h2P : a₂.val.val (seamComplementFirst a₀.val) =
      a₁.val.val (seamComplementSecond a₀.val) := by
    have h := t.map_of_ne (seamComplementSecond a₀.val) hBtQ.symm
      (by rw [← hDt]; exact hDQ.symm)
    rw [hpart₂, Equiv.swap_apply_right] at h
    exact h
  have h2o (c : Fin (n + m + 1)) (hcB : c ≠ t.left) (hcD : c ≠ r.right)
      (hcP : c ≠ seamComplementFirst a₀.val) (hcQ : c ≠ seamComplementSecond a₀.val) :
      a₂.val.val c = a₁.val.val c := by
    have h := t.map_of_ne c hcB (by rw [← hDt]; exact hcD)
    rw [hpart₂, Equiv.swap_apply_of_ne_of_ne hcP hcQ] at h
    exact h
  -- The northeast columns of the entry and exit sources.
  have hNEs := seamMatchingEntry_northeast_eq_singleton (x, z) a₀ e
  obtain ⟨A, hAdef⟩ : ∃ A, (if e.left.val < n then e.left else e.right) = A := ⟨_, rfl⟩
  rw [hAdef] at hNEs
  have hA : A.val < n ∧ n < (a₀.val.val A).val :=
    (mem_seamNortheastColumns _ _).mp (by rw [hNEs]; exact Finset.mem_singleton_self A)
  have hEcases : (e.left = A ∧ e.right = seamComplementFirst a₀.val) ∨
      (e.left = seamComplementSecond a₀.val ∧ e.right = A) := by
    rcases seamMatchingEntry_endpoints (x, z) a₀ e he with h | h
    · left
      rw [if_pos h.1] at hAdef
      exact ⟨hAdef, h.2.1⟩
    · right
      rw [if_neg (by rw [h.2.1]; omega)] at hAdef
      exact ⟨h.2.1, hAdef⟩
  have hNEs₂ := seamMatchingExit_northeast_eq_singleton (x, w) a₂ f
  obtain ⟨E, hEdef⟩ : ∃ E, (if f.left.val < n then f.left else f.right) = E := ⟨_, rfl⟩
  rw [hEdef] at hNEs₂
  have hFcases : (f.left = E ∧ f.right = seamComplementFirst a₀.val) ∨
      (f.left = seamComplementSecond a₀.val ∧ f.right = E) := by
    rcases seamMatchingExit_endpoints (x, w) a₂ f hf with h | h
    · left
      rw [if_pos h.1] at hEdef
      exact ⟨hEdef, h.2.1.trans hf₂⟩
    · right
      rw [if_neg (by rw [h.2.1, hs₂]; omega)] at hEdef
      exact ⟨h.2.1.trans hs₂, hEdef⟩
  -- The death removes the old northeast column.
  have hBtA : t.left = A := by
    have hAG_or : t.left = A ∨ t.left = r.left := by
      by_cases hBG : t.left = r.left
      · exact Or.inr hBG
      · left
        have hv : a₁.val.val t.left = a₀.val.val t.left := h1o t.left hBG hBtD hBtP
        have hm : t.left ∈ seamNortheastColumns a₀.val.val :=
          (mem_seamNortheastColumns _ _).mpr ⟨hBtn, by rw [← hv]; exact htr⟩
        rw [hNEs] at hm
        exact Finset.mem_singleton.mp hm
    rcases hAG_or with h | h
    · exact h
    exfalso
    have hGA : r.left ≠ A := fun hh => by rw [hh] at hrr; omega
    have hGeL : r.left ≠ e.left := by
      rcases hEcases with hh | hh
      · rw [hh.1]; exact hGA
      · rw [hh.1]; exact hGQ
    have hGeR : r.left ≠ e.right := by
      rcases hEcases with hh | hh
      · rw [hh.2]; exact hGP
      · rw [hh.2]; exact hGA
    have hpG : seamState x z r.left = a₀.val.val r.left := by
      have hh := e.map_of_ne r.left hGeL hGeR
      rw [hpart₀, Equiv.swap_apply_of_ne_of_ne hGP hGQ] at hh
      exact hh.symm
    have h2G : a₂.val.val r.left = a₀.val.val (seamComplementFirst a₀.val) := by
      rw [← h, h2Bt, h1D]
    have hGE : r.left ≠ E := by
      intro hh
      have hm : E ∈ seamNortheastColumns a₂.val.val := by
        rw [hNEs₂]
        exact Finset.mem_singleton_self E
      rw [← hh, mem_seamNortheastColumns, h2G] at hm
      omega
    have hGfL : r.left ≠ f.left := by
      rcases hFcases with hh | hh
      · rw [hh.1]; exact hGE
      · rw [hh.1]; exact hGQ
    have hGfR : r.left ≠ f.right := by
      rcases hFcases with hh | hh
      · rw [hh.2]; exact hGP
      · rw [hh.2]; exact hGE
    have hqG : seamState x w r.left = a₂.val.val r.left := f.map_of_ne r.left hGfL hGfR
    have hh := seamSecondShort_firstBlock_eq x z w r.left hGn
    rw [hpG, hqG, h2G] at hh
    exact hGP (a₀.val.val.toPerm.injective hh)
  subst hBtA
  have hAG : t.left ≠ r.left := fun hh => by rw [hh] at hA; omega
  have h1A : a₁.val.val t.left = a₀.val.val t.left := h1o t.left hAG hBtD hBtP
  have h2A : a₂.val.val t.left = a₀.val.val (seamComplementFirst a₀.val) := h2Bt.trans h1D
  have h2D' : a₂.val.val r.right = a₀.val.val t.left := h2D.trans h1A
  have h2G : a₂.val.val r.left = a₀.val.val r.right :=
    (h2o r.left hAG.symm hGD hGP hGQ).trans h1G
  have h2Q' : a₂.val.val (seamComplementSecond a₀.val) = a₀.val.val r.left := h2Q.trans h1P
  have h2P' : a₂.val.val (seamComplementFirst a₀.val) =
      a₀.val.val (seamComplementSecond a₀.val) :=
    h2P.trans (h1o _ hGQ.symm hDQ.symm hPQ'.symm)
  have hbc : (a₀.val.val (seamComplementSecond a₀.val)).val < (a₀.val.val r.left).val := by
    rw [h2P', h2Q'] at hab₂
    exact hab₂
  -- The high row at the birth column is below the high row at the northeast column.
  have hKH : (a₀.val.val r.right).val < (a₀.val.val t.left).val := by
    have hne : (a₀.val.val r.right).val ≠ (a₀.val.val t.left).val := fun hh =>
      hBtD (a₀.val.val.toPerm.injective (Fin.ext hh)).symm
    by_contra hlt
    rcases lt_or_gt_of_ne (show r.left.val ≠ t.left.val from fun hh => hAG (Fin.ext hh).symm)
      with hGA | hGA
    · apply false_of_mem r hr t.left (mem_cIoo_inc hGA (by omega))
      exact mem_cIoo_inc (by omega) (by omega)
    · apply false_of_mem t ht r.left (by rw [← hDt]; exact mem_cIoo_inc hGA (by omega))
      rw [← hDt, h1G, h1A, h1D]
      exact mem_cIoo_wrap (by omega) (Or.inl (by omega))
  -- The entry has sides `(Q, A)`.
  have hEside : e.left = seamComplementSecond a₀.val ∧ e.right = t.left := by
    rcases hEcases with hh | hh
    · exfalso
      have hpD : seamState x z r.right = a₀.val.val r.right := by
        have h := e.map_of_ne r.right (by rw [hh.1]; exact hBtD.symm) (by rw [hh.2]; exact hDP')
        rw [hpart₀, Equiv.swap_apply_of_ne_of_ne hDP' hDQ] at h
        exact h.symm
      have hpA : seamState x z t.left = a₀.val.val (seamComplementSecond a₀.val) := by
        have h := e.map_right
        rw [hh.2, hh.1, hpart₀, Equiv.swap_apply_left] at h
        exact h.symm
      have hpP : seamState x z (seamComplementFirst a₀.val) = a₀.val.val t.left := by
        have h := e.map_left
        rw [hh.1, hh.2, hpart₀, Equiv.swap_apply_of_ne_of_ne hBtP hBtQ] at h
        exact h.symm
      apply false_of_mem e he r.right (by rw [hh.1, hh.2]; exact mem_cIoo_inc (by omega) hDP)
      rw [hpD, hh.1, hh.2, hpA, hpP]
      exact mem_cIoo_inc (by omega) (by omega)
    · exact hh
  -- The exit has sides `(Q, G)`.
  have hEG : E = r.left := by
    have hm : r.left ∈ seamNortheastColumns a₂.val.val :=
      (mem_seamNortheastColumns _ _).mpr ⟨hGn, by rw [h2G]; omega⟩
    rw [hNEs₂] at hm
    exact (Finset.mem_singleton.mp hm).symm
  have hFside : f.left = seamComplementSecond a₀.val ∧ f.right = r.left := by
    rw [hEG] at hFcases
    rcases hFcases with hh | hh
    · exfalso
      apply false_of_mem f hf r.right (by rw [hh.1, hh.2]; exact mem_cIoo_inc (by omega) hDP)
      rw [hh.1, hh.2, h2D', h2G, h2P']
      exact mem_cIoo_wrap (by omega) (Or.inl hKH)
    · exact hh
  -- Retained source and target values.
  have hpA : seamState x z t.left = a₀.val.val (seamComplementFirst a₀.val) := by
    have h := e.map_left
    rw [hEside.1, hEside.2, hpart₀, Equiv.swap_apply_right] at h
    exact h.symm
  have hpQ : seamState x z (seamComplementSecond a₀.val) = a₀.val.val t.left := by
    have h := e.map_right
    rw [hEside.2, hEside.1, hpart₀, Equiv.swap_apply_of_ne_of_ne hBtP hBtQ] at h
    exact h.symm
  have hpo (c : Fin (n + m + 1)) (hcA : c ≠ t.left) (hcP : c ≠ seamComplementFirst a₀.val)
      (hcQ : c ≠ seamComplementSecond a₀.val) : seamState x z c = a₀.val.val c := by
    have h := e.map_of_ne c (by rw [hEside.1]; exact hcQ) (by rw [hEside.2]; exact hcA)
    rw [hpart₀, Equiv.swap_apply_of_ne_of_ne hcP hcQ] at h
    exact h.symm
  have hpP : seamState x z (seamComplementFirst a₀.val) =
      a₀.val.val (seamComplementSecond a₀.val) := by
    have h := e.map_of_ne (seamComplementFirst a₀.val) (by rw [hEside.1]; exact hPQ')
      (by rw [hEside.2]; exact hBtP.symm)
    rw [hpart₀, Equiv.swap_apply_left] at h
    exact h.symm
  have hpG : seamState x z r.left = a₀.val.val r.left := hpo r.left hAG.symm hGP hGQ
  have hpD : seamState x z r.right = a₀.val.val r.right := hpo r.right hBtD.symm hDP' hDQ
  have hqQ : seamState x w (seamComplementSecond a₀.val) = a₀.val.val r.right := by
    have h := f.map_left
    rw [hFside.1, hFside.2, h2G] at h
    exact h
  have hqG : seamState x w r.left = a₀.val.val r.left := by
    have h := f.map_right
    rw [hFside.2, hFside.1, h2Q'] at h
    exact h
  have hqo (c : Fin (n + m + 1)) (hcQ : c ≠ seamComplementSecond a₀.val) (hcG : c ≠ r.left) :
      seamState x w c = a₂.val.val c :=
    f.map_of_ne c (by rw [hFside.1]; exact hcQ) (by rw [hFside.2]; exact hcG)
  -- The last first-factor row is the low row at `P`.
  have hxl : seamState x z (seamComplementFirst a₀.val) = seamLeft n m (x (Fin.last n)) :=
    seamSecondOneStep_retained_low_row x z _ hP.1 (by rw [hpP]; exact hQ.2)
  have hxlv : (x (Fin.last n)).val = (a₀.val.val (seamComplementSecond a₀.val)).val := by
    have hh := congrArg Fin.val hxl
    rw [hpP, seamLeft_val] at hh
    exact hh.symm
  have hlowP : ∀ c : Fin (n + m + 1), n ≤ c.val → (seamState x z c).val ≤ n →
      c = seamComplementFirst a₀.val := fun c hc hv =>
    (seamSecondShort_source_low x z c hc hv).trans
      (seamSecondShort_source_low x z _ hP.1 (by rw [hpP]; exact hQ.2)).symm
  -- The low row at the northeast column is zero.
  have ha0 : (a₀.val.val (seamComplementFirst a₀.val)).val = 0 := by
    by_contra ha0
    obtain ⟨V, hV⟩ : ∃ V, seamState x z V = seamLeft n m 0 :=
      ⟨(seamState x z).toPerm.symm (seamLeft n m 0), (seamState x z).toPerm.apply_symm_apply _⟩
    have hVv : (seamState x z V).val = 0 := by rw [hV, seamLeft_val, Fin.val_zero]
    have hVn : V.val < n := by
      by_contra hh
      have hVP := hlowP V (by omega) (by omega)
      rw [hVP, hpP] at hVv
      omega
    have hVA : V ≠ t.left := fun hh => by rw [hh, hpA] at hVv; omega
    have hVG : V ≠ r.left := fun hh => by rw [hh, hpG] at hVv; omega
    have hVP : V ≠ seamComplementFirst a₀.val := fun hh => by rw [hh] at hVn; omega
    have hVQ : V ≠ seamComplementSecond a₀.val := fun hh => by rw [hh] at hVn; omega
    have hVD : V ≠ r.right := fun hh => by rw [hh] at hVn; omega
    have h0V : a₀.val.val V = seamState x z V := (hpo V hVA hVP hVQ).symm
    have h1V : a₁.val.val V = a₀.val.val V := h1o V hVG hVD hVP
    rcases lt_or_gt_of_ne (show V.val ≠ t.left.val from fun hh => hVA (Fin.ext hh)) with hlt | hlt
    · apply false_of_mem e he V
        (by rw [hEside.1, hEside.2]; exact mem_cIoo_wrap (by omega) (Or.inr hlt))
      rw [hEside.1, hEside.2, hpQ, hpA]
      exact mem_cIoo_wrap (by omega) (Or.inr (by omega))
    · apply false_of_mem t ht V (by rw [← hDt]; exact mem_cIoo_inc hlt (by omega))
      rw [← hDt, h1V, h0V, h1A, h1D]
      exact mem_cIoo_wrap (by omega) (Or.inr (by omega))
  -- The low row at the birth column is `n`.
  have hcn : (a₀.val.val r.left).val = n := by
    by_contra hcn
    obtain ⟨V, hV⟩ : ∃ V, seamState x z V = seamLeft n m (Fin.last n) :=
      ⟨(seamState x z).toPerm.symm (seamLeft n m (Fin.last n)),
        (seamState x z).toPerm.apply_symm_apply _⟩
    have hVv : (seamState x z V).val = n := by rw [hV, seamLeft_val, Fin.val_last]
    have hVn : V.val < n := by
      by_contra hh
      have hVP := hlowP V (by omega) (by omega)
      rw [hVP, hpP] at hVv
      omega
    have hVA : V ≠ t.left := fun hh => by rw [hh, hpA] at hVv; omega
    have hVG : V ≠ r.left := fun hh => by rw [hh, hpG] at hVv; omega
    have hVP : V ≠ seamComplementFirst a₀.val := fun hh => by rw [hh] at hVn; omega
    have hVQ : V ≠ seamComplementSecond a₀.val := fun hh => by rw [hh] at hVn; omega
    have hVD : V ≠ r.right := fun hh => by rw [hh] at hVn; omega
    have h0V : a₀.val.val V = seamState x z V := (hpo V hVA hVP hVQ).symm
    have h1V : a₁.val.val V = a₀.val.val V := h1o V hVG hVD hVP
    have h2V : a₂.val.val V = a₁.val.val V := h2o V hVA hVD hVP hVQ
    rcases lt_or_gt_of_ne (show V.val ≠ r.left.val from fun hh => hVG (Fin.ext hh)) with hlt | hlt
    · apply false_of_mem f hf V
        (by rw [hFside.1, hFside.2]; exact mem_cIoo_wrap (by omega) (Or.inr hlt))
      rw [hFside.1, hFside.2, h2V, h1V, h0V, h2Q', h2G]
      exact mem_cIoo_inc (by omega) (by omega)
    · apply false_of_mem r hr V (mem_cIoo_inc hlt (by omega))
      rw [h0V]
      exact mem_cIoo_inc (by omega) (by omega)
  -- The last first-factor row is interior.
  have hx0 : x (Fin.last n) ≠ 0 := fun hh => by
    rw [hh, Fin.val_zero] at hxlv
    omega
  have hxn : x (Fin.last n) ≠ Fin.last n := fun hh => by
    rw [hh, Fin.val_last] at hxlv
    omega
  have hAeq : t.left = seamLeft n m (x.toPerm.symm 0) :=
    seamImmediateSecond_pivot_of_value x z t.left hBtn 0
      (by rw [hpA]; exact Fin.ext (by rw [seamLeft_val, Fin.val_zero]; exact ha0))
  have hGeq : r.left = seamLeft n m (x.toPerm.symm (Fin.last n)) :=
    seamImmediateSecond_pivot_of_value x z r.left hGn (Fin.last n)
      (by rw [hpG]; exact Fin.ext (by rw [seamLeft_val, Fin.val_last]; exact hcn))
  -- The retained endpoints differ by the exchange of `Q` and `D`.
  have hqswap : seamState x w =
      (seamState x z).swapColumns (seamComplementSecond a₀.val) r.right := by
    apply GridState.ext
    intro c
    rw [GridState.swapColumns_apply]
    by_cases hcQ : c = seamComplementSecond a₀.val
    · rw [hcQ, Equiv.swap_apply_left, hqQ, hpD]
    by_cases hcD : c = r.right
    · rw [hcD, Equiv.swap_apply_right, hpQ, hqo r.right hDQ hGD.symm, h2D']
    by_cases hcA : c = t.left
    · rw [hcA, Equiv.swap_apply_of_ne_of_ne hBtQ hBtD, hpA, hqo t.left hBtQ hAG, h2A]
    by_cases hcG : c = r.left
    · rw [hcG, Equiv.swap_apply_of_ne_of_ne hGQ hGD, hqG, hpG]
    by_cases hcP : c = seamComplementFirst a₀.val
    · rw [hcP, Equiv.swap_apply_of_ne_of_ne hPQ' hDP'.symm, hpP, hqo _ hPQ' hGP.symm, h2P']
    rw [Equiv.swap_apply_of_ne_of_ne hcQ hcD, hpo c hcA hcP hcQ, hqo c hcQ hcG,
      h2o c hcA hcD hcP hcQ, h1o c hcG hcD hcP]
  -- The second-factor projection of this exchange.
  let F := seamSecondShortRect (u := seamState x z) (v := seamState x w)
    (seamComplementSecond a₀.val) r.right hDQ.symm hqswap
  let ρ₀ := seamRetainedSecondRectangle (x, z) (x, w) F hQ.1 hDn
  have hρL : seamRight n m ρ₀.left = seamComplementSecond a₀.val :=
    seamRight_secondFactorIndex _ hQ.1
  have hρR : seamRight n m ρ₀.right = r.right := seamRight_secondFactorIndex _ hDn
  have hbot : seamSecondFactorRow x ρ₀.bottom = seamState x z (seamComplementSecond a₀.val) :=
    seamRetainedSecondRectangle_bottom_recovery (x, z) (x, w) F hQ.1 hDn
  have htopr : seamSecondFactorRow x ρ₀.top = seamState x z r.right :=
    seamRetainedSecondRectangle_top_recovery (x, z) (x, w) F hQ.1 hDn
  have hxlast := (x (Fin.last n)).isLt
  have hρtop : n + ρ₀.top.val = (a₀.val.val r.right).val := by
    by_cases h0 : ρ₀.top = 0
    · exfalso
      rw [h0, seamSecondFactorRow_zero, hpD] at htopr
      have hh := congrArg Fin.val htopr
      rw [seamLeft_val] at hh
      omega
    · rw [seamSecondFactorRow_of_ne_zero x _ h0, hpD] at htopr
      have hh := congrArg Fin.val htopr
      rw [seamRight_val] at hh
      exact hh
  have hρbot : n + ρ₀.bottom.val = (a₀.val.val t.left).val := by
    by_cases h0 : ρ₀.bottom = 0
    · exfalso
      rw [h0, seamSecondFactorRow_zero, hpQ] at hbot
      have hh := congrArg Fin.val hbot
      rw [seamLeft_val] at hh
      omega
    · rw [seamSecondFactorRow_of_ne_zero x _ h0, hpQ] at hbot
      have hh := congrArg Fin.val hbot
      rw [seamRight_val] at hh
      exact hh
  have hcol : ρ₀.right < ρ₀.left := by
    have h1 := congrArg Fin.val hρL
    have h2 := congrArg Fin.val hρR
    rw [seamRight_val] at h1 h2
    exact Fin.lt_def.mpr (by omega)
  have hρe : ρ₀.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo _).mpr
    intro d hd hrow
    have hcolV : seamRight n m d ∈ Grid.cIoo (seamComplementSecond a₀.val) r.right := by
      rw [← hρL, ← hρR, seamRight_mem_cIoo_iff]
      exact hd
    have hrowV : seamState x z (seamRight n m d) ∈
        Grid.cIoo (seamState x z (seamComplementSecond a₀.val)) (seamState x z r.right) := by
      rw [seamState_secondFactorRow, ← hbot, ← htopr, seamSecondFactorRow_mem_cIoo_iff]
      exact hrow
    have hVn : n ≤ (seamRight n m d).val := by rw [seamRight_val]; omega
    generalize seamRight n m d = V at hcolV hrowV hVn
    rw [Grid.mem_cIoo, if_neg (by omega)] at hcolV
    have hcolV := hcolV.2
    rw [hpQ, hpD, Grid.mem_cIoo, if_neg (by omega)] at hrowV
    have hrowV := hrowV.2
    have hVA : V ≠ t.left := fun hh => by rw [hh] at hVn; omega
    have hVG : V ≠ r.left := fun hh => by rw [hh] at hVn; omega
    have hVP : V ≠ seamComplementFirst a₀.val := fun hh => by rw [hh] at hcolV; omega
    have hVQ : V ≠ seamComplementSecond a₀.val := fun hh => by rw [hh] at hcolV; omega
    have hVD : V ≠ r.right := fun hh => by rw [hh] at hcolV; omega
    have hhigh : n < (seamState x z V).val := by
      by_contra hh
      exact hVP (hlowP V hVn (by omega))
    have h0V : a₀.val.val V = seamState x z V := (hpo V hVA hVP hVQ).symm
    have h1V : a₁.val.val V = a₀.val.val V := h1o V hVG hVD hVP
    have h2V : a₂.val.val V = a₁.val.val V := h2o V hVA hVD hVP hVQ
    rcases hcolV with hQV | hVDlt
    · rcases hrowV with hHV | hVK
      · apply false_of_mem e he V
          (by rw [hEside.1, hEside.2]; exact mem_cIoo_wrap (by omega) (Or.inl hQV))
        rw [hEside.1, hEside.2, hpQ, hpA]
        exact mem_cIoo_wrap (by omega) (Or.inl hHV)
      · apply false_of_mem f hf V
          (by rw [hFside.1, hFside.2]; exact mem_cIoo_wrap (by omega) (Or.inl hQV))
        rw [hFside.1, hFside.2, h2V, h1V, h0V, h2Q', h2G]
        exact mem_cIoo_inc (by omega) hVK
    · rcases hrowV with hHV | hVK
      · apply false_of_mem t ht V (by rw [← hDt]; exact mem_cIoo_inc (by omega) hVDlt)
        rw [← hDt, h1V, h0V, h1A, h1D]
        exact mem_cIoo_wrap (by omega) (Or.inl hHV)
      · apply false_of_mem r hr V (mem_cIoo_inc (by omega) hVDlt)
        rw [h0V]
        exact mem_cIoo_inc (by omega) hVK
  have hmem := seamSecondRemaining_of_rows x ρ₀ hρe hn hcol (by omega) (by omega)
  refine ⟨hx0, hxn, ⟨ρ₀, hmem⟩, ?_, ?_, hGeq, hρR.symm, hAeq, ?_, ?_, ?_⟩
  · exact hEside.1.trans hρL.symm
  · exact hEside.2.trans hAeq
  · exact hDt.symm.trans hρR.symm
  · exact hFside.1.trans hρL.symm
  · exact hFside.2.trans hGeq

end Normal

end OnLeConjecture.KnotFloer.GridFull
