/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ExteriorSignedWordGridPositive
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationMatching

/-! # The horizontal matching of a signed word

For a signed word `v`, the matching `SignedGrid.sM v` sends each outgoing corner to the incoming
corner of the same height where its horizontal arc ends. It is obtained from the matching of the
positive word `SignedGrid.base v` of the indices of `v` by renaming the corners of the negative
letters (`SignedGrid.tauOut`, `SignedGrid.tauIn`): the outgoing corners `1, 2` and the incoming
corners `0, 1` of a negative letter are exchanged.

Main results:
* `SignedGrid.sM_height`: the arc keeps its height.
* `SignedGrid.sM_spec`: an integer arc ends at the next occurrence of its rank, cyclically.
* `SignedGrid.sM_symm_min`: the arc entering a corner starts at the nearest outgoing corner of
  the same height on its left, cyclically, which is the defining condition of
  `IsSignedWordGrid`.
* `SignedGrid.isSignedWordGrid_iff`: a grid is a signed word grid if and only if its `O` rows are
  ordered by height and the `X` marking of each column lies in the row of the arc entering it.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti

variable {m : ℕ}

/-! ### The underlying positive word -/

/-- The positive word of the indices of a signed word. -/
def base (v : SignedAdjacentWord m) : PositiveAdjacentWord m := v.map Prod.fst

theorem base_length (v : SignedAdjacentWord m) : (base v).length = v.length := List.length_map _

theorem base_getElem (v : SignedAdjacentWord m) {k : ℕ} (hk : k < (base v).length) :
    (base v)[k] = (v[k]'(by rw [← base_length]; exact hk)).1 := List.getElem_map _

/-- The corners of `v` as corners of `base v`. -/
def cc (v : SignedAdjacentWord m) : Fin v.length × Fin 3 ≃ Fin (base v).length × Fin 3 :=
  (finCongr (base_length v).symm).prodCongr (Equiv.refl _)

@[simp] theorem cc_fst_val (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    ((cc v p).1).val = p.1.val := rfl

@[simp] theorem cc_snd (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    (cc v p).2 = p.2 := rfl

@[simp] theorem cc_symm_fst_val (v : SignedAdjacentWord m) (p : Fin (base v).length × Fin 3) :
    (((cc v).symm p).1).val = p.1.val := rfl

@[simp] theorem cc_symm_snd (v : SignedAdjacentWord m) (p : Fin (base v).length × Fin 3) :
    ((cc v).symm p).2 = p.2 := rfl

/-- Renaming of the outgoing corners of the negative letters. -/
def tauOut (v : SignedAdjacentWord m) : Equiv.Perm (Fin v.length × Fin 3) where
  toFun p := (p.1, if v[p.1.val].2 = 1 then p.2 else Equiv.swap 1 2 p.2)
  invFun p := (p.1, if v[p.1.val].2 = 1 then p.2 else Equiv.swap 1 2 p.2)
  left_inv p := by
    rcases p with ⟨h, c⟩
    by_cases hs : v[h.val].2 = 1 <;> simp [hs]
  right_inv p := by
    rcases p with ⟨h, c⟩
    by_cases hs : v[h.val].2 = 1 <;> simp [hs]

/-- Renaming of the incoming corners of the negative letters. -/
def tauIn (v : SignedAdjacentWord m) : Equiv.Perm (Fin v.length × Fin 3) where
  toFun p := (p.1, if v[p.1.val].2 = 1 then p.2 else Equiv.swap 0 1 p.2)
  invFun p := (p.1, if v[p.1.val].2 = 1 then p.2 else Equiv.swap 0 1 p.2)
  left_inv p := by
    rcases p with ⟨h, c⟩
    by_cases hs : v[h.val].2 = 1 <;> simp [hs]
  right_inv p := by
    rcases p with ⟨h, c⟩
    by_cases hs : v[h.val].2 = 1 <;> simp [hs]

@[simp] theorem tauOut_fst (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    (tauOut v p).1 = p.1 := rfl

@[simp] theorem tauIn_fst (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    (tauIn v p).1 = p.1 := rfl

theorem tauOut_symm (v : SignedAdjacentWord m) : (tauOut v).symm = tauOut v := rfl

theorem tauIn_symm (v : SignedAdjacentWord m) : (tauIn v).symm = tauIn v := rfl

theorem tauOut_tauOut (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    tauOut v (tauOut v p) = p := (tauOut v).symm_apply_apply p

theorem tauIn_tauIn (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    tauIn v (tauIn v p) = p := (tauIn v).symm_apply_apply p

/-- The matching of a signed word: outgoing corner to incoming corner of its arc. -/
def sM (v : SignedAdjacentWord m) : Equiv.Perm (Fin v.length × Fin 3) :=
  (tauOut v).trans ((cc v).trans ((positiveRectilinearWordMatching (base v)).trans
    ((cc v).symm.trans (tauIn v))))

theorem sM_apply (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    sM v p = tauIn v ((cc v).symm (positiveRectilinearWordMatching (base v) (cc v (tauOut v p)))) :=
  rfl

theorem sM_fst (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    ((sM v p).1).val =
      ((positiveRectilinearWordMatching (base v) (cc v (tauOut v p))).1).val := rfl

/-! ### Heights -/

theorem oHeight2_eq (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    v.oHeight2 p = posOHeight2 (base v) (cc v (tauOut v p)) := by
  rcases p with ⟨h, c⟩
  have hb := base_getElem v (k := h.val) (by rw [base_length]; exact h.isLt)
  simp only [SignedAdjacentWord.oHeight2, signedOHeight2, posOHeight2, tauOut, cc,
    Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply, finCongr_apply, Fin.val_cast,
    Equiv.refl_apply]
  rw [hb]
  by_cases hs : v[h.val].2 = 1
  · simp only [hs, if_true]
  · simp only [hs, if_false]
    fin_cases c <;> simp [Equiv.swap_apply_def]

theorem xHeight2_eq (v : SignedAdjacentWord m) (q : Fin v.length × Fin 3) :
    v.xHeight2 q = posXHeight2 (base v) (cc v (tauIn v q)) := by
  rcases q with ⟨h, c⟩
  have hb := base_getElem v (k := h.val) (by rw [base_length]; exact h.isLt)
  simp only [SignedAdjacentWord.xHeight2, signedXHeight2, posXHeight2, tauIn, cc,
    Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply, finCongr_apply, Fin.val_cast,
    Equiv.refl_apply]
  rw [hb]
  by_cases hs : v[h.val].2 = 1
  · simp only [hs, if_true]
  · simp only [hs, if_false]
    fin_cases c <;> simp [Equiv.swap_apply_def]

/-- The arc of a corner keeps its height. -/
theorem sM_height (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    v.xHeight2 (sM v p) = v.oHeight2 p := by
  rw [xHeight2_eq, oHeight2_eq, sM_apply, tauIn_tauIn, Equiv.apply_symm_apply]
  have := posOHeight2_matching_symm (base v)
    (positiveRectilinearWordMatching (base v) (cc v (tauOut v p)))
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

theorem sM_middle (v : SignedAdjacentWord m) (h : Fin v.length) : sM v (h, 0) = (h, 2) := by
  rw [sM_apply]
  have e1 : tauOut v (h, 0) = (h, 0) := by
    simp only [tauOut, Equiv.coe_fn_mk]; split_ifs <;> rfl
  rw [e1]
  have e2 : cc v (h, 0) = (finCongr (base_length v).symm h, 0) := rfl
  rw [e2, positiveRectilinearWordMatching_middle]
  simp only [tauIn, Equiv.coe_fn_mk]
  apply Prod.ext
  · rfl
  · simp only [cc_symm_snd]; split_ifs <;> rfl

/-- In a letter, the outgoing and incoming heights of a corner differ. -/
theorem oHeight2_ne_xHeight2 (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    v.oHeight2 p ≠ v.xHeight2 p := by
  rcases p with ⟨h, c⟩
  simp only [SignedAdjacentWord.oHeight2, SignedAdjacentWord.xHeight2, signedOHeight2,
    signedXHeight2]
  split_ifs <;> fin_cases c <;> simp <;> omega

/-- An odd outgoing height occurs only at the corner `0`. -/
theorem oHeight2_odd_iff (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    v.oHeight2 p % 2 = 1 ↔ p.2 = 0 := by
  rcases p with ⟨h, c⟩
  simp only [SignedAdjacentWord.oHeight2, signedOHeight2]
  split_ifs <;> fin_cases c <;> simp <;> omega

/-- An odd incoming height occurs only at the corner `2`. -/
theorem xHeight2_odd_iff (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    v.xHeight2 p % 2 = 1 ↔ p.2 = 2 := by
  rcases p with ⟨h, c⟩
  simp only [SignedAdjacentWord.xHeight2, signedXHeight2]
  split_ifs <;> fin_cases c <;> simp <;> omega

/-- Two outgoing corners of the same letter with the same height coincide. -/
theorem eq_of_oHeight2_eq (v : SignedAdjacentWord m) {p p' : Fin v.length × Fin 3}
    (h1 : p.1 = p'.1) (h : v.oHeight2 p = v.oHeight2 p') : p = p' := by
  rcases p with ⟨a, c⟩
  rcases p' with ⟨a', c'⟩
  simp only at h1
  subst h1
  simp only [SignedAdjacentWord.oHeight2, signedOHeight2] at h
  congr 1
  split_ifs at h <;> fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> omega

/-- Two incoming corners of the same letter with the same height coincide. -/
theorem eq_of_xHeight2_eq (v : SignedAdjacentWord m) {p p' : Fin v.length × Fin 3}
    (h1 : p.1 = p'.1) (h : v.xHeight2 p = v.xHeight2 p') : p = p' := by
  rcases p with ⟨a, c⟩
  rcases p' with ⟨a', c'⟩
  simp only at h1
  subst h1
  simp only [SignedAdjacentWord.xHeight2, signedXHeight2] at h
  congr 1
  split_ifs at h <;> fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> omega

/-- In a letter, the incoming corner of an integer height lies left of the outgoing corner of the
same height. -/
theorem in_lt_out (v : SignedAdjacentWord m) {p q : Fin v.length × Fin 3} (h1 : p.1 = q.1)
    (hp : p.2 ≠ 0) (h : v.oHeight2 p = v.xHeight2 q) : q.2 < p.2 := by
  rcases p with ⟨a, c⟩
  rcases q with ⟨a', c'⟩
  simp only at h1 hp
  subst h1
  simp only [SignedAdjacentWord.oHeight2, SignedAdjacentWord.xHeight2, signedOHeight2,
    signedXHeight2] at h
  split_ifs at h <;> fin_cases c <;> fin_cases c' <;> simp at h hp ⊢ <;> omega

/-! ### The next occurrence -/

/-- The rank `s` occurs in the letter `k`. -/
def Occ (v : SignedAdjacentWord m) (s : ℕ) (k : Fin v.length) : Prop :=
  (v[k.val].1).val = s ∨ (v[k.val].1).val + 1 = s

theorem occ_of_oHeight2 (v : SignedAdjacentWord m) {p : Fin v.length × Fin 3} (hp : p.2 ≠ 0) :
    Occ v (v.oHeight2 p / 2) p.1 := by
  rcases p with ⟨a, c⟩
  simp only at hp
  simp only [Occ, SignedAdjacentWord.oHeight2, signedOHeight2]
  split_ifs <;> fin_cases c <;> simp at hp ⊢ <;> omega

theorem occ_of_xHeight2 (v : SignedAdjacentWord m) {q : Fin v.length × Fin 3} (hq : q.2 ≠ 2) :
    Occ v (v.xHeight2 q / 2) q.1 := by
  rcases q with ⟨a, c⟩
  simp only at hq
  simp only [Occ, SignedAdjacentWord.xHeight2, signedXHeight2]
  split_ifs <;> fin_cases c <;> simp at hq ⊢ <;> omega

theorem oHeight2_even (v : SignedAdjacentWord m) {p : Fin v.length × Fin 3} (hp : p.2 ≠ 0) :
    v.oHeight2 p = 2 * (v.oHeight2 p / 2) := by
  have := (oHeight2_odd_iff v p).not.mpr hp
  omega

/-- An integer arc ends at the next occurrence of its rank, cyclically. -/
theorem sM_spec (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) (hp : p.2 ≠ 0) :
    (p.1 < (sM v p).1 ∧ ∀ k, Occ v (v.oHeight2 p / 2) k → p.1 < k → (sM v p).1 ≤ k) ∨
      ((sM v p).1 ≤ p.1 ∧ ∀ k, Occ v (v.oHeight2 p / 2) k → (sM v p).1 ≤ k ∧ k ≤ p.1) := by
  set a := cc v (tauOut v p) with ha
  have ha2 : a.2 ≠ 0 := by
    simp only [ha, cc_snd, tauOut, Equiv.coe_fn_mk]
    split_ifs
    · exact hp
    · intro h0
      have : p.2 = Equiv.swap (1 : Fin 3) 2 0 := by
        rw [← h0, Equiv.swap_apply_self]
      rw [this] at hp; exact hp (by decide)
  let r : Fin m := if a.2 = 2 then adjacentUpper (base v)[a.1.val]
    else adjacentLower (base v)[a.1.val]
  have hcr : (a.2 = 1 ∧ r = adjacentLower (base v)[a.1.val]) ∨
      (a.2 = 2 ∧ r = adjacentUpper (base v)[a.1.val]) := by
    by_cases h2 : a.2 = 2
    · exact Or.inr ⟨h2, by simp [r, h2]⟩
    · refine Or.inl ⟨?_, by simp [r, h2]⟩
      have := a.2.isLt
      have h0 : a.2.val ≠ 0 := fun e => ha2 (Fin.ext e)
      have h2' : a.2.val ≠ 2 := fun e => h2 (Fin.ext e)
      exact Fin.ext (by simp; omega)
  have hrv : r.val = v.oHeight2 p / 2 := by
    rw [oHeight2_eq, ← ha]
    simp only [posOHeight2, r]
    have := a.2.isLt
    by_cases h2 : a.2 = 2
    · simp only [h2, if_true, adjacentUpper]; simp
    · have h1 : a.2 = 1 := by
        have h0 : a.2.val ≠ 0 := fun e => ha2 (Fin.ext e)
        have h2' : a.2.val ≠ 2 := fun e => h2 (Fin.ext e)
        exact Fin.ext (by simp; omega)
      simp only [adjacentLower, h1]; simp
  obtain ⟨q, hq1, -, hq3⟩ := matching_spec (base v) r a.1 a.2 hcr
  have hsM : ((sM v p).1).val = q.1.val := by rw [sM_fst, ← ha, hq1]
  have hocc : ∀ k : Fin v.length, Occ v (v.oHeight2 p / 2) k ↔
      (r = adjacentLower ((base v)[k.val]'(by simp [base_length])) ∨
        r = adjacentUpper ((base v)[k.val]'(by simp [base_length]))) := by
    intro k
    have hb := base_getElem v (k := k.val) (by simp [base_length])
    simp only [Occ, Fin.ext_iff, adjacentLower, adjacentUpper, hrv, hb]
    omega
  have hap : a.1.val = p.1.val := rfl
  rcases hq3 with ⟨hlt, hmin⟩ | ⟨hle, hall⟩
  · left
    refine ⟨by rw [Fin.lt_def, hsM, ← hap]; exact hlt, fun k hk hpk => ?_⟩
    have := hmin ⟨k.val, by simp [base_length]⟩ ((hocc k).mp hk)
      (by rw [Fin.lt_def]; simp only; rw [hap]; exact hpk)
    rw [Fin.le_def, hsM]; exact this
  · right
    refine ⟨by rw [Fin.le_def, hsM, ← hap]; exact hle, fun k hk => ?_⟩
    have := hall ⟨k.val, by simp [base_length]⟩ ((hocc k).mp hk)
    rw [Fin.le_def, Fin.le_def, hsM]
    exact ⟨this.1, by have := this.2; rw [Fin.le_def] at this; simp only at this; omega⟩

/-- The arc of an integer corner is determined by its height and the next-occurrence property. -/
theorem sM_eq_of_spec (v : SignedAdjacentWord m) (p q : Fin v.length × Fin 3) (hp : p.2 ≠ 0)
    (hq : v.xHeight2 q = v.oHeight2 p)
    (hnext : (p.1 < q.1 ∧ ∀ k, Occ v (v.oHeight2 p / 2) k → p.1 < k → q.1 ≤ k) ∨
      (q.1 ≤ p.1 ∧ ∀ k, Occ v (v.oHeight2 p / 2) k → q.1 ≤ k ∧ k ≤ p.1)) :
    sM v p = q := by
  have hspec := sM_spec v p hp
  have hev : v.oHeight2 p % 2 = 0 := by
    have := (oHeight2_odd_iff v p).not.mpr hp; omega
  have hq2 : q.2 ≠ 2 := fun h => by
    have := (xHeight2_odd_iff v q).mpr h; rw [hq] at this; omega
  have hq₀2 : (sM v p).2 ≠ 2 := fun h => by
    have := (xHeight2_odd_iff v (sM v p)).mpr h; rw [sM_height] at this; omega
  have oq : Occ v (v.oHeight2 p / 2) q.1 := by
    have := occ_of_xHeight2 v hq2; rwa [hq] at this
  have oq₀ : Occ v (v.oHeight2 p / 2) (sM v p).1 := by
    have := occ_of_xHeight2 v hq₀2; rwa [sM_height] at this
  have h1 : (sM v p).1 = q.1 := by
    rcases hspec with ⟨l₀, m₀⟩ | ⟨l₀, a₀⟩ <;> rcases hnext with ⟨l, m'⟩ | ⟨l, a'⟩
    · exact le_antisymm (m₀ q.1 oq l) (m' _ oq₀ l₀)
    · exact absurd (a' _ oq₀).2 (not_le.mpr l₀)
    · exact absurd (a₀ _ oq).2 (not_le.mpr l)
    · exact le_antisymm (a₀ q.1 oq).1 (a' _ oq₀).1
  exact eq_of_xHeight2_eq v h1 (by rw [sM_height, hq])

/-! ### Nearest outgoing corners -/

theorem modsub {N x y : ℕ} (hx : x < N) (hy : y < N) :
    (x + N - y) % N = if y ≤ x then x - y else x + N - y := by
  split_ifs with h
  · rw [show x + N - y = (x - y) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The number of letters strictly between `p` and `q`, going right from `p`, with a letter `p`
equal to `q` counted as a full turn. -/
def D (v : SignedAdjacentWord m) (p q : Fin v.length × Fin 3) : ℕ :=
  if p.1.val < q.1.val then q.1.val - 1 - p.1.val else q.1.val + v.length - 1 - p.1.val

theorem gap_add (v : SignedAdjacentWord m) {p q : Fin v.length × Fin 3}
    (hpq : p.1 ≠ q.1 ∨ q.2 < p.2) :
    v.cornerGap p q + p.2.val = 3 * (D v p q + 1) + q.2.val := by
  have hp1 := p.1.isLt
  have hq1 := q.1.isLt
  have hp2 := p.2.isLt
  have hq2 := q.2.isLt
  have hcp : (finProdFinEquiv p).val < v.length * 3 := (finProdFinEquiv p).isLt
  have hcq : (finProdFinEquiv q).val < v.length * 3 := (finProdFinEquiv q).isLt
  unfold SignedAdjacentWord.cornerGap D
  rw [modsub hcq hcp, finProdFinEquiv_val3, finProdFinEquiv_val3]
  have hne : p.1.val ≠ q.1.val ∨ q.2.val < p.2.val := by
    rcases hpq with h | h
    · exact Or.inl (Fin.val_ne_iff.mpr h)
    · exact Or.inr h
  split_ifs <;> omega

theorem D_cmp {L a a' h : ℕ} (ha : a < L) (ha' : a' < L) (hh : h < L) (hne : a' ≠ a)
    (spec : (a < h ∧ (a < a' → h ≤ a')) ∨ (h ≤ a ∧ h ≤ a' ∧ a' ≤ a)) :
    (if a < h then h - 1 - a else h + L - 1 - a) + 1 ≤
      (if a' < h then h - 1 - a' else h + L - 1 - a') := by
  split_ifs <;> omega

theorem gap_inj (v : SignedAdjacentWord m) {p p' q : Fin v.length × Fin 3}
    (h : v.cornerGap p q = v.cornerGap p' q) : p = p' := by
  have hcp : (finProdFinEquiv p).val < v.length * 3 := (finProdFinEquiv p).isLt
  have hcp' : (finProdFinEquiv p').val < v.length * 3 := (finProdFinEquiv p').isLt
  have hcq : (finProdFinEquiv q).val < v.length * 3 := (finProdFinEquiv q).isLt
  unfold SignedAdjacentWord.cornerGap at h
  rw [modsub hcq hcp, modsub hcq hcp'] at h
  have : (finProdFinEquiv p).val = (finProdFinEquiv p').val := by split_ifs at h <;> omega
  exact finProdFinEquiv.injective (Fin.ext this)

theorem symm_middle (v : SignedAdjacentWord m) {q : Fin v.length × Fin 3} (hq : q.2 = 2) :
    (sM v).symm q = (q.1, 0) := by
  rw [Equiv.symm_apply_eq, sM_middle]
  exact Prod.ext rfl hq

/-- **The arc entering a corner starts at the nearest outgoing corner of the same height on its
left.** -/
theorem sM_symm_min (v : SignedAdjacentWord m) (q : Fin v.length × Fin 3) :
    v.oHeight2 ((sM v).symm q) = v.xHeight2 q ∧
      ∀ p', v.oHeight2 p' = v.xHeight2 q →
        v.cornerGap ((sM v).symm q) q ≤ v.cornerGap p' q := by
  have hq : sM v ((sM v).symm q) = q := Equiv.apply_symm_apply _ _
  have hh : v.oHeight2 ((sM v).symm q) = v.xHeight2 q := by
    conv_rhs => rw [← hq]
    rw [sM_height]
  refine ⟨hh, fun p' hp' => ?_⟩
  by_cases h2 : q.2 = 2
  · have hp := symm_middle v h2
    have hodd : v.xHeight2 q % 2 = 1 := (xHeight2_odd_iff v q).mpr h2
    have hp'0 : p'.2 = 0 := (oHeight2_odd_iff v p').mp (by rw [hp']; exact hodd)
    by_cases h1 : p'.1 = q.1
    · have : p' = (q.1, 0) := Prod.ext h1 hp'0
      rw [this, hp]
    · have e1 := gap_add v (p := p') (q := q) (Or.inl h1)
      have e2 : v.cornerGap (q.1, 0) q = 2 := by
        have hcq : (finProdFinEquiv q).val < v.length * 3 := (finProdFinEquiv q).isLt
        have hcp : (finProdFinEquiv ((q.1, 0) : Fin v.length × Fin 3)).val < v.length * 3 :=
          (finProdFinEquiv _).isLt
        unfold SignedAdjacentWord.cornerGap
        rw [modsub hcq hcp, finProdFinEquiv_val3, finProdFinEquiv_val3, h2]
        simp
      rw [hp, e2]
      rw [hp'0, h2] at e1
      simp only [Fin.val_zero, Fin.val_two] at e1
      omega
  · set p := (sM v).symm q with hpdef
    have hp0 : p.2 ≠ 0 := by
      intro h0
      have := sM_middle v p.1
      rw [show ((p.1, 0) : Fin v.length × Fin 3) = p from Prod.ext rfl h0.symm, hq] at this
      exact h2 (by rw [this])
    have hev : v.oHeight2 p % 2 = 0 := by
      have := (oHeight2_odd_iff v p).not.mpr hp0; omega
    have hp'0 : p'.2 ≠ 0 := by
      intro h0
      have := (oHeight2_odd_iff v p').mpr h0
      rw [hp', ← hh] at this; omega
    by_cases h1 : p'.1 = p.1
    · rw [eq_of_oHeight2_eq v h1 (by rw [hp', hh])]
    · have hocc : Occ v (v.oHeight2 p / 2) p'.1 := by
        have := occ_of_oHeight2 v hp'0; rwa [hp', ← hh] at this
      have hspec := sM_spec v p hp0
      rw [hq] at hspec
      have hcond : ∀ p'' : Fin v.length × Fin 3, p''.2 ≠ 0 → v.oHeight2 p'' = v.xHeight2 q →
          p''.1 ≠ q.1 ∨ q.2 < p''.2 := by
        intro p'' h0 hh''
        by_cases he : p''.1 = q.1
        · exact Or.inr (in_lt_out v he h0 hh'')
        · exact Or.inl he
      have e1 := gap_add v (hcond p' hp'0 hp')
      have e2 := gap_add v (hcond p hp0 hh)
      have hD : D v p q + 1 ≤ D v p' q := by
        have hne : p'.1.val ≠ p.1.val := Fin.val_ne_iff.mpr h1
        unfold D
        apply D_cmp p.1.isLt p'.1.isLt q.1.isLt hne
        rcases hspec with ⟨hlt, hmin⟩ | ⟨hle, hall⟩
        · exact Or.inl ⟨hlt, fun h => hmin p'.1 hocc h⟩
        · exact Or.inr ⟨hle, (hall p'.1 hocc).1, (hall p'.1 hocc).2⟩
      have := p.2.isLt
      have := p'.2.isLt
      omega

/-- **Characterization of signed word grids.** -/
theorem isSignedWordGrid_iff (v : SignedAdjacentWord m) (G : GridDiagram (v.length * 3)) :
    IsSignedWordGrid v G ↔
      (∀ p q, v.oHeight2 p < v.oHeight2 q →
        G.O (finProdFinEquiv p) < G.O (finProdFinEquiv q)) ∧
      ∀ q, G.X (finProdFinEquiv q) = G.O (finProdFinEquiv ((sM v).symm q)) := by
  constructor
  · intro hG
    refine ⟨hG.O_lt, fun q => ?_⟩
    obtain ⟨p, hp1, hp2, hp3⟩ := hG.X_eq q
    obtain ⟨h0, hmin⟩ := sM_symm_min v q
    have e : p = (sM v).symm q := gap_inj v (le_antisymm (hp2 _ h0) (hmin p hp1))
    rw [hp3, e]
  · rintro ⟨hO, hX⟩
    exact ⟨hO, fun q => ⟨(sM v).symm q, (sM_symm_min v q).1, (sM_symm_min v q).2, hX q⟩⟩

theorem X_eq_sM {v : SignedAdjacentWord m} {G : GridDiagram (v.length * 3)}
    (hG : IsSignedWordGrid v G) (q : Fin v.length × Fin 3) :
    G.X (finProdFinEquiv q) = G.O (finProdFinEquiv ((sM v).symm q)) :=
  ((isSignedWordGrid_iff v G).mp hG).2 q

/-! ### Two signed word grids of one word are related by row commutations -/

theorem cyc_nonint {N a b c d : ℕ} (ha : a < N) (hb : b < N) (hc : c < N) (hd : d < N)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (hbd : b ≠ d) (had : a ≠ d) (hbc : b ≠ c)
    (h1 : (b + N - a) % N ≤ (b + N - c) % N) (h2 : (d + N - c) % N ≤ (d + N - a) % N) :
    NonintN a b c d := by
  rw [modsub hb ha, modsub hb hc] at h1
  rw [modsub hd hc, modsub hd ha] at h2
  unfold NonintN CIooN
  constructor <;> constructor <;> intro hh <;> split_ifs at h1 h2 hh ⊢ <;> omega

/-- The height of the arc in a row of a signed word grid. -/
def rowHeight (v : SignedAdjacentWord m) (G : GridDiagram (v.length * 3))
    (r : Fin (v.length * 3)) : ℕ :=
  v.oHeight2 (finProdFinEquiv.symm (G.O.transpose r))

theorem rowHeight_monotone {v : SignedAdjacentWord m} {G : GridDiagram (v.length * 3)}
    (hG : IsSignedWordGrid v G) : Monotone (rowHeight v G) := by
  intro r r' hrr'
  by_contra hlt
  rw [not_le] at hlt
  have h := hG.O_lt _ _ hlt
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, GridState.apply_transpose_apply,
    GridState.apply_transpose_apply] at h
  exact absurd hrr' (not_le.mpr h)

theorem rowHeight_eq {v : SignedAdjacentWord m} {G G' : GridDiagram (v.length * 3)}
    (hG : IsSignedWordGrid v G) (hG' : IsSignedWordGrid v G') :
    rowHeight v G' = rowHeight v G := by
  let π : Equiv.Perm (Fin (v.length * 3)) := G'.O.toPerm.symm.trans G.O.toPerm
  have hcomp : rowHeight v G' = rowHeight v G ∘ π := by
    funext r
    simp only [rowHeight, Function.comp_apply, π, Equiv.trans_apply, GridState.transpose_apply,
      Equiv.symm_apply_apply]
  have hperm : (List.ofFn (rowHeight v G')).Perm (List.ofFn (rowHeight v G)) := by
    rw [hcomp]
    exact Equiv.Perm.ofFn_comp_perm π _
  have hsort := List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr (rowHeight_monotone hG'))
    (List.sortedLE_ofFn_iff.mpr (rowHeight_monotone hG)) hperm
  exact List.ofFn_injective hsort

/-- Arcs of the same height do not interleave. -/
theorem nonint_of_height_eq (v : SignedAdjacentWord m) {p p' : Fin v.length × Fin 3}
    (hne : p ≠ p') (hh : v.oHeight2 p = v.oHeight2 p') :
    NonintN (finProdFinEquiv p).val (finProdFinEquiv (sM v p)).val
      (finProdFinEquiv p').val (finProdFinEquiv (sM v p')).val := by
  have hq : v.xHeight2 (sM v p) = v.oHeight2 p := sM_height v p
  have hq' : v.xHeight2 (sM v p') = v.oHeight2 p' := sM_height v p'
  have m1 := (sM_symm_min v (sM v p)).2 p' (by rw [hq, hh])
  have m2 := (sM_symm_min v (sM v p')).2 p (by rw [hq', hh])
  rw [Equiv.symm_apply_apply] at m1 m2
  have hne' : ∀ a b : Fin v.length × Fin 3, a ≠ b →
      (finProdFinEquiv a).val ≠ (finProdFinEquiv b).val :=
    fun a b h e => h (finProdFinEquiv.injective (Fin.ext e))
  have hpq : ∀ a b : Fin v.length × Fin 3, v.oHeight2 a = v.xHeight2 b → a ≠ b :=
    fun a b h e => oHeight2_ne_xHeight2 v a (by rw [h, e])
  unfold SignedAdjacentWord.cornerGap at m1 m2
  exact cyc_nonint (finProdFinEquiv p).isLt (finProdFinEquiv (sM v p)).isLt
    (finProdFinEquiv p').isLt (finProdFinEquiv (sM v p')).isLt
    (hne' _ _ (hpq _ _ hq.symm)) (hne' _ _ (hpq _ _ hq'.symm)) (hne' _ _ hne)
    (hne' _ _ (fun e => hne ((sM v).injective e))) (hne' _ _ (hpq _ _ (by rw [hq', hh])))
    (hne' _ _ (fun e => hpq _ _ (by rw [hq, hh]) e.symm)) m1 m2

/-- **Two signed word grids of the same word are related by grid moves.** -/
theorem signed_movesTo {v : SignedAdjacentWord m} {G G' : GridDiagram (v.length * 3)}
    (hG : IsSignedWordGrid v G) (hG' : IsSignedWordGrid v G') : G.MovesTo G' := by
  let σ : Equiv.Perm (Fin (v.length * 3)) := G.O.toPerm.symm.trans G'.O.toPerm
  have hσO : ∀ c, σ (G.O c) = G'.O c := fun c => by
    change G'.O.toPerm (G.O.toPerm.symm (G.O.toPerm c)) = G'.O.toPerm c
    rw [Equiv.symm_apply_apply]
  have hrel : G' = G.relabelRows σ := by
    ext1
    · exact GridState.ext fun c => by
        rw [GridDiagram.relabelRows_O, GridState.relabelRows_apply, hσO]
    · refine GridState.ext fun c => ?_
      rw [GridDiagram.relabelRows_X, GridState.relabelRows_apply]
      obtain ⟨a, rfl⟩ := finProdFinEquiv.surjective c
      rw [X_eq_sM hG, X_eq_sM hG', hσO]
  rw [hrel]
  apply GridDiagram.movesTo_relabelRows_of_monotone G (rowHeight v G) (rowHeight_monotone hG)
  · intro r r' hrr'
    change Grid.Noninterleaving (G.O.transpose r) (G.X.transpose r) (G.O.transpose r')
      (G.X.transpose r')
    obtain ⟨a, ha⟩ := finProdFinEquiv.surjective (G.O.transpose r)
    obtain ⟨a', ha'⟩ := finProdFinEquiv.surjective (G.O.transpose r')
    have hXa : G.X.transpose r = finProdFinEquiv (sM v a) := by
      rw [GridState.transpose_apply, Equiv.symm_apply_eq]
      change r = G.X (finProdFinEquiv (sM v a))
      rw [X_eq_sM hG, Equiv.symm_apply_apply, ha, GridState.apply_transpose_apply]
    have hXa' : G.X.transpose r' = finProdFinEquiv (sM v a') := by
      rw [GridState.transpose_apply, Equiv.symm_apply_eq]
      change r' = G.X (finProdFinEquiv (sM v a'))
      rw [X_eq_sM hG, Equiv.symm_apply_apply, ha', GridState.apply_transpose_apply]
    rw [← ha, ← ha', hXa, hXa', noninterleaving_iff_nonintN]
    by_cases he : a = a'
    · subst he
      unfold NonintN CIooN
      constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega
    · apply nonint_of_height_eq v he
      simpa only [rowHeight, ← ha, ← ha', Equiv.symm_apply_apply] using hrr'
  · intro r
    rw [← congrFun (rowHeight_eq hG hG') (σ r)]
    simp only [rowHeight, σ, Equiv.trans_apply, GridState.transpose_apply]
    change v.oHeight2 (finProdFinEquiv.symm
      (G'.O.toPerm.symm (G'.O.toPerm (G.O.toPerm.symm r)))) = _
    rw [Equiv.symm_apply_apply]


end OnLeConjecture.KnotTheory.SignedGrid
