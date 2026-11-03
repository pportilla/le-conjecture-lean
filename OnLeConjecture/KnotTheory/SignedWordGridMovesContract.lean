/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesFinal

/-! # Contraction of a bivalent column

A column `c` whose `O`- and `X`-markings lie in consecutive rows `e` and `z` is moved to the right
past columns without markings in these rows, until it is next to the column `d` carrying the other
`X`-marking of the row `e`, and then removed by a destabilization (`LabeledGrid.exists_contract`).
This is the second elementary rule of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 7, *Two elementary grid rules*). All results are
unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

theorem erase_of_adj {l m₁ m₂ : List R} {e z : R} (hnd : l.Nodup)
    (h : l = m₁ ++ e :: z :: m₂ ∨ l = m₁ ++ z :: e :: m₂) :
    l.erase e = m₁ ++ z :: m₂ := by
  rcases h with h | h <;> subst h
  · have he : e ∉ m₁ := fun hm => by
      have := List.nodup_middle.mp hnd
      exact (List.nodup_cons.mp this).1 (List.mem_append_left _ hm)
    rw [List.erase_append_right _ he, List.erase_cons_head]
  · have he : e ∉ m₁ ++ [z] := fun hm => by
      have h2 : (m₁ ++ [z] ++ e :: m₂).Nodup := by simpa using hnd
      exact (List.nodup_cons.mp (List.nodup_middle.mp h2)).1 (List.mem_append_left _ hm)
    rw [show m₁ ++ z :: e :: m₂ = (m₁ ++ [z]) ++ e :: m₂ by simp,
      List.erase_append_right _ he, List.erase_cons_head]
    simp

/-- **Contraction of a bivalent column.** -/
theorem exists_contract (G : LabeledGrid (n + 1) C R) {c d : C} {l₁ l₂ : List C}
    (hcols : G.cols = c :: (l₁ ++ d :: l₂)) {e z : R} (hOc : G.O c = e) (hXc : G.X c = z)
    (hXd : G.X d = e) (hOd : G.O d ≠ z) {m₁ m₂ : List R}
    (hadj : G.rows = m₁ ++ e :: z :: m₂ ∨ G.rows = m₁ ++ z :: e :: m₂)
    (hl₁ : ∀ d' ∈ l₁, G.O d' ≠ z ∧ G.X d' ≠ e) :
    ∃ G' : LabeledGrid n C R, G'.cols = l₁ ++ d :: l₂ ∧ G'.rows = m₁ ++ z :: m₂ ∧
      G'.O = G.O ∧ G'.X = Function.update G.X d z ∧ G.toGrid.MovesTo G'.toGrid := by
  have hcm : c ∈ G.cols := by rw [hcols]; simp
  have hnd := G.cols_nodup
  rw [hcols] at hnd
  have hcl : c ∉ l₁ := fun h => (List.nodup_cons.mp hnd).1 (List.mem_append_left _ h)
  have hrp : G.rpos (G.X c) = G.rpos (G.O c) + 1 ∨ G.rpos (G.O c) = G.rpos (G.X c) + 1 := by
    rw [hOc, hXc]
    rcases hadj with h | h
    · exact Or.inl (G.rpos_succ_of_rows h)
    · exact Or.inr (G.rpos_succ_of_rows h)
  obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveColRight (l₁ := []) (mid := l₁)
    (l₂ := d :: l₂) (c := c) (by simpa using hcols) (fun d' hd' => by
      have hd'm : d' ∈ G.cols := by rw [hcols]; simp [hd']
      have hne : d' ≠ c := fun h => hcl (h ▸ hd')
      refine G.colsNonint_of_short hcm hd'm hrp (fun h => hne (G.O_inj _ hd'm _ hcm h))
        ?_ ?_ (fun h => hne (G.X_inj _ hd'm _ hcm h))
      · rw [hXc]; exact (hl₁ d' hd').1
      · rw [hOc]; exact (hl₁ d' hd').2)
  have hc₁' : G₁.cols = l₁ ++ c :: d :: l₂ ∨ G₁.cols = l₁ ++ d :: c :: l₂ := by
    left; rw [hc₁]; simp
  have hOc₁ : G₁.O c = e := by rw [hO₁, hOc]
  have hXc₁ : G₁.X c = z := by rw [hX₁, hXc]
  have hXd₁ : G₁.X d = e := by rw [hX₁, hXd]
  have hOd₁ : G₁.O d ≠ z := by rw [hO₁]; exact hOd
  rcases hadj with h | h
  · obtain ⟨G', hc', hr', hO', hX', hm'⟩ := G₁.exists_mergeX_up (m₁ := m₁) (mid := [])
      (m₂ := m₂) hc₁' (by rw [hr₁, h]; simp) hOc₁ hXc₁ hXd₁ hOd₁ (by simp)
    refine ⟨G', hc', ?_, by rw [hO', hO₁], by rw [hX', hX₁], hm₁.trans hm'⟩
    rw [hr']; simp
  · obtain ⟨G', hc', hr', hO', hX', hm'⟩ := G₁.exists_mergeX_down (m₁ := m₁) (mid := [])
      (m₂ := m₂) hc₁' (by rw [hr₁, h]; simp) hOc₁ hXc₁ hXd₁ hOd₁ (by simp)
    refine ⟨G', hc', ?_, by rw [hO', hO₁], by rw [hX', hX₁], hm₁.trans hm'⟩
    rw [hr']; simp

end LabeledGrid

/-- In a list sorted strictly by a key, two elements with no key strictly between them are
consecutive. -/
theorem consecutive_of_key {α : Type*} {K : α → ℕ} {l : List α}
    (hl : l.Pairwise (fun a b => K a < K b)) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : K a < K b) (hnone : ∀ x ∈ l, ¬ (K a < K x ∧ K x < K b)) :
    ∃ m₁ m₂, l = m₁ ++ a :: b :: m₂ := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.mp ha with rfl | ha'
    · -- `a` is the head; the next element is `b`
      cases l with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl
        exact absurd hab (lt_irrefl _)
      | cons y l' =>
        rcases List.mem_cons.mp hb with hb | hb
        · subst hb; exact absurd hab (lt_irrefl _)
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact ⟨[], l', rfl⟩
        · exfalso
          have h1 := hl.1 y (by simp)
          have h2 := (List.pairwise_cons.mp hl.2).1 b hb'
          exact hnone y (by simp) ⟨h1, h2⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd ((hl.1 a ha').trans hab) (lt_irrefl _)
      · obtain ⟨m₁, m₂, h⟩ := ih hl.2 ha' hb' (fun x hx => hnone x (by simp [hx]))
        exact ⟨x :: m₁, m₂, by rw [h]; rfl⟩

end OnLeConjecture.KnotTheory

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

theorem getElem_shift (X t : SignedAdjacentWord m) {K k : ℕ} (hX : X.length = K)
    (hk : k < t.length) : (X ++ t)[k + K]'(by simp; omega) = t[k] := by
  rw [List.getElem_append_right (by omega)]
  simp only [hX, Nat.add_sub_cancel]

theorem occ_shift (X t : SignedAdjacentWord m) {K : ℕ} (hX : X.length = K) (s : ℕ) {k : ℕ}
    (hk : k < t.length) :
    Occ (X ++ t) s ⟨k + K, by simp; omega⟩ ↔ Occ t s ⟨k, hk⟩ := by
  unfold Occ; simp only; rw [getElem_shift X t hX hk]

/-- **Matchings of `X ++ t` and `t`.** An arc of `t` is the same arc in `X ++ t`, unless it is
the arc wrapping around to the first occurrence of a rank that occurs in `X`, in which case both
the arc leaving its start and the arc entering its end in `X ++ t` meet `X`. -/
theorem sM_shift (X t : SignedAdjacentWord m) {K : ℕ} (hX : X.length = K) {h : ℕ}
    (ht : h < t.length) (c : Fin 3) :
    (K ≤ (sM (X ++ t) (⟨h + K, by simp; omega⟩, c)).1.val ∧
        (sM (X ++ t) (⟨h + K, by simp; omega⟩, c)).1.val = (sM t (⟨h, ht⟩, c)).1.val + K ∧
        (sM (X ++ t) (⟨h + K, by simp; omega⟩, c)).2 = (sM t (⟨h, ht⟩, c)).2) ∨
      ((sM (X ++ t) (⟨h + K, by simp; omega⟩, c)).1.val < K ∧
        ((sM (X ++ t)).symm (⟨(sM t (⟨h, ht⟩, c)).1.val + K, by
          have := (sM t (⟨h, ht⟩, c)).1.isLt; simp; omega⟩, (sM t (⟨h, ht⟩, c)).2)).1.val < K) := by
  have hL : (X ++ t).length = K + t.length := by simp [hX]
  by_cases hc0 : c = 0
  · subst hc0
    left
    rw [sM_middle, sM_middle]
    exact ⟨by simp, rfl, rfl⟩
  set p₁ : Fin (X ++ t).length × Fin 3 := (⟨h + K, by simp; omega⟩, c) with hp₁
  set p₂ : Fin t.length × Fin 3 := (⟨h, ht⟩, c) with hp₂
  have hO : (X ++ t).oHeight2 p₁ = t.oHeight2 p₂ := by
    simp only [hp₁, hp₂, SignedAdjacentWord.oHeight2, getElem_shift X t hX ht]
  set s := t.oHeight2 p₂ / 2 with hs
  set q := sM t p₂ with hq
  have hql := q.1.isLt
  have hev : t.oHeight2 p₂ % 2 = 0 := by
    have := (oHeight2_odd_iff t p₂).not.mpr hc0; omega
  have hq2 : q.2 ≠ 2 := fun e => by
    have := (xHeight2_odd_iff t q).mpr e; rw [hq, sM_height] at this; omega
  have oq : Occ t s q.1 := by
    have := occ_of_xHeight2 t hq2; rwa [hq, sM_height] at this
  -- corners of `t` inside `X ++ t`
  let sh : Fin t.length × Fin 3 → Fin (X ++ t).length × Fin 3 :=
    fun a => (⟨a.1.val + K, by have := a.1.isLt; omega⟩, a.2)
  have hxh : ∀ a, (X ++ t).xHeight2 (sh a) = t.xHeight2 a := by
    intro a
    simp only [sh, SignedAdjacentWord.xHeight2, getElem_shift X t hX a.1.isLt]
  have hoh : ∀ a, (X ++ t).oHeight2 (sh a) = t.oHeight2 a := by
    intro a
    simp only [sh, SignedAdjacentWord.oHeight2, getElem_shift X t hX a.1.isLt]
  -- occurrences in `X ++ t` from position `K` on
  have hocc : ∀ k : Fin (X ++ t).length, K ≤ k.val → Occ (X ++ t) s k →
      ∃ hk : k.val - K < t.length, Occ t s ⟨k.val - K, hk⟩ := by
    intro k hk ho
    have hk' : k.val - K < t.length := by have := k.isLt; omega
    refine ⟨hk', ?_⟩
    have := (occ_shift X t hX s hk').mp
    simp only [show k.val - K + K = k.val by omega] at this
    exact this ho
  rcases sM_spec t p₂ hc0 with ⟨hlt, hmin⟩ | ⟨hle, hall⟩
  · left
    have heq : sM (X ++ t) p₁ = sh q := by
      apply sM_eq_of_spec _ _ _ hc0
      · rw [hxh, hq, sM_height, hO]
      · left
        rw [hO, ← hs]
        refine ⟨by change h + K < q.1.val + K; have : h < q.1.val := hlt; omega, fun k ho hk => ?_⟩
        have hk1 : h + K < k.val := hk
        obtain ⟨hk', ho'⟩ := hocc k (by omega) ho
        have := hmin ⟨k.val - K, hk'⟩ ho' (by change h < k.val - K; omega)
        change q.1.val + K ≤ k.val
        have : q.1.val ≤ k.val - K := this
        omega
    rw [heq]
    exact ⟨by simp [sh], rfl, rfl⟩
  · by_cases hbl : ∃ k : Fin (X ++ t).length, k.val < K ∧ Occ (X ++ t) s k
    · right
      obtain ⟨k₀, hk₀, ho₀⟩ := hbl
      constructor
      · rcases sM_spec (X ++ t) p₁ hc0 with ⟨hlt', -⟩ | ⟨-, hall'⟩
        · exfalso
          have hq'2 : (sM (X ++ t) p₁).2 ≠ 2 := fun e => by
            have := (xHeight2_odd_iff _ _).mpr e
            rw [sM_height, hO] at this; omega
          have o' : Occ (X ++ t) s (sM (X ++ t) p₁).1 := by
            have := occ_of_xHeight2 _ hq'2; rwa [sM_height, hO] at this
          have hlt'' : h + K < (sM (X ++ t) p₁).1.val := hlt'
          obtain ⟨hk', ho'⟩ := hocc _ (by omega) o'
          have := (hall ⟨_, hk'⟩ ho').2
          have : (sM (X ++ t) p₁).1.val - K ≤ h := this
          omega
        · rw [hO, ← hs] at hall'
          have := (hall' k₀ ho₀).1
          have : (sM (X ++ t) p₁).1.val ≤ k₀.val := this
          omega
      · set a := (sM (X ++ t)).symm (sh q) with ha
        have hMa : sM (X ++ t) a = sh q := by rw [ha]; exact Equiv.apply_symm_apply _ _
        change a.1.val < K
        by_contra haK
        push Not at haK
        have ha0 : a.2 ≠ 0 := by
          intro h0
          have := sM_middle (X ++ t) a.1
          rw [show ((a.1, 0) : Fin (X ++ t).length × Fin 3) = a from Prod.ext rfl h0.symm,
            hMa] at this
          exact hq2 (congrArg Prod.snd this)
        have hOa : (X ++ t).oHeight2 a = 2 * s := by
          rw [← sM_height, hMa, hxh, hq, sM_height]; omega
        have oa : Occ (X ++ t) s a.1 := by
          have := occ_of_oHeight2 _ ha0; rwa [hOa, show 2 * s / 2 = s by omega] at this
        rcases sM_spec (X ++ t) a ha0 with ⟨hlt', -⟩ | ⟨hle', hall'⟩
        · rw [hMa] at hlt'
          have hlt'' : a.1.val < q.1.val + K := hlt'
          obtain ⟨hk', ho'⟩ := hocc a.1 haK oa
          have := (hall ⟨_, hk'⟩ ho').1
          have : q.1.val ≤ a.1.val - K := this
          omega
        · rw [hMa, hOa, show 2 * s / 2 = s by omega] at hall'
          have := (hall' k₀ ho₀).1
          have : q.1.val + K ≤ k₀.val := this
          omega
    · left
      push Not at hbl
      have heq : sM (X ++ t) p₁ = sh q := by
        apply sM_eq_of_spec _ _ _ hc0
        · rw [hxh, hq, sM_height, hO]
        · right
          rw [hO, ← hs]
          refine ⟨by change q.1.val + K ≤ h + K; have : q.1.val ≤ h := hle; omega, fun k ho => ?_⟩
          have hkK : K ≤ k.val := by
            by_contra hh; push Not at hh; exact hbl k hh ho
          obtain ⟨hk', ho'⟩ := hocc k hkK ho
          have := hall ⟨k.val - K, hk'⟩ ho'
          refine ⟨?_, ?_⟩
          · change q.1.val + K ≤ k.val; have : q.1.val ≤ k.val - K := this.1; omega
          · change k.val ≤ h + K; have : k.val - K ≤ h := this.2; omega
      rw [heq]
      exact ⟨by simp [sh], rfl, rfl⟩

end OnLeConjecture.KnotTheory.SignedGrid
