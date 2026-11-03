/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationSound

/-! # Moving free rows across external rows

Two labeled grids with the same columns and markings whose row lists differ only by the positions
of *free* rows relative to *external* rows are related by grid moves, provided that free rows do
not interleave external rows (`LabeledGrid.movesTo_of_shuffle`). Free rows are window rows, so
the order of the window rows and the order of the non-free rows are the same in both lists. This
is the last step of the proof of `docs/route-n/J09-word-grid-moves.tex`, Proposition *braid*.
All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

theorem eq_nil_of_append_cons_eq {α : Type*} {X Y Z : List α} {r : α} (hY : r ∉ Y)
    (h : X ++ r :: Y = Z ++ [r]) : Y = [] := by
  rcases List.eq_nil_or_concat Y with hY0 | ⟨Y', b, rfl⟩
  · exact hY0
  · exfalso
    have : (X ++ r :: Y') ++ [b] = Z ++ [r] := by simpa using h
    have hb := (List.append_inj' this rfl).2
    simp at hb
    exact hY (by simp [hb])

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

/-- **Shuffling free rows.** -/
theorem movesTo_of_shuffle (free win : R → Bool) (hfw : ∀ r, free r = true → win r = true)
    (G₁ G₂ : LabeledGrid n C R) (hc : G₁.cols = G₂.cols) (hO : ∀ c ∈ G₁.cols, G₁.O c = G₂.O c)
    (hX : ∀ c ∈ G₁.cols, G₁.X c = G₂.X c)
    (hcomm : ∀ a b, free a = true → win b = false → G₁.RowsNonint a b ∧ G₁.RowsNonint b a)
    (hf : G₁.rows.filter (fun r => !free r) = G₂.rows.filter (fun r => !free r))
    (hw : G₁.rows.filter win = G₂.rows.filter win) :
    G₁.toGrid.MovesTo G₂.toGrid := by
  suffices H : ∀ (k : ℕ) (H₁ : LabeledGrid n C R) (l₁ l₂ s : List R), l₂.length = k →
      H₁.cols = G₁.cols → H₁.O = G₁.O → H₁.X = G₁.X → H₁.rows = l₁ ++ s → G₂.rows = l₂ ++ s →
      l₁.filter (fun r => !free r) = l₂.filter (fun r => !free r) →
      l₁.filter win = l₂.filter win → H₁.toGrid.MovesTo G₂.toGrid by
    exact H _ G₁ G₁.rows G₂.rows [] rfl rfl rfl rfl (by simp) (by simp) hf hw
  intro k
  induction k with
  | zero =>
    intro H₁ l₁ l₂ s hl hc₁ hO₁ hX₁ hr₁ hr₂ hf' hw'
    have hl₂ : l₂ = [] := List.eq_nil_of_length_eq_zero hl
    subst hl₂
    have hl₁ : l₁ = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro r hr
      by_cases hfr : free r = true
      · have : r ∈ l₁.filter win := List.mem_filter.mpr ⟨hr, by simp [hfw r hfr]⟩
        rw [hw'] at this; simp at this
      · have : r ∈ l₁.filter (fun r => !free r) := List.mem_filter.mpr ⟨hr, by simpa using hfr⟩
        rw [hf'] at this; simp at this
    subst hl₁
    have : H₁.toGrid = G₂.toGrid := by
      apply toGrid_eq_of_data
      · rw [hc₁, hc]
      · rw [hr₁, hr₂]
      · intro c hcm; rw [hO₁, hO c (hc₁ ▸ hcm)]
      · intro c hcm; rw [hX₁, hX c (hc₁ ▸ hcm)]
    rw [this]
  | succ k ih =>
    intro H₁ l₁ l₂ s hl hc₁ hO₁ hX₁ hr₁ hr₂ hf' hw'
    obtain ⟨l₂', r, rfl⟩ : ∃ l₂' r, l₂ = l₂' ++ [r] := by
      rcases List.eq_nil_or_concat l₂ with h | ⟨L, b, h⟩
      · subst h; simp at hl
      · exact ⟨L, b, by simpa using h⟩
    have hnd₂ := G₂.rows_nodup
    rw [hr₂] at hnd₂
    have hr_mem₂ : r ∈ (l₂' ++ [r]).filter (fun r => !free r) ∨
        r ∈ (l₂' ++ [r]).filter win := by
      by_cases hfr : free r = true
      · right; exact List.mem_filter.mpr ⟨by simp, by simp [hfw r hfr]⟩
      · left; exact List.mem_filter.mpr ⟨by simp, by simpa using hfr⟩
    have hr₁m : r ∈ l₁ := by
      rcases hr_mem₂ with h | h
      · rw [← hf'] at h; exact (List.mem_filter.mp h).1
      · rw [← hw'] at h; exact (List.mem_filter.mp h).1
    obtain ⟨a₁, b₁, rfl⟩ := List.append_of_mem hr₁m
    have hnd₁ := H₁.rows_nodup
    rw [hr₁] at hnd₁
    have hrb : r ∉ b₁ := by
      intro h
      have := (List.nodup_append.mp hnd₁).1
      exact (List.nodup_cons.mp (List.nodup_append.mp this).2.1).1 h
    have hfilt : ∀ p : R → Bool, p r = true →
        (a₁ ++ r :: b₁).filter p = (l₂' ++ [r]).filter p → b₁.filter p = [] := by
      intro p hp h
      rw [List.filter_append, List.filter_cons_of_pos hp, List.filter_append,
        List.filter_cons_of_pos hp, List.filter_nil] at h
      exact eq_nil_of_append_cons_eq (fun hm => hrb (List.mem_filter.mp hm).1) h
    -- the rows after `r` commute with `r`
    have hcom : ∀ z ∈ b₁, H₁.RowsNonint r z := by
      intro z hz
      have hz' : z ∈ b₁ := hz
      rw [rowsNonint_congr G₁ H₁ hc₁ hO₁ hX₁]
      by_cases hfr : free r = true
      · have hb := hfilt win (hfw r hfr) hw'
        have hwz : win z = false := by
          by_contra hne
          have : z ∈ b₁.filter win := List.mem_filter.mpr ⟨hz, by simpa using hne⟩
          rw [hb] at this; simp at this
        exact (hcomm r z hfr hwz).1
      · have hb := hfilt (fun r => !free r) (by simpa using hfr) hf'
        have hfz : free z = true := by
          by_contra hne
          have : z ∈ b₁.filter (fun r => !free r) := List.mem_filter.mpr ⟨hz, by simpa using hne⟩
          rw [hb] at this; simp at this
        have hwr : win r = false := by
          by_contra hne
          have hb' := hfilt win (by simpa using hne) hw'
          have : z ∈ b₁.filter win := List.mem_filter.mpr ⟨hz, hfw z hfz⟩
          rw [hb'] at this; simp at this
        exact (hcomm z r hfz hwr).2
    obtain ⟨H₂, hc₂, hr₂', hO₂, hX₂, hmv⟩ := H₁.exists_moveRowUp (m₁ := a₁) (x := r) (mid := b₁)
      (m₂ := s) (by rw [hr₁]; simp) hcom
    have key : ∀ p : R → Bool, (a₁ ++ r :: b₁).filter p = (l₂' ++ [r]).filter p →
        (a₁ ++ b₁).filter p = l₂'.filter p := by
      intro p h
      by_cases hp : p r = true
      · have hb := hfilt p hp h
        rw [List.filter_append, List.filter_cons_of_pos hp, List.filter_append,
          List.filter_cons_of_pos hp, List.filter_nil, hb] at h
        rw [List.filter_append, hb]
        simpa using h
      · have hp' : p r = false := by simpa using hp
        rw [List.filter_append, List.filter_cons_of_neg (by simpa using hp'), List.filter_append,
          List.filter_cons_of_neg (by simpa using hp'), List.filter_nil, List.append_nil] at h
        rw [List.filter_append, ← h]
    refine hmv.trans (ih H₂ (a₁ ++ b₁) l₂' (r :: s) (by simp at hl; omega) (hc₂.trans hc₁)
      (hO₂.trans hO₁) (hX₂.trans hX₁) (by simp [hr₂']) (by rw [hr₂]; simp only [List.append_assoc, List.singleton_append])
      (key _ hf') (key _ hw'))

end LabeledGrid

end OnLeConjecture.KnotTheory
