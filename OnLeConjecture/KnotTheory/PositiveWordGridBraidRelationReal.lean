/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationModel
public import OnLeConjecture.KnotTheory.PositiveWordGridMovesMacros
public import OnLeConjecture.KnotTheory.TorusWordGridHybrid

/-! # Realizations of window states

A labeled grid `G` with column labels `ℕ ⊕ (ℕ × Fin 3)` and row labels `ℕ ⊕ (ℕ × Fin 3)`
*realizes* a window state `S` (`BraidWindow.Real`) if its columns are the window columns `inl w`,
`w ∈ W`, followed by the outside columns `inr q`, `q ∈ Q`, the window columns carry the labels of
`S` as `inl` row labels, and the `inl` rows of `G` are the rows of `S` in the same order. This is
`docs/route-n/J09-word-grid-moves.tex`, Definition *window state*, with the window at the left end.
The rows `inr e` are the external rows. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.BraidWindow

open TauCeti

/-- Column labels: window columns and outside corners. -/
abbrev BCol := ℕ ⊕ (ℕ × Fin 3)

/-- Row labels: window labels and outside arcs. -/
abbrev BRow := ℕ ⊕ (ℕ × Fin 3)

/-- The window labels of a list of rows. -/
def lefts (l : List BRow) : List ℕ := l.filterMap Sum.getLeft?

/-- Rows that are connecting or external. -/
def nonInt : BRow → Bool
  | Sum.inl n => isConn n
  | Sum.inr _ => true

/-- `G` realizes the window state `S`, with window column labels `W` and outside columns `Q`. -/
structure Real {n : ℕ} (S : WState) (G : LabeledGrid n BCol BRow) (W : List ℕ)
    (Q : List (ℕ × Fin 3)) : Prop where
  cols : G.cols = W.map Sum.inl ++ Q.map Sum.inr
  len : W.length = S.cols.length
  marks : ∀ p ∈ W.zip S.cols, G.O (Sum.inl p.1) = Sum.inl p.2.1 ∧ G.X (Sum.inl p.1) = Sum.inl p.2.2
  rows : lefts G.rows = S.rows

/-- The outside columns keep their markings, and the connecting and external rows keep their
order. -/
def SameOut {n n' : ℕ} (G : LabeledGrid n BCol BRow) (G' : LabeledGrid n' BCol BRow)
    (Q : List (ℕ × Fin 3)) : Prop :=
  (∀ c ∈ Q, G'.O (Sum.inr c) = G.O (Sum.inr c) ∧ G'.X (Sum.inr c) = G.X (Sum.inr c)) ∧
    G'.rows.filter nonInt = G.rows.filter nonInt

theorem SameOut.refl {n : ℕ} (G : LabeledGrid n BCol BRow) (Q : List (ℕ × Fin 3)) :
    SameOut G G Q := ⟨fun _ _ => ⟨rfl, rfl⟩, rfl⟩

theorem SameOut.trans {n₁ n₂ n₃ : ℕ} {G₁ : LabeledGrid n₁ BCol BRow} {G₂ : LabeledGrid n₂ BCol BRow}
    {G₃ : LabeledGrid n₃ BCol BRow} {Q : List (ℕ × Fin 3)} (h₁ : SameOut G₁ G₂ Q)
    (h₂ : SameOut G₂ G₃ Q) : SameOut G₁ G₃ Q :=
  ⟨fun c hc => ⟨((h₂.1 c hc).1).trans (h₁.1 c hc).1, ((h₂.1 c hc).2).trans (h₁.1 c hc).2⟩,
    h₂.2.trans h₁.2⟩

/-! ### Lists of rows -/

theorem mem_lefts {l : List BRow} {z : ℕ} : z ∈ lefts l ↔ Sum.inl z ∈ l := by
  simp only [lefts, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    rcases a with a | a
    · simp at h; rw [← h]; exact ha
    · simp at h
  · intro h; exact ⟨_, h, rfl⟩

theorem lefts_append (l₁ l₂ : List BRow) : lefts (l₁ ++ l₂) = lefts l₁ ++ lefts l₂ := by
  simp [lefts, List.filterMap_append]

theorem lefts_cons_inl (z : ℕ) (l : List BRow) : lefts (Sum.inl z :: l) = z :: lefts l := by
  simp [lefts]

theorem lefts_cons_inr (e : ℕ × Fin 3) (l : List BRow) : lefts (Sum.inr e :: l) = lefts l := by
  simp [lefts, List.filterMap_cons]

section Generic

variable {ρ : Type*} [DecidableEq ρ] (f : ρ → Option ℕ) (g : ℕ → ρ)

/-- In a list of distinct entries, positions of the entries with `f`-values in `l.filterMap f`
and in `l` are in the same order. -/
theorem idxOf_filterMap_lt_iff (hfg : ∀ z, f (g z) = some z) (hgf : ∀ r z, f r = some z → r = g z)
    {l : List ρ} (hnd : l.Nodup) {u v : ℕ} (hu : u ∈ l.filterMap f) (hv : v ∈ l.filterMap f) :
    (l.filterMap f).idxOf u < (l.filterMap f).idxOf v ↔ l.idxOf (g u) < l.idxOf (g v) := by
  induction l with
  | nil => simp at hu
  | cons a l ih =>
    have hnd' := (List.nodup_cons.mp hnd).2
    rcases ha : f a with _ | a'
    · rw [List.filterMap_cons_none ha] at hu hv ⊢
      have hga : ∀ z, a ≠ g z := fun z h => by rw [h, hfg] at ha; simp at ha
      rw [List.idxOf_cons_ne _ (hga u), List.idxOf_cons_ne _ (hga v)]
      have := ih hnd' hu hv
      omega
    · rw [List.filterMap_cons_some ha] at hu hv ⊢
      have hag := hgf a a' ha
      subst hag
      by_cases hua : u = a' <;> by_cases hva : v = a'
      · subst hua; subst hva; simp
      · subst hua
        have : g v ≠ g u := fun h => hva (by have := congrArg f h; rw [hfg, hfg] at this; simpa using this)
        rw [List.idxOf_cons_self, List.idxOf_cons_self,
          List.idxOf_cons_ne _ (Ne.symm hva), List.idxOf_cons_ne _ (Ne.symm this)]
        omega
      · subst hva
        have : g u ≠ g v := fun h => hua (by have := congrArg f h; rw [hfg, hfg] at this; simpa using this)
        rw [List.idxOf_cons_self, List.idxOf_cons_self,
          List.idxOf_cons_ne _ (Ne.symm hua), List.idxOf_cons_ne _ (Ne.symm this)]
        omega
      · have h1 : g u ≠ g a' := fun h => hua (by have := congrArg f h; rw [hfg, hfg] at this; simpa using this)
        have h2 : g v ≠ g a' := fun h => hva (by have := congrArg f h; rw [hfg, hfg] at this; simpa using this)
        rw [List.idxOf_cons_ne _ (Ne.symm hua), List.idxOf_cons_ne _ (Ne.symm hva),
          List.idxOf_cons_ne _ (Ne.symm h1), List.idxOf_cons_ne _ (Ne.symm h2)]
        have hu' := (List.mem_cons.mp hu).resolve_left hua
        have hv' := (List.mem_cons.mp hv).resolve_left hva
        have := ih hnd' hu' hv'
        omega

end Generic

theorem idxOf_mid_bounds' {α : Type*} [DecidableEq α] {l m₁ mid m₂ : List α} {x y r : α}
    (hnd : l.Nodup) (hl : l = m₁ ++ x :: (mid ++ y :: m₂)) (hr : r ∈ mid) :
    l.idxOf x < l.idxOf r ∧ l.idxOf r < l.idxOf y := by
  subst hl
  obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hr
  have hnd' := hnd
  simp only [List.append_assoc, List.cons_append] at hnd'
  rw [List.nodup_append] at hnd'
  obtain ⟨-, hnd2, hdis⟩ := hnd'
  have hx1 : x ∉ m₁ := fun h => hdis x h x (by simp) rfl
  have hr1 : r ∉ m₁ := fun h => hdis r h r (by simp) rfl
  have hy1 : y ∉ m₁ := fun h => hdis y h y (by simp) rfl
  have hn2 := List.nodup_cons.mp hnd2
  have hxr : x ≠ r := fun h => hn2.1 (by simp [h])
  have hxy : x ≠ y := fun h => hn2.1 (by simp [h])
  have hnd3 := hn2.2
  rw [List.nodup_append] at hnd3
  obtain ⟨-, hnd4, hdis2⟩ := hnd3
  have hrp1 : r ∉ p₁ := fun h => hdis2 r h r (by simp) rfl
  have hyp1 : y ∉ p₁ := fun h => hdis2 y h y (by simp) rfl
  have hn4 := List.nodup_cons.mp hnd4
  have hry : r ≠ y := fun h => hn4.1 (by simp [h])
  have hyp2 : y ∉ p₂ := fun h => by
    have := hn4.2
    rw [List.nodup_append] at this
    exact this.2.2 y h y (by simp) rfl
  simp only [List.append_assoc, List.cons_append]
  rw [List.idxOf_append_of_notMem hx1, List.idxOf_append_of_notMem hr1,
    List.idxOf_append_of_notMem hy1, List.idxOf_cons_self, List.idxOf_cons_ne _ hxr,
    List.idxOf_cons_ne _ hxy, List.idxOf_append_of_notMem hrp1, List.idxOf_append_of_notMem hyp1,
    List.idxOf_cons_self, List.idxOf_cons_ne _ hry, List.idxOf_append_of_notMem hyp2,
    List.idxOf_cons_self]
  omega

/-- Agreement of `NonintN` for two quadruples in the same relative order. -/
theorem nonintN_congr {a b c d a' b' c' d' : ℕ}
    (hab : a < b ↔ a' < b') (hba : b < a ↔ b' < a') (hac : a < c ↔ a' < c') (hca : c < a ↔ c' < a')
    (had : a < d ↔ a' < d') (hda : d < a ↔ d' < a') (hbc : b < c ↔ b' < c') (hcb : c < b ↔ c' < b')
    (hbd : b < d ↔ b' < d') (hdb : d < b ↔ d' < b') (hcd : c < d ↔ c' < d')
    (hdc : d < c ↔ d' < c') : NonintN a b c d ↔ NonintN a' b' c' d' := by
  unfold NonintN CIooN
  simp only [ne_iff_lt_or_gt, gt_iff_lt, hab, hba, hac, hca, had, hda, hbc, hcb, hbd, hdb, hcd, hdc]

/-- Agreement of `NonintN` when a strictly monotone map relates the quadruples. -/
theorem nonintN_congr_of_iff {a b c d a' b' c' d' : ℕ}
    (H : ∀ x ∈ [(a, a'), (b, b'), (c, c'), (d, d')], ∀ y ∈ [(a, a'), (b, b'), (c, c'), (d, d')],
      (x.1 < y.1 ↔ x.2 < y.2)) : NonintN a b c d ↔ NonintN a' b' c' d' :=
  nonintN_congr
    (H (a, a') (by simp) (b, b') (by simp))
    (H (b, b') (by simp) (a, a') (by simp))
    (H (a, a') (by simp) (c, c') (by simp))
    (H (c, c') (by simp) (a, a') (by simp))
    (H (a, a') (by simp) (d, d') (by simp))
    (H (d, d') (by simp) (a, a') (by simp))
    (H (b, b') (by simp) (c, c') (by simp))
    (H (c, c') (by simp) (b, b') (by simp))
    (H (b, b') (by simp) (d, d') (by simp))
    (H (d, d') (by simp) (b, b') (by simp))
    (H (c, c') (by simp) (d, d') (by simp))
    (H (d, d') (by simp) (c, c') (by simp))

/-! ### Basic facts on realizations -/

namespace Real

variable {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ} {Q : List (ℕ × Fin 3)}

theorem col_eq {t : ℕ} (ht : t < S.cols.length) : S.col t = S.cols[t] := by
  simp [WState.col, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem O_w (hG : Real S G W Q) (t : ℕ) (ht : t < W.length) :
    G.O (Sum.inl W[t]) = Sum.inl (S.col t).1 := by
  have hm : (W[t], S.cols[t]'(by rw [← hG.len]; exact ht)) ∈ W.zip S.cols := by
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp [hG.len] at ht ⊢; omega, by simp⟩
  rw [(hG.marks _ hm).1, col_eq]

theorem X_w (hG : Real S G W Q) (t : ℕ) (ht : t < W.length) :
    G.X (Sum.inl W[t]) = Sum.inl (S.col t).2 := by
  have hm : (W[t], S.cols[t]'(by rw [← hG.len]; exact ht)) ∈ W.zip S.cols := by
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp [hG.len] at ht ⊢; omega, by simp⟩
  rw [(hG.marks _ hm).2, col_eq]

theorem mem_rows (hG : Real S G W Q) {z : ℕ} : Sum.inl z ∈ G.rows ↔ z ∈ S.rows := by
  rw [← hG.rows, mem_lefts]

theorem rpos_lt_iff (hG : Real S G W Q) {u v : ℕ} (hu : u ∈ S.rows) (hv : v ∈ S.rows) :
    G.rpos (Sum.inl u) < G.rpos (Sum.inl v) ↔ S.ri u < S.ri v := by
  have h := idxOf_filterMap_lt_iff Sum.getLeft? Sum.inl (fun z => rfl)
    (fun r z h => by rcases r with r | r <;> simp at h; rw [h]) G.rows_nodup
    (u := u) (v := v) (by rw [← lefts, hG.rows]; exact hu) (by rw [← lefts, hG.rows]; exact hv)
  rw [← lefts, hG.rows] at h
  exact h.symm

theorem cpos_w (hG : Real S G W Q) {t : ℕ} (ht : t < W.length) :
    G.cpos (Sum.inl W[t]) = t := by
  have hl : t < (W.map (Sum.inl : ℕ → BCol)).length := by simpa using ht
  have e : W.map Sum.inl = (W.map (Sum.inl : ℕ → BCol)).take t ++ (W.map (Sum.inl : ℕ → BCol))[t] :: (W.map (Sum.inl : ℕ → BCol)).drop (t + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  rw [G.cpos_of_cols_eq (l₁ := (W.map (Sum.inl : ℕ → BCol)).take t)
    (l₂ := (W.map (Sum.inl : ℕ → BCol)).drop (t + 1) ++ Q.map Sum.inr) (by
      rw [hG.cols]; conv_lhs => rw [e]
      simp)]
  simp; omega

theorem cpos_q (hG : Real S G W Q) {c : BCol} (hc : c ∈ Q.map Sum.inr) : W.length ≤ G.cpos c := by
  have := G.length_le_cpos_of_mem hG.cols hc
  simpa using this

theorem mem_cols (hG : Real S G W Q) {c : BCol} (hc : c ∈ G.cols) :
    (∃ t, ∃ ht : t < W.length, c = Sum.inl W[t]) ∨ c ∈ Q.map Sum.inr := by
  rw [hG.cols, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hw
    exact Or.inl ⟨t, ht, rfl⟩
  · exact Or.inr hc

theorem w_mem (hG : Real S G W Q) {t : ℕ} (ht : t < W.length) : Sum.inl W[t] ∈ G.cols := by
  rw [hG.cols]; simp [List.getElem_mem]

theorem W_nodup (hG : Real S G W Q) : W.Nodup := by
  have := G.cols_nodup; rw [hG.cols] at this
  exact (List.nodup_map_iff Sum.inl_injective).mp (List.nodup_append.mp this).1

/-- The column of the `O`-marking of a window label. -/
theorem O_col (hG : Real S G W Q) {c : BCol} {z : ℕ} (hc : c ∈ G.cols) (h : G.O c = Sum.inl z) :
    (S.pO z < W.length ∧ G.cpos c = S.pO z) ∨ (S.pO z = W.length ∧ W.length ≤ G.cpos c) := by
  have hlen := hG.len
  rcases hG.mem_cols hc with ⟨t, ht, rfl⟩ | hq
  · left
    rw [hG.O_w t ht] at h
    have hz : (S.col t).1 = z := by simpa using h
    have hfi : S.pO z = t := by
      unfold WState.pO
      rw [List.findIdx_eq (by omega)]
      refine ⟨by rw [← col_eq (by omega), hz]; simp, fun j hj => ?_⟩
      by_contra hne
      have hj' : (S.cols[j]'(by omega)).1 = z := by simpa using hne
      have e : G.O (Sum.inl W[j]) = G.O (Sum.inl W[t]) := by
        rw [hG.O_w j (by omega), hG.O_w t ht, col_eq (by omega), hj', ← hz]
      have := G.O_inj _ (hG.w_mem (by omega)) _ (hG.w_mem ht) e
      simp only [Sum.inl.injEq] at this
      have := (List.Nodup.getElem_inj_iff hG.W_nodup).mp this
      omega
    exact ⟨by omega, by rw [hG.cpos_w ht, hfi]⟩
  · right
    refine ⟨?_, hG.cpos_q hq⟩
    unfold WState.pO
    rw [hlen, List.findIdx_eq_length]
    intro x hx
    by_contra hne
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : (S.cols[j]).1 = z := by simpa using hne
    have e : G.O (Sum.inl W[j]) = G.O c := by
      rw [hG.O_w j (by omega), h, col_eq hj, hj']
    have := G.O_inj _ (hG.w_mem (by omega)) _ hc e
    obtain ⟨q, -, hq'⟩ := List.mem_map.mp hq
    rw [← hq'] at this
    simp at this

/-- The column of the `X`-marking of a window label. -/
theorem X_col (hG : Real S G W Q) {c : BCol} {z : ℕ} (hc : c ∈ G.cols) (h : G.X c = Sum.inl z) :
    (S.pX z < W.length ∧ G.cpos c = S.pX z) ∨ (S.pX z = W.length ∧ W.length ≤ G.cpos c) := by
  have hlen := hG.len
  rcases hG.mem_cols hc with ⟨t, ht, rfl⟩ | hq
  · left
    rw [hG.X_w t ht] at h
    have hz : (S.col t).2 = z := by simpa using h
    have hfi : S.pX z = t := by
      unfold WState.pX
      rw [List.findIdx_eq (by omega)]
      refine ⟨by rw [← col_eq (by omega), hz]; simp, fun j hj => ?_⟩
      by_contra hne
      have hj' : (S.cols[j]'(by omega)).2 = z := by simpa using hne
      have e : G.X (Sum.inl W[j]) = G.X (Sum.inl W[t]) := by
        rw [hG.X_w j (by omega), hG.X_w t ht, col_eq (by omega), hj', ← hz]
      have := G.X_inj _ (hG.w_mem (by omega)) _ (hG.w_mem ht) e
      simp only [Sum.inl.injEq] at this
      have := (List.Nodup.getElem_inj_iff hG.W_nodup).mp this
      omega
    exact ⟨by omega, by rw [hG.cpos_w ht, hfi]⟩
  · right
    refine ⟨?_, hG.cpos_q hq⟩
    unfold WState.pX
    rw [hlen, List.findIdx_eq_length]
    intro x hx
    by_contra hne
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : (S.cols[j]).2 = z := by simpa using hne
    have e : G.X (Sum.inl W[j]) = G.X c := by
      rw [hG.X_w j (by omega), h, col_eq hj, hj']
    have := G.X_inj _ (hG.w_mem (by omega)) _ hc e
    obtain ⟨q, -, hq'⟩ := List.mem_map.mp hq
    rw [← hq'] at this
    simp at this

/-- Columns with a marking in an external row are outside columns. -/
theorem col_of_inr (hG : Real S G W Q) {c : BCol} {e : ℕ × Fin 3} (hc : c ∈ G.cols)
    (h : G.O c = Sum.inr e ∨ G.X c = Sum.inr e) : c ∈ Q.map Sum.inr := by
  rcases hG.mem_cols hc with ⟨t, ht, rfl⟩ | hq
  · rcases h with h | h
    · rw [hG.O_w t ht] at h; simp at h
    · rw [hG.X_w t ht] at h; simp at h
  · exact hq

end Real

end OnLeConjecture.KnotTheory.BraidWindow
