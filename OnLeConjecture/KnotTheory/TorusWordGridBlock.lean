/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesMacros

/-! # Reduction of a descending Coxeter block

This module proves the block reduction lemma of `docs/route-n/J11-torus-word-grid.tex`
(Lemma *block reduction*). Let `A ≥ 1` and let `β = σ_{A-1} ⋯ σ_1 σ_0` be the descending Coxeter
word on `A + 1` strands. Its letter in position `t` is `σ_{A-1-t}`. A labeled grid contains `β` as
a block when its columns contain the `3A` corners `(0, t, c)` of `β` consecutively, with the
markings of the admissible grid of `β`, the row `inc r` entering the first occurrence of the rank
`r` in the block.

Under an order condition on the rows (`BlockRowOrder`), grid moves delete the `2A - 1` columns
`(0, t, 0)` and `(0, t, 1)`, `t < A - 1`, together with their rows, and leave the columns
`(0, 0, 2), …, (0, A - 2, 2), (0, A - 1, 1), (0, A - 1, 2)` (`exists_blockReduction`). The other
columns and rows are arbitrary.

Labels are fixed once and for all: a column is an `R`-column `ρ c` or a corner `(b, t, c)` of the
letter `t` of the block `b` of a power of `β`; a row is an `R`-row `ϱ t`, an incoming row `ι r`,
or the arc leaving a corner. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-! ### Labels -/

/-- Column labels: `R`-columns and corners `(block, letter, column)`. -/
abbrev TorusCol := ℕ ⊕ (ℕ × ℕ × Fin 3)

/-- Row labels: `R`-rows, incoming rows and arcs. -/
abbrev TorusRow := ℕ ⊕ (ℕ ⊕ (ℕ × ℕ × Fin 3))

/-- The `R`-column `ρ c`. -/
def rCol (c : ℕ) : TorusCol := Sum.inl c

/-- The corner `(b, t, c)`. -/
def cor (b t : ℕ) (c : Fin 3) : TorusCol := Sum.inr (b, t, c)

/-- The `R`-row `ϱ t`. -/
def rRow (t : ℕ) : TorusRow := Sum.inl t

/-- The incoming row `ι r`. -/
def iRow (r : ℕ) : TorusRow := Sum.inr (Sum.inl r)

/-- The arc leaving the corner `(b, t, c)`. -/
def arc (b t : ℕ) (c : Fin 3) : TorusRow := Sum.inr (Sum.inr (b, t, c))

theorem cor_injective {b t b' t' : ℕ} {c c' : Fin 3} (h : cor b t c = cor b' t' c') :
    b = b' ∧ t = t' ∧ c = c' := by
  simp only [cor, Sum.inr.injEq, Prod.mk.injEq] at h; exact h

theorem arc_injective {b t b' t' : ℕ} {c c' : Fin 3} (h : arc b t c = arc b' t' c') :
    b = b' ∧ t = t' ∧ c = c' := by
  simp only [arc, Sum.inr.injEq, Prod.mk.injEq] at h; exact h

@[simp] theorem cor_ne_rCol (b t : ℕ) (c : Fin 3) (d : ℕ) : cor b t c ≠ rCol d := by
  simp [cor, rCol]

@[simp] theorem arc_ne_rRow (b t : ℕ) (c : Fin 3) (d : ℕ) : arc b t c ≠ rRow d := by
  simp [arc, rRow]

@[simp] theorem arc_ne_iRow (b t : ℕ) (c : Fin 3) (d : ℕ) : arc b t c ≠ iRow d := by
  simp [arc, iRow]

@[simp] theorem iRow_ne_rRow (r t : ℕ) : iRow r ≠ rRow t := by simp [iRow, rRow]

@[simp] theorem cor_inj_iff {b t b' t' : ℕ} {c c' : Fin 3} :
    cor b t c = cor b' t' c' ↔ b = b' ∧ t = t' ∧ c = c' := by
  simp [cor]

@[simp] theorem arc_inj_iff {b t b' t' : ℕ} {c c' : Fin 3} :
    arc b t c = arc b' t' c' ↔ b = b' ∧ t = t' ∧ c = c' := by
  simp [arc]

@[simp] theorem iRow_inj_iff {r r' : ℕ} : iRow r = iRow r' ↔ r = r' := by simp [iRow]

@[simp] theorem rRow_inj_iff {r r' : ℕ} : rRow r = rRow r' ↔ r = r' := by simp [rRow]

@[simp] theorem rCol_inj_iff {r r' : ℕ} : rCol r = rCol r' ↔ r = r' := by simp [rCol]

/-! ### Positions in lists -/

section Positions

variable {α : Type*} [DecidableEq α]

theorem idxOf_rel_of_pairwise {l : List α} {R : α → α → Prop} (hl : l.Pairwise R)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : l.idxOf y < l.idxOf x) : R y x := by
  have h1 : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  have h2 : l.idxOf y < l.length := List.idxOf_lt_length_iff.mpr hy
  have := List.pairwise_iff_getElem.mp hl (l.idxOf y) (l.idxOf x) h2 h1 hxy
  rwa [List.getElem_idxOf, List.getElem_idxOf] at this

/-- In a list sorted by a function, a strictly smaller value comes first. -/
theorem idxOf_lt_of_level {l : List α} {f : α → ℕ} (hl : l.Pairwise (fun a b => f a ≤ f b))
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : f x < f y) : l.idxOf x < l.idxOf y := by
  by_contra h
  rcases Nat.lt_or_ge (l.idxOf y) (l.idxOf x) with h' | h'
  · have := idxOf_rel_of_pairwise hl hx hy h'; omega
  · have : l.idxOf x = l.idxOf y := by omega
    have := (List.idxOf_inj hx).mp this; subst this; omega

/-- Two elements in increasing positions split the list. -/
theorem exists_split_of_idxOf_lt {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hxy : l.idxOf x < l.idxOf y) : ∃ m₁ mid m₂, l = m₁ ++ x :: (mid ++ y :: m₂) := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases hax : a = x
    · subst hax
      have hya : y ≠ a := by
        intro h; subst h; simp at hxy
      have hy' : y ∈ l := (List.mem_cons.mp hy).resolve_left hya
      obtain ⟨mid, m₂, rfl⟩ := List.append_of_mem hy'
      exact ⟨[], mid, m₂, rfl⟩
    · have hay : a ≠ y := by
        intro h; subst h
        rw [List.idxOf_cons_self] at hxy; omega
      rw [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hay] at hxy
      obtain ⟨m₁, mid, m₂, rfl⟩ := ih ((List.mem_cons.mp hx).resolve_left (Ne.symm hax))
        ((List.mem_cons.mp hy).resolve_left (Ne.symm hay)) (by omega)
      exact ⟨a :: m₁, mid, m₂, rfl⟩

/-- An element strictly between `x` and `y` has a position strictly between theirs. -/
theorem idxOf_mid_bounds {l m₁ mid m₂ : List α} {x y r : α} (hnd : l.Nodup)
    (hl : l = m₁ ++ x :: (mid ++ y :: m₂)) (hr : r ∈ mid) : l.idxOf x < l.idxOf r := by
  subst hl
  have hxm : x ∉ m₁ := fun h => by
    have := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1; simp [h] at this
  have hrm : r ∉ m₁ := fun h => by
    have := (List.nodup_append.mp hnd).2.2 r h r (by simp [hr]); exact this rfl
  have hrx : x ≠ r := fun h => by
    subst h
    have := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1; simp [hr] at this
  rw [List.idxOf_append_of_notMem hxm, List.idxOf_append_of_notMem hrm, List.idxOf_cons_self,
    List.idxOf_cons_ne _ hrx]
  omega

/-- An element with a smaller value than `x` does not lie between `x` and `y`. -/
theorem not_mem_mid_of_level {l m₁ mid m₂ : List α} {f : α → ℕ}
    (hs : l.Pairwise (fun a b => f a ≤ f b)) (hnd : l.Nodup)
    (hl : l = m₁ ++ x :: (mid ++ y :: m₂)) {r : α} (hr : r ∈ l) (hrx : f r < f x) :
    r ∉ mid := by
  intro hm
  have h1 := idxOf_mid_bounds hnd hl hm
  have hx : x ∈ l := by rw [hl]; simp
  have h2 := idxOf_lt_of_level hs hr hx hrx
  omega

/-- An element with a larger value than `y` does not lie between `x` and `y`. -/
theorem not_mem_mid_of_level' {l m₁ mid m₂ : List α} {f : α → ℕ}
    (hs : l.Pairwise (fun a b => f a ≤ f b)) (hnd : l.Nodup)
    (hl : l = m₁ ++ x :: (mid ++ y :: m₂)) {r : α} (hr : r ∈ l) (hry : f y < f r) :
    r ∉ mid := by
  intro hm
  have hy : y ∈ l := by rw [hl]; simp
  have h2 := idxOf_lt_of_level hs hy hr hry
  subst hl
  have hrm : r ∉ m₁ := fun h => by
    have := (List.nodup_append.mp hnd).2.2 r h r (by simp [hm]); exact this rfl
  have hym : y ∉ m₁ := fun h => by
    have := (List.nodup_append.mp hnd).2.2 y h y (by simp); exact this rfl
  have hxr : x ≠ r := fun h => by
    subst h
    have := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1; simp [hm] at this
  have hxy : x ≠ y := fun h => by
    subst h
    have := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1; simp at this
  have hnd2 := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).2
  have hnd3 := (List.nodup_append.mp hnd2).2.1
  have hnd4 : (mid ++ y :: m₂).Nodup := hnd3
  have hym' : y ∉ mid := fun h => by
    have := (List.nodup_append.mp hnd4).2.2 y h y (by simp); exact this rfl
  rw [List.idxOf_append_of_notMem hrm, List.idxOf_append_of_notMem hym, List.idxOf_cons_ne _ hxr,
    List.idxOf_cons_ne _ hxy, List.idxOf_append_of_mem hm, List.idxOf_append_of_notMem hym',
    List.idxOf_cons_self] at h2
  have := List.idxOf_lt_length_iff.mpr hm
  omega

end Positions

/-! ### Lists of block columns -/

/-- The columns of the letters `t₀, …, t₀ + k - 1` of block `0`. -/
def blockTriples (t₀ k : ℕ) : List TorusCol :=
  (List.range' t₀ k).flatMap fun s => [cor 0 s 0, cor 0 s 1, cor 0 s 2]

/-- The columns `(0, s, 0), (0, s, 2)` of the letters `t₀, …, t₀ + k - 1`. -/
def blockPairs (t₀ k : ℕ) : List TorusCol :=
  (List.range' t₀ k).flatMap fun s => [cor 0 s 0, cor 0 s 2]

/-- The columns `(0, s, 2)` of the letters `t₀, …, t₀ + k - 1`. -/
def blockBs (t₀ k : ℕ) : List TorusCol :=
  (List.range' t₀ k).map fun s => cor 0 s 2

theorem blockTriples_succ (t₀ k : ℕ) :
    blockTriples t₀ (k + 1) = [cor 0 t₀ 0, cor 0 t₀ 1, cor 0 t₀ 2] ++ blockTriples (t₀ + 1) k := by
  simp [blockTriples, List.range'_succ]

theorem blockPairs_succ (t₀ k : ℕ) :
    blockPairs t₀ (k + 1) = blockPairs t₀ k ++ [cor 0 (t₀ + k) 0, cor 0 (t₀ + k) 2] := by
  simp [blockPairs, List.range'_concat]

theorem blockPairs_succ' (t₀ k : ℕ) :
    blockPairs t₀ (k + 1) = [cor 0 t₀ 0, cor 0 t₀ 2] ++ blockPairs (t₀ + 1) k := by
  simp [blockPairs, List.range'_succ]

theorem blockBs_succ (t₀ k : ℕ) :
    blockBs t₀ (k + 1) = blockBs t₀ k ++ [cor 0 (t₀ + k) 2] := by
  simp [blockBs, List.range'_concat]

theorem mem_blockBs {c : TorusCol} {t₀ k : ℕ} :
    c ∈ blockBs t₀ k ↔ ∃ s, t₀ ≤ s ∧ s < t₀ + k ∧ c = cor 0 s 2 := by
  simp [blockBs, List.mem_range', eq_comm]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨t₀ + i, by omega, by omega, rfl⟩
  · rintro ⟨s, h1, h2, rfl⟩; exact ⟨s - t₀, by omega, by congr 1; omega⟩

/-! ### The block hypotheses -/

/-- The hypotheses of the block reduction: the block `β` sits between `L₁` and `L₂`, its rows
are those of an admissible grid of `β`, the rows `inc r` enter it, and the rows are sorted by
a level function `lv` with the stated values. -/
structure BlockData {N : ℕ} (A : ℕ) (G : LabeledGrid N TorusCol TorusRow) (inc : ℕ → TorusRow)
    (lv : TorusRow → ℕ) (L₁ L₂ : List TorusCol) : Prop where
  cols : G.cols = L₁ ++ blockTriples 0 A ++ L₂
  O_cor : ∀ t < A, ∀ c, G.O (cor 0 t c) = arc 0 t c
  X_cor0 : ∀ t < A, G.X (cor 0 t 0) = inc (A - 1 - t)
  X_cor1 : ∀ t < A, G.X (cor 0 t 1) = if t = 0 then inc A else arc 0 (t - 1) 1
  X_cor2 : ∀ t < A, G.X (cor 0 t 2) = arc 0 t 0
  inc_ne : ∀ r t c, inc r ≠ arc 0 t c
  sorted : G.rows.Pairwise fun a b => lv a ≤ lv b
  lv_arc0 : ∀ t < A, lv (arc 0 t 0) = 4 * (A - 1 - t) + 2
  lv_arc1 : ∀ t < A, lv (arc 0 t 1) = 4 * (A - 1 - t)
  lv_arc2 : ∀ t < A, lv (arc 0 t 2) = 4 * (A - t)
  lv_inc : ∀ r ≤ A, lv (inc r) = 4 * r + 1

/-! ### Stage 1: merging the descending columns -/

theorem nonintN_nested_of_lt {p₁ p₂ q₁ q₂ : ℕ} (h1 : p₁ < q₁) (h2 : q₁ < q₂) (h3 : q₂ < p₂) :
    NonintN p₁ p₂ q₂ q₁ := by
  apply nonintN_of_nested; right
  constructor <;> simp only [min_def, max_def] <;> split_ifs <;> omega

theorem nonintN_below_of_lt {p₁ p₂ q₁ q₂ : ℕ} (h1 : q₁ < p₁) (h2 : q₂ < p₁) (h3 : p₁ < p₂) :
    NonintN p₁ p₂ q₁ q₂ := by
  apply nonintN_of_lt; right
  simp only [max_lt_iff, lt_min_iff]; omega

/-- **Stage 1.** After `t` merges, the descending columns of the letters `0, …, t` form one
column `(0, t, 1)` whose `X`-marking is `inc A`. -/
theorem blockStage1 {N A : ℕ} {inc : ℕ → TorusRow} {lv : TorusRow → ℕ} {L₁ L₂ : List TorusCol}
    (G : LabeledGrid N TorusCol TorusRow) (hB : BlockData A G inc lv L₁ L₂) :
    ∀ t, t + 1 ≤ A → ∃ (N' : ℕ) (G' : LabeledGrid N' TorusCol TorusRow), N' + t = N ∧
      G'.cols = L₁ ++ blockPairs 0 t ++ [cor 0 t 0, cor 0 t 1, cor 0 t 2] ++
        blockTriples (t + 1) (A - 1 - t) ++ L₂ ∧
      G'.rows.Sublist G.rows ∧
      (∀ x, x ∈ G'.rows ↔ x ∈ G.rows ∧ ∀ s < t, x ≠ arc 0 s 1) ∧
      G'.O = G.O ∧
      (∀ c ∈ G'.cols, G'.X c = if c = cor 0 t 1 then inc A else G.X c) ∧
      G.toGrid.MovesTo G'.toGrid := by
  intro t
  induction t with
  | zero =>
    intro hA
    refine ⟨N, G, rfl, ?_, List.Sublist.refl _, fun x => ⟨fun h => ⟨h, fun s hs => absurd hs
      (Nat.not_lt_zero _)⟩, fun h => h.1⟩, rfl, ?_, GridDiagram.MovesTo.refl _⟩
    · rw [hB.cols]
      obtain ⟨k, hk⟩ : ∃ k, A = k + 1 := ⟨A - 1, by omega⟩
      rw [hk, blockTriples_succ]
      simp [blockPairs, hk]
    · intro c _
      split_ifs with h
      · rw [h, hB.X_cor1 0 (by omega), if_pos rfl]
      · rfl
  | succ t ih =>
    intro hA
    obtain ⟨N₀, G₀, hN₀, hc₀, hs₀, hm₀, hO₀, hX₀, hmv₀⟩ := ih (by omega)
    have hsorted₀ : G₀.rows.Pairwise fun a b => lv a ≤ lv b := hB.sorted.sublist hs₀
    have hlt : ∀ x y, x ∈ G₀.rows → y ∈ G₀.rows → lv x < lv y → G₀.rpos x < G₀.rpos y :=
      fun x y hx hy h => idxOf_lt_of_level hsorted₀ hx hy h
    set P := L₁ ++ blockPairs 0 t
    set rest := blockTriples (t + 2) (A - 2 - t) ++ L₂
    have hcols₀ : G₀.cols = P ++ [cor 0 t 0, cor 0 t 1, cor 0 t 2] ++
        ([cor 0 (t + 1) 0, cor 0 (t + 1) 1, cor 0 (t + 1) 2] ++ rest) := by
      rw [hc₀]
      obtain ⟨k, hk⟩ : ∃ k, A - 1 - t = k + 1 := ⟨A - 2 - t, by omega⟩
      have hk' : A - 2 - t = k := by omega
      rw [hk, blockTriples_succ]
      simp only [rest, hk', List.append_assoc, show t + 1 + 1 = t + 2 from rfl]
    have hmem₀ : ∀ c, c ∈ [cor 0 t 0, cor 0 t 1, cor 0 t 2, cor 0 (t + 1) 0, cor 0 (t + 1) 1,
        cor 0 (t + 1) 2] → c ∈ G₀.cols := by
      intro c hc; rw [hcols₀]; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hXM : G₀.X (cor 0 t 1) = inc A := by
      rw [hX₀ _ (hmem₀ _ (by simp)), if_pos rfl]
    have hXother : ∀ c ∈ G₀.cols, c ≠ cor 0 t 1 → G₀.X c = G.X c := by
      intro c hc hne; rw [hX₀ c hc, if_neg hne]
    -- rows used below and their levels
    have r1 : arc 0 t 1 ∈ G₀.rows := by
      have := G₀.O_mem _ (hmem₀ (cor 0 t 1) (by simp)); rwa [hO₀, hB.O_cor t (by omega)] at this
    have r2 : inc A ∈ G₀.rows := by
      have := G₀.X_mem _ (hmem₀ (cor 0 t 1) (by simp)); rwa [hXM] at this
    have r3 : arc 0 t 0 ∈ G₀.rows := by
      have := G₀.X_mem _ (hmem₀ (cor 0 t 2) (by simp))
      rwa [hXother _ (hmem₀ _ (by simp)) (by simp), hB.X_cor2 t (by omega)] at this
    have r4 : arc 0 t 2 ∈ G₀.rows := by
      have := G₀.O_mem _ (hmem₀ (cor 0 t 2) (by simp)); rwa [hO₀, hB.O_cor t (by omega)] at this
    have r5 : arc 0 (t + 1) 0 ∈ G₀.rows := by
      have := G₀.O_mem _ (hmem₀ (cor 0 (t + 1) 0) (by simp))
      rwa [hO₀, hB.O_cor (t + 1) (by omega)] at this
    have r6 : inc (A - 1 - (t + 1)) ∈ G₀.rows := by
      have := G₀.X_mem _ (hmem₀ (cor 0 (t + 1) 0) (by simp))
      rwa [hXother _ (hmem₀ _ (by simp)) (by simp), hB.X_cor0 (t + 1) (by omega)] at this
    have l1 := hB.lv_arc1 t (by omega)
    have l0 := hB.lv_arc0 t (by omega)
    have l2 := hB.lv_arc2 t (by omega)
    have li := hB.lv_inc A le_rfl
    have l5 := hB.lv_arc0 (t + 1) (by omega)
    have l6 := hB.lv_inc (A - 1 - (t + 1)) (by omega)
    -- move the merged column right past two columns
    obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hmv₁⟩ := G₀.exists_moveColRight
      (l₁ := P ++ [cor 0 t 0]) (c := cor 0 t 1) (mid := [cor 0 t 2, cor 0 (t + 1) 0])
      (l₂ := [cor 0 (t + 1) 1, cor 0 (t + 1) 2] ++ rest) (by rw [hcols₀]; simp) (by
        intro d hd
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        unfold LabeledGrid.ColsNonint
        rw [hO₀, hXM, hB.O_cor t (by omega)]
        rcases hd with rfl | rfl
        · rw [hXother _ (hmem₀ _ (by simp)) (by simp), hB.O_cor t (by omega),
            hB.X_cor2 t (by omega)]
          exact nonintN_nested_of_lt (hlt _ _ r1 r3 (by omega)) (hlt _ _ r3 r4 (by omega))
            (hlt _ _ r4 r2 (by omega))
        · rw [hXother _ (hmem₀ _ (by simp)) (by simp), hB.O_cor (t + 1) (by omega),
            hB.X_cor0 (t + 1) (by omega)]
          exact nonintN_below_of_lt (hlt _ _ r5 r1 (by omega)) (hlt _ _ r6 r1 (by omega))
            (hlt _ _ r1 r2 (by omega)))
    -- merge with the next descending column
    have hr1' : arc 0 t 1 ∈ G₁.rows := hr₁ ▸ r1
    have hr2' : inc A ∈ G₁.rows := hr₁ ▸ r2
    have hsorted₁ : G₁.rows.Pairwise fun a b => lv a ≤ lv b := hr₁ ▸ hsorted₀
    obtain ⟨m₁, mid, m₂, hsplit⟩ := exists_split_of_idxOf_lt hr1' hr2'
      (idxOf_lt_of_level hsorted₁ hr1' hr2' (by omega))
    obtain ⟨n, rfl⟩ : ∃ n, N₀ = n + 1 := ⟨N₀ - 1, by
      have := G₀.cols_length; rw [hcols₀] at this; simp at this; omega⟩
    have hd1 : G₁.O (cor 0 (t + 1) 1) = arc 0 (t + 1) 1 := by
      rw [hO₁, hO₀, hB.O_cor (t + 1) (by omega)]
    obtain ⟨G₂, hc₂, hr₂, hO₂, hX₂, hmv₂⟩ := G₁.exists_mergeX_up
      (l₁ := P ++ [cor 0 t 0, cor 0 t 2, cor 0 (t + 1) 0]) (c := cor 0 t 1)
      (d := cor 0 (t + 1) 1) (l₂ := [cor 0 (t + 1) 2] ++ rest) (e := arc 0 t 1) (z := inc A)
      (Or.inl (by rw [hc₁]; simp)) hsplit (by rw [hO₁, hO₀, hB.O_cor t (by omega)])
      (by rw [hX₁, hXM])
      (by rw [hX₁, hXother _ (hmem₀ _ (by simp)) (by simp), hB.X_cor1 (t + 1) (by omega),
        if_neg (by omega)]; rfl)
      (by rw [hd1]; exact fun h => hB.inc_ne _ _ _ h.symm)
      (by
        intro r hr he
        rw [hd1] at he
        subst he
        have hm : arc 0 (t + 1) 1 ∈ G₁.rows := by
          have := G₁.O_mem _ (show cor 0 (t + 1) 1 ∈ G₁.cols by rw [hc₁]; simp)
          rwa [hd1] at this
        exact not_mem_mid_of_level hsorted₁ G₁.rows_nodup hsplit hm
          (by rw [hB.lv_arc1 (t + 1) (by omega)]; omega) hr)
    refine ⟨n, G₂, by omega, ?_, ?_, ?_, ?_, ?_, hmv₀.trans (hmv₁.trans hmv₂)⟩
    · rw [hc₂, blockPairs_succ]
      simp [P, rest, show A - 1 - (t + 1) = A - 2 - t by omega]
    · rw [hr₂]
      refine List.Sublist.trans ?_ (hr₁ ▸ hs₀)
      rw [hsplit]
      simp
    · intro x
      have hnd := G₁.rows_nodup
      rw [hsplit] at hnd
      constructor
      · intro hx
        rw [hr₂] at hx
        have hx1 : x ∈ G₁.rows := by rw [hsplit]; simp at hx ⊢; tauto
        have hxe : x ≠ arc 0 t 1 := by
          intro he; subst he
          have h1 := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1
          simp at h1; simp at hx; tauto
        rw [hr₁, hm₀] at hx1
        refine ⟨hx1.1, fun s hs => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact hx1.2 s hs
        · exact hxe
      · rintro ⟨hx, hs⟩
        have hx1 : x ∈ G₁.rows := by rw [hr₁, hm₀]; exact ⟨hx, fun s h => hs s (by omega)⟩
        rw [hsplit] at hx1
        rw [hr₂]
        simp at hx1 ⊢
        rcases hx1 with h | h | h | h | h
        · exact Or.inl h
        · exact absurd h (hs t (by omega))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    · rw [hO₂, hO₁, hO₀]
    · intro c hc
      rw [hX₂, hX₁]
      by_cases hcd : c = cor 0 (t + 1) 1
      · rw [hcd, Function.update_self, if_pos rfl]
      · rw [Function.update_of_ne hcd, if_neg hcd]
        have hG1 : G₁.cols = (P ++ [cor 0 t 0, cor 0 t 2, cor 0 (t + 1) 0]) ++ cor 0 t 1 ::
            (cor 0 (t + 1) 1 :: ([cor 0 (t + 1) 2] ++ rest)) := by rw [hc₁]; simp
        have hcM : c ≠ cor 0 t 1 := by
          intro he; subst he
          have hnd := G₁.cols_nodup
          rw [hG1] at hnd
          apply LabeledGrid.not_mem_of_nodup_middle hnd
          rw [hc₂] at hc
          simpa using hc
        have h1 : c ∈ G₁.cols := by
          rw [hG1]; rw [hc₂] at hc
          have : c ∈ (P ++ [cor 0 t 0, cor 0 t 2, cor 0 (t + 1) 0]) ++
              (cor 0 (t + 1) 1 :: ([cor 0 (t + 1) 2] ++ rest)) := by simpa using hc
          exact LabeledGrid.mem_middle_of_mem this
        have hperm : G₁.cols.Perm G₀.cols := by
          rw [hc₁, hcols₀]
          have := (List.perm_middle (a := cor 0 t 1) (l₁ := [cor 0 t 2, cor 0 (t + 1) 0])
            (l₂ := [cor 0 (t + 1) 1, cor 0 (t + 1) 2] ++ rest)).append_left (P ++ [cor 0 t 0])
          simpa using this
        exact hXother c (hperm.subset h1) hcM

/-! ### Stage 2: removing the middle arcs -/

/-- **Stage 2.** After stage 1 and `t` further merges, the ascending columns of the letters
`0, …, t - 1` have been merged into the columns `(0, s, 2)`. -/
theorem blockStage2 {N A : ℕ} {inc : ℕ → TorusRow} {lv : TorusRow → ℕ} {L₁ L₂ : List TorusCol}
    (G : LabeledGrid N TorusCol TorusRow) (hB : BlockData A G inc lv L₁ L₂) (hA : 1 ≤ A) :
    ∀ t, t ≤ A - 1 → ∃ (N' : ℕ) (G' : LabeledGrid N' TorusCol TorusRow), N' + (A - 1) + t = N ∧
      G'.cols = L₁ ++ blockBs 0 t ++ blockPairs t (A - 1 - t) ++
        [cor 0 (A - 1) 0, cor 0 (A - 1) 1, cor 0 (A - 1) 2] ++ L₂ ∧
      G'.rows.Sublist G.rows ∧
      (∀ x, x ∈ G'.rows ↔ x ∈ G.rows ∧ (∀ s < A - 1, x ≠ arc 0 s 1) ∧ ∀ s < t, x ≠ arc 0 s 0) ∧
      G'.O = G.O ∧ G'.X (cor 0 (A - 1) 1) = inc A ∧
      (∀ s < t, G'.X (cor 0 s 2) = inc (A - 1 - s)) ∧
      (∀ c ∈ G'.cols, c ≠ cor 0 (A - 1) 1 → (∀ s < t, c ≠ cor 0 s 2) → G'.X c = G.X c) ∧
      G.toGrid.MovesTo G'.toGrid := by
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨N₀, G₀, hN₀, hc₀, hs₀, hm₀, hO₀, hX₀, hmv₀⟩ := blockStage1 G hB (A - 1) (by omega)
    have hc' : G₀.cols = L₁ ++ blockBs 0 0 ++ blockPairs 0 (A - 1 - 0) ++
        [cor 0 (A - 1) 0, cor 0 (A - 1) 1, cor 0 (A - 1) 2] ++ L₂ := by
      rw [hc₀, show A - 1 + 1 = A by omega, show A - 1 - (A - 1) = 0 by omega]
      simp [blockBs, blockTriples]
    have hmemV : cor 0 (A - 1) 1 ∈ G₀.cols := by rw [hc₀]; simp
    refine ⟨N₀, G₀, by omega, hc', hs₀, fun x => ?_, hO₀, ?_, fun s hs => absurd hs
      (Nat.not_lt_zero _), fun c hc h1 _ => ?_, hmv₀⟩
    · rw [hm₀]; exact ⟨fun h => ⟨h.1, h.2, fun s hs => absurd hs (Nat.not_lt_zero _)⟩,
        fun h => ⟨h.1, h.2.1⟩⟩
    · rw [hX₀ _ hmemV, if_pos rfl]
    · rw [hX₀ c hc, if_neg h1]
  | succ t ih =>
    intro ht
    have a1 : A - 1 - t = (A - 2 - t) + 1 := by omega
    have a2 : A - 1 - (t + 1) = A - 2 - t := by omega
    have a3 : t < A := by omega
    have a4 : t < A - 1 := by omega
    obtain ⟨N₀, G₀, hN₀, hc₀, hs₀, hm₀, hO₀, hXV, hXB, hXo, hmv₀⟩ := ih (by omega)
    have hsorted₀ : G₀.rows.Pairwise fun a b => lv a ≤ lv b := hB.sorted.sublist hs₀
    set P := L₁ ++ blockBs 0 t
    set rest := blockPairs (t + 1) (A - 2 - t) ++
      [cor 0 (A - 1) 0, cor 0 (A - 1) 1, cor 0 (A - 1) 2] ++ L₂
    have hcols₀ : G₀.cols = P ++ cor 0 t 0 :: cor 0 t 2 :: rest := by
      rw [hc₀, a1, blockPairs_succ']
      simp only [P, rest, List.append_assoc]
      simp
    have hmA : cor 0 t 0 ∈ G₀.cols := by rw [hcols₀]; simp
    have hmB : cor 0 t 2 ∈ G₀.cols := by rw [hcols₀]; simp
    have hXA : G₀.X (cor 0 t 0) = inc (A - 1 - t) := by
      rw [hXo _ hmA (by simp) (fun s _ => by simp), hB.X_cor0 t (by omega)]
    have hXBt : G₀.X (cor 0 t 2) = arc 0 t 0 := by
      rw [hXo _ hmB (by simp) (fun s hs => by simp; omega), hB.X_cor2 t a3]
    have hOA : G₀.O (cor 0 t 0) = arc 0 t 0 := by rw [hO₀, hB.O_cor t a3]
    have hOB : G₀.O (cor 0 t 2) = arc 0 t 2 := by rw [hO₀, hB.O_cor t (by omega)]
    have re : arc 0 t 0 ∈ G₀.rows := hOA ▸ G₀.O_mem _ hmA
    have rz : inc (A - 1 - t) ∈ G₀.rows := hXA ▸ G₀.X_mem _ hmA
    have rd : arc 0 t 2 ∈ G₀.rows := hOB ▸ G₀.O_mem _ hmB
    have le := hB.lv_arc0 t (by omega)
    have lz := hB.lv_inc (A - 1 - t) (by omega)
    have ld := hB.lv_arc2 t (by omega)
    obtain ⟨m₁, mid, m₂, hsplit⟩ := exists_split_of_idxOf_lt rz re
      (idxOf_lt_of_level hsorted₀ rz re (by omega))
    obtain ⟨n, rfl⟩ : ∃ n, N₀ = n + 1 := ⟨N₀ - 1, by
      have := G₀.cols_length; rw [hcols₀] at this; simp at this; omega⟩
    obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hmv₁⟩ := G₀.exists_mergeX_down (l₁ := P) (c := cor 0 t 0)
      (d := cor 0 t 2) (l₂ := rest) (e := arc 0 t 0) (z := inc (A - 1 - t))
      (Or.inl hcols₀) hsplit hOA hXA hXBt (by rw [hOB]; exact fun h => hB.inc_ne _ _ _ h.symm)
      (by
        intro r hr he
        rw [hOB] at he; subst he
        exact not_mem_mid_of_level' hsorted₀ G₀.rows_nodup hsplit rd (by omega) hr)
    refine ⟨n, G₁, by rw [← hN₀]; ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmv₀.trans hmv₁⟩
    · rw [hc₁, blockBs_succ, a2]
      simp only [P, rest, List.append_assoc]
      simp
    · rw [hr₁]
      refine List.Sublist.trans ?_ hs₀
      rw [hsplit]; simp
    · intro x
      have hnd := G₀.rows_nodup
      rw [hsplit] at hnd
      have hiff : x ∈ G₁.rows ↔ x ∈ G₀.rows ∧ x ≠ arc 0 t 0 := by
        rw [hr₁, hsplit]
        have h1 : arc 0 t 0 ∉ m₁ ++ inc (A - 1 - t) :: (mid ++ m₂) := by
          have := LabeledGrid.not_mem_of_nodup_middle (l₁ := m₁ ++ inc (A - 1 - t) :: mid)
            (l₂ := m₂) (c := arc 0 t 0) (by simpa using hnd)
          simpa using this
        constructor
        · intro hx
          refine ⟨by simp at hx ⊢; rcases hx with h | h | h | h <;> simp [h], ?_⟩
          rintro rfl; exact h1 (by simpa using hx)
        · rintro ⟨hx, hne⟩
          simp at hx ⊢
          rcases hx with h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact absurd h hne
          · exact Or.inr (Or.inr (Or.inr h))
      rw [hiff, hm₀]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        refine ⟨h1, h2, fun s hs => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact h3 s hs
        · exact h4
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2, fun s hs => h3 s (by omega)⟩, h3 t (by omega)⟩
    · rw [hO₁, hO₀]
    · rw [hX₁, Function.update_of_ne (by simp), hXV]
    · intro s hs
      rw [hX₁]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · rw [Function.update_of_ne (by simp; omega), hXB s hs]
      · rw [Function.update_self]
    · intro c hc h1 h2
      rw [hX₁, Function.update_of_ne (h2 t (by omega))]
      have hc0 : c ∈ G₀.cols := by
        rw [hcols₀]; rw [hc₁] at hc
        exact LabeledGrid.mem_middle_of_mem hc
      exact hXo c hc0 h1 (fun s hs => h2 s (by omega))

/-- **Block reduction.** The block `β` of `3A` columns is replaced, by grid moves, by the
`A + 1` columns `(0, 0, 2), …, (0, A - 2, 2), (0, A - 1, 1), (0, A - 1, 2)`; the column
`(0, A - 1, 1)` now runs from `inc A` to the arc leaving it, and `(0, t, 2)` from `inc (A-1-t)`
to the arc leaving it. The rows `(0, t, 1)` (`t < A - 1`) and `(0, t, 0)` are deleted. -/
theorem exists_blockReduction {N A : ℕ} {inc : ℕ → TorusRow} {lv : TorusRow → ℕ}
    {L₁ L₂ : List TorusCol} (G : LabeledGrid N TorusCol TorusRow)
    (hB : BlockData A G inc lv L₁ L₂) (hA : 1 ≤ A) :
    ∃ (N' : ℕ) (G' : LabeledGrid N' TorusCol TorusRow), N' + (2 * A - 1) = N ∧
      G'.cols = L₁ ++ blockBs 0 (A - 1) ++ [cor 0 (A - 1) 1, cor 0 (A - 1) 2] ++ L₂ ∧
      G'.rows.Sublist G.rows ∧
      (∀ x, x ∈ G'.rows ↔ x ∈ G.rows ∧ (∀ s < A - 1, x ≠ arc 0 s 1) ∧ ∀ s < A, x ≠ arc 0 s 0) ∧
      G'.O = G.O ∧ G'.X (cor 0 (A - 1) 1) = inc A ∧
      (∀ s < A, G'.X (cor 0 s 2) = inc (A - 1 - s)) ∧
      (∀ c ∈ G'.cols, c ≠ cor 0 (A - 1) 1 → (∀ s < A, c ≠ cor 0 s 2) → G'.X c = G.X c) ∧
      G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨N₀, G₀, hN₀, hc₀, hs₀, hm₀, hO₀, hXV, hXB, hXo, hmv₀⟩ :=
    blockStage2 G hB hA (A - 1) le_rfl
  have hsorted₀ : G₀.rows.Pairwise fun a b => lv a ≤ lv b := hB.sorted.sublist hs₀
  have hlt : ∀ x y, x ∈ G₀.rows → y ∈ G₀.rows → lv x < lv y → G₀.rpos x < G₀.rpos y :=
    fun x y hx hy h => idxOf_lt_of_level hsorted₀ hx hy h
  set P := L₁ ++ blockBs 0 (A - 1)
  have hcols₀ : G₀.cols = P ++ cor 0 (A - 1) 0 :: ([cor 0 (A - 1) 1] ++
      cor 0 (A - 1) 2 :: L₂) := by
    rw [hc₀, show A - 1 - (A - 1) = 0 by omega]; simp [P, blockPairs]
  have hmA : cor 0 (A - 1) 0 ∈ G₀.cols := by rw [hcols₀]; simp
  have hmV : cor 0 (A - 1) 1 ∈ G₀.cols := by rw [hcols₀]; simp
  have hmB : cor 0 (A - 1) 2 ∈ G₀.cols := by rw [hcols₀]; simp
  have hXA : G₀.X (cor 0 (A - 1) 0) = inc 0 := by
    rw [hXo _ hmA (by simp) (fun s _ => by simp), hB.X_cor0 _ (by omega)]
    congr 1; omega
  have hXBt : G₀.X (cor 0 (A - 1) 2) = arc 0 (A - 1) 0 := by
    rw [hXo _ hmB (by simp) (fun s hs => by simp; omega), hB.X_cor2 _ (by omega)]
  have hOA : G₀.O (cor 0 (A - 1) 0) = arc 0 (A - 1) 0 := by rw [hO₀, hB.O_cor _ (by omega)]
  have hOV : G₀.O (cor 0 (A - 1) 1) = arc 0 (A - 1) 1 := by rw [hO₀, hB.O_cor _ (by omega)]
  have hOB : G₀.O (cor 0 (A - 1) 2) = arc 0 (A - 1) 2 := by rw [hO₀, hB.O_cor _ (by omega)]
  have ra : arc 0 (A - 1) 0 ∈ G₀.rows := hOA ▸ G₀.O_mem _ hmA
  have ri0 : inc 0 ∈ G₀.rows := hXA ▸ G₀.X_mem _ hmA
  have rv : arc 0 (A - 1) 1 ∈ G₀.rows := hOV ▸ G₀.O_mem _ hmV
  have riA : inc A ∈ G₀.rows := hXV ▸ G₀.X_mem _ hmV
  have rd : arc 0 (A - 1) 2 ∈ G₀.rows := hOB ▸ G₀.O_mem _ hmB
  have la := hB.lv_arc0 (A - 1) (by omega)
  have lv1 := hB.lv_arc1 (A - 1) (by omega)
  have ld := hB.lv_arc2 (A - 1) (by omega)
  have l0 := hB.lv_inc 0 (by omega)
  have lA := hB.lv_inc A le_rfl
  simp only [show A - 1 - (A - 1) = 0 by omega, show A - (A - 1) = 1 by omega] at la lv1 ld
  -- move the last ascending column past the merged descending column
  obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hmv₁⟩ := G₀.exists_moveColRight (l₁ := P)
    (c := cor 0 (A - 1) 0) (mid := [cor 0 (A - 1) 1]) (l₂ := cor 0 (A - 1) 2 :: L₂) hcols₀ (by
      intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      subst hd
      unfold LabeledGrid.ColsNonint
      rw [hOA, hXA, hOV, hXV]
      apply nonintN_of_nested; left
      have h1 := hlt _ _ rv ri0 (by omega)
      have h2 := hlt _ _ ri0 ra (by omega)
      have h3 := hlt _ _ ra riA (by omega)
      constructor <;> simp only [min_def, max_def] <;> split_ifs <;> omega)
  have hsorted₁ : G₁.rows.Pairwise fun a b => lv a ≤ lv b := hr₁ ▸ hsorted₀
  have ra' : arc 0 (A - 1) 0 ∈ G₁.rows := hr₁ ▸ ra
  have ri0' : inc 0 ∈ G₁.rows := hr₁ ▸ ri0
  obtain ⟨m₁, mid, m₂, hsplit⟩ := exists_split_of_idxOf_lt ri0' ra'
    (idxOf_lt_of_level hsorted₁ ri0' ra' (by omega))
  obtain ⟨n, rfl⟩ : ∃ n, N₀ = n + 1 := ⟨N₀ - 1, by
    have := G₀.cols_length; rw [hcols₀] at this; simp at this; omega⟩
  obtain ⟨G₂, hc₂, hr₂, hO₂, hX₂, hmv₂⟩ := G₁.exists_mergeX_down (l₁ := P ++ [cor 0 (A - 1) 1])
    (c := cor 0 (A - 1) 0) (d := cor 0 (A - 1) 2) (l₂ := L₂) (e := arc 0 (A - 1) 0)
    (z := inc 0) (Or.inl (by rw [hc₁])) hsplit (by rw [hO₁, hOA]) (by rw [hX₁, hXA])
    (by rw [hX₁, hXBt]) (by rw [hO₁, hOB]; exact fun h => hB.inc_ne _ _ _ h.symm)
    (by
      intro r hr he
      rw [hO₁, hOB] at he; subst he
      exact not_mem_mid_of_level' hsorted₁ G₁.rows_nodup hsplit (hr₁ ▸ rd) (by omega) hr)
  refine ⟨n, G₂, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmv₀.trans (hmv₁.trans hmv₂)⟩
  · rw [hc₂]; simp [P]
  · rw [hr₂]
    refine List.Sublist.trans ?_ (hr₁ ▸ hs₀)
    rw [hsplit]; simp
  · intro x
    have hnd := G₁.rows_nodup
    rw [hsplit] at hnd
    have hiff : x ∈ G₂.rows ↔ x ∈ G₁.rows ∧ x ≠ arc 0 (A - 1) 0 := by
      rw [hr₂, hsplit]
      have h1 : arc 0 (A - 1) 0 ∉ m₁ ++ inc 0 :: (mid ++ m₂) := by
        have := LabeledGrid.not_mem_of_nodup_middle (l₁ := m₁ ++ inc 0 :: mid)
          (l₂ := m₂) (c := arc 0 (A - 1) 0) (by simpa using hnd)
        simpa using this
      constructor
      · intro hx
        refine ⟨by simp at hx ⊢; rcases hx with h | h | h | h <;> simp [h], ?_⟩
        rintro rfl; exact h1 (by simpa using hx)
      · rintro ⟨hx, hne⟩
        simp at hx ⊢
        rcases hx with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact absurd h hne
        · exact Or.inr (Or.inr (Or.inr h))
    rw [hiff, hr₁, hm₀]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨h1, h2, fun s hs => ?_⟩
      rcases Nat.lt_or_ge s (A - 1) with hs' | hs'
      · exact h3 s hs'
      · rw [show s = A - 1 by omega]; exact h4
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2, fun s hs => h3 s (by omega)⟩, h3 (A - 1) (by omega)⟩
  · rw [hO₂, hO₁, hO₀]
  · rw [hX₂, Function.update_of_ne (by simp), hX₁, hXV]
  · intro s hs
    rw [hX₂]
    rcases Nat.lt_or_ge s (A - 1) with hs' | hs'
    · rw [Function.update_of_ne (by simp; omega), hX₁, hXB s hs']
    · rw [show s = A - 1 by omega, Function.update_self]
      congr 1; omega
  · intro c hc h1 h2
    rw [hX₂, Function.update_of_ne (h2 (A - 1) (by omega)), hX₁]
    have hc0 : c ∈ G₀.cols := by
      rw [hcols₀]; rw [hc₂] at hc
      have : c ∈ P ++ (cor 0 (A - 1) 1 :: (cor 0 (A - 1) 2 :: L₂)) := by simpa using hc
      simp only [List.mem_append, List.mem_cons] at this ⊢
      rcases this with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have hcA : c ≠ cor 0 (A - 1) 0 := by
      intro he; subst he
      have hnd := G₂.cols_nodup
      rw [hc₂] at hc hnd
      have hnd1 := G₁.cols_nodup
      rw [hc₁] at hnd1
      exact LabeledGrid.not_mem_of_nodup_middle (l₁ := P ++ [cor 0 (A - 1) 1])
        (l₂ := cor 0 (A - 1) 2 :: L₂) (c := cor 0 (A - 1) 0) (by simpa using hnd1)
        (by simpa using hc)
    exact hXo c hc0 h1 (fun s hs => h2 s (by omega))

end OnLeConjecture.KnotTheory
