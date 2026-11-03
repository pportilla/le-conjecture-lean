/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.TorusWordGridBlock

/-! # Hybrid grids

The hybrid grid `H_{a,k}(β^j)` of `docs/route-n/J11-torus-word-grid.tex`, Definition *hybrid*,
with `a = A + 1` strands: the torus grid `R_{a,k}` with `N = A + 1 + k` columns, followed by the
word grid of `β^j`, where `β = σ_{A-1} ⋯ σ_0`. The predicate `IsHybrid A k j G` says that the
labeled grid `G` has the columns `hybCols A k j`, the markings `hybO A k j` and `hybX A k j`, and
rows strictly increasing for the key `hybKey A j`. The key orders the rows by height, and within a
height puts later blocks lower and the incoming row `ι r` above all arcs of height `r`.

`LabeledGrid.relabel` transports a labeled grid along injective renamings of its labels without
changing its grid diagram (`LabeledGrid.toGrid_relabel`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-! ### Renaming labels -/

theorem idxOf_map_of_leftInverse {α β : Type*} [DecidableEq α] [DecidableEq β] (g : α → β)
    (ginv : β → α) (l : List α) (hg : ∀ x ∈ l, ginv (g x) = x) (r : α) (hr : r ∈ l) :
    (l.map g).idxOf (g r) = l.idxOf r := by
  induction l with
  | nil => simp at hr
  | cons a l ih =>
    simp only [List.map_cons]
    by_cases har : a = r
    · subst har; simp
    · have hga : g a ≠ g r := fun h => har (by
        rw [← hg a (by simp), h, hg r hr])
      rw [List.idxOf_cons_ne _ hga, List.idxOf_cons_ne _ har]
      congr 1
      exact ih (fun x hx => hg x (by simp [hx])) ((List.mem_cons.mp hr).resolve_left
        (Ne.symm har))

namespace LabeledGrid

variable {n : ℕ} {C R C' R' : Type*}

/-- Rename the labels of a labeled grid along maps with left inverses. -/
def relabel (G : LabeledGrid n C R) (f : C → C') (finv : C' → C) (g : R → R') (ginv : R' → R)
    (hf : ∀ c ∈ G.cols, finv (f c) = c) (hg : ∀ r ∈ G.rows, ginv (g r) = r) :
    LabeledGrid n C' R' where
  cols := G.cols.map f
  rows := G.rows.map g
  O := g ∘ G.O ∘ finv
  X := g ∘ G.X ∘ finv
  cols_length := by simp [G.cols_length]
  rows_length := by simp [G.rows_length]
  cols_nodup := G.cols_nodup.map_on fun a ha b hb h => by rw [← hf a ha, h, hf b hb]
  rows_nodup := G.rows_nodup.map_on fun a ha b hb h => by rw [← hg a ha, h, hg b hb]
  O_mem c' hc' := by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    simp only [Function.comp, hf c hc]
    exact List.mem_map_of_mem (G.O_mem c hc)
  X_mem c' hc' := by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    simp only [Function.comp, hf c hc]
    exact List.mem_map_of_mem (G.X_mem c hc)
  O_inj a' ha' b' hb' h := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    simp only [Function.comp, hf a ha, hf b hb] at h
    have := congrArg ginv h
    rw [hg _ (G.O_mem a ha), hg _ (G.O_mem b hb)] at this
    rw [G.O_inj a ha b hb this]
  X_inj a' ha' b' hb' h := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    simp only [Function.comp, hf a ha, hf b hb] at h
    have := congrArg ginv h
    rw [hg _ (G.X_mem a ha), hg _ (G.X_mem b hb)] at this
    rw [G.X_inj a ha b hb this]
  O_ne_X c' hc' h := by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    simp only [Function.comp, hf c hc] at h
    have := congrArg ginv h
    rw [hg _ (G.O_mem c hc), hg _ (G.X_mem c hc)] at this
    exact G.O_ne_X c hc this

theorem toGrid_relabel [DecidableEq R] [DecidableEq R'] (G : LabeledGrid n C R) (f : C → C')
    (finv : C' → C) (g : R → R') (ginv : R' → R) (hf : ∀ c ∈ G.cols, finv (f c) = c)
    (hg : ∀ r ∈ G.rows, ginv (g r) = r) :
    (G.relabel f finv g ginv hf hg).toGrid = G.toGrid := by
  have hcol : ∀ i, (G.relabel f finv g ginv hf hg).colAt i = f (G.colAt i) := fun i => by
    simp [colAt, relabel]
  have hrpos : ∀ r ∈ G.rows, (G.relabel f finv g ginv hf hg).rpos (g r) = G.rpos r := by
    intro r hr
    exact idxOf_map_of_leftInverse g ginv G.rows hg r hr
  apply toGrid_eq_of_incidence
  · intro i
    rw [hcol]
    simp only [relabel, Function.comp, hf _ (G.colAt_mem i)]
    exact hrpos _ (G.O_mem _ (G.colAt_mem i))
  · intro i
    rw [hcol]
    simp only [relabel, Function.comp, hf _ (G.colAt_mem i)]
    exact hrpos _ (G.X_mem _ (G.colAt_mem i))

end LabeledGrid

/-! ### Labels of the hybrid grids -/

/-- The arc leaving the last occurrence of the rank `r` in the block `b`. -/
def outArc (A b r : ℕ) : TorusRow := if r = 0 then arc b (A - 1) 1 else arc b (A - r) 2

/-- The row entering the block `b` at the rank `r`: the row `ι r` for the first block, and the
arc leaving the last occurrence of `r` in the previous block otherwise. -/
def inRow (A b r : ℕ) : TorusRow := if b = 0 then iRow r else outArc A (b - 1) r

/-- The residue of `-c` modulo `A + 1 + k`, for `c < A + 1 + k`. -/
def oRes (A k c : ℕ) : ℕ := if c = 0 then 0 else A + 1 + k - c

/-- The residue of `A + 1 - c` modulo `A + 1 + k`, for `c < A + 1 + k`. -/
def xRes (A k c : ℕ) : ℕ := if c ≤ A + 1 then A + 1 - c else 2 * A + 2 + k - c

/-- The row of the `O`-marking with residue `t`: a window row `ι (t - 1)` or an `R`-row. -/
def winO (A t : ℕ) : TorusRow := if 1 ≤ t ∧ t ≤ A + 1 then iRow (t - 1) else rRow t

/-- The row of the `X`-marking with residue `t` when `J` blocks remain. -/
def winX (A J t : ℕ) : TorusRow := if 1 ≤ t ∧ t ≤ A + 1 then inRow A J (t - 1) else rRow t

/-- The `X`-marking of the corner `(b, t, c)`, given the rows `inc b r` entering the blocks. -/
def corX (A : ℕ) (inc : ℕ → ℕ → TorusRow) (b t : ℕ) (c : Fin 3) : TorusRow :=
  if c = 0 then inc b (A - 1 - t) else if c = 1 then (if t = 0 then inc b A else arc b (t - 1) 1)
  else arc b t 0

/-- The `O`-markings of the hybrid grid. -/
def hybO (A k : ℕ) : TorusCol → TorusRow
  | Sum.inl c => winO A (oRes A k c)
  | Sum.inr (b, t, c) => arc b t c

/-- The `X`-markings of the hybrid grid with `J` remaining blocks. -/
def hybX (A k J : ℕ) : TorusCol → TorusRow
  | Sum.inl c => winX A J (xRes A k c)
  | Sum.inr (b, t, c) => corX A (inRow A) b t c

@[simp] theorem hybO_rCol (A k c : ℕ) : hybO A k (rCol c) = winO A (oRes A k c) := rfl

@[simp] theorem hybO_cor (A k b t : ℕ) (c : Fin 3) : hybO A k (cor b t c) = arc b t c := rfl

@[simp] theorem hybX_rCol (A k J c : ℕ) : hybX A k J (rCol c) = winX A J (xRes A k c) := rfl

@[simp] theorem hybX_cor (A k J b t : ℕ) (c : Fin 3) :
    hybX A k J (cor b t c) = corX A (inRow A) b t c := rfl

/-! ### Column lists -/

/-- The corners of the letters `t₀, …, t₀ + n - 1` of the block `b`. -/
def blockColsR (b t₀ n : ℕ) : List TorusCol :=
  (List.range' t₀ n).flatMap fun t => [cor b t 0, cor b t 1, cor b t 2]

/-- The corners of the block `b`. -/
def blockCols (A b : ℕ) : List TorusCol := blockColsR b 0 A

/-- The corners of the blocks `b₀, …, b₀ + J - 1`. -/
def wordCols (A b₀ J : ℕ) : List TorusCol := (List.range' b₀ J).flatMap (blockCols A)

/-- The `R`-columns `ρ t₀, …, ρ (t₀ + n - 1)`. -/
def rColsR (t₀ n : ℕ) : List TorusCol := (List.range' t₀ n).map rCol

/-- The `R`-columns `ρ 0, …, ρ (N - 1)`. -/
def rCols (N : ℕ) : List TorusCol := rColsR 0 N

/-- The columns of the hybrid grid. -/
def hybCols (A k J : ℕ) : List TorusCol := rCols (A + 1 + k) ++ wordCols A 0 J

theorem mem_blockColsR {b t₀ n : ℕ} {x : TorusCol} :
    x ∈ blockColsR b t₀ n ↔ ∃ t, t₀ ≤ t ∧ t < t₀ + n ∧ ∃ c : Fin 3, x = cor b t c := by
  simp only [blockColsR, List.mem_flatMap, List.mem_range', List.mem_cons, List.mem_nil_iff,
    or_false]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, h | h | h⟩ <;> exact ⟨t₀ + 1 * i, by omega, by omega, _, h⟩
  · rintro ⟨t, h1, h2, c, rfl⟩
    refine ⟨t, ⟨t - t₀, by omega, by omega⟩, ?_⟩
    fin_cases c <;> simp

theorem mem_blockCols {A b : ℕ} {x : TorusCol} :
    x ∈ blockCols A b ↔ ∃ t < A, ∃ c : Fin 3, x = cor b t c := by
  rw [blockCols, mem_blockColsR]
  constructor
  · rintro ⟨t, -, h, c, rfl⟩; exact ⟨t, by omega, c, rfl⟩
  · rintro ⟨t, h, c, rfl⟩; exact ⟨t, by omega, by omega, c, rfl⟩

theorem mem_wordCols {A b₀ J : ℕ} {x : TorusCol} :
    x ∈ wordCols A b₀ J ↔ ∃ b, b₀ ≤ b ∧ b < b₀ + J ∧ ∃ t < A, ∃ c : Fin 3, x = cor b t c := by
  simp only [wordCols, List.mem_flatMap, List.mem_range', mem_blockCols]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, t, ht, c, rfl⟩
    exact ⟨b₀ + 1 * i, by omega, by omega, t, ht, c, rfl⟩
  · rintro ⟨b, h1, h2, t, ht, c, rfl⟩
    exact ⟨b, ⟨b - b₀, by omega, by omega⟩, t, ht, c, rfl⟩

theorem mem_rColsR {t₀ n : ℕ} {x : TorusCol} : x ∈ rColsR t₀ n ↔ ∃ c, t₀ ≤ c ∧ c < t₀ + n ∧
    x = rCol c := by
  simp only [rColsR, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩; exact ⟨t₀ + 1 * i, by omega, by omega, rfl⟩
  · rintro ⟨c, h1, h2, rfl⟩; exact ⟨c, ⟨c - t₀, by omega, by omega⟩, rfl⟩

theorem mem_rCols {N : ℕ} {x : TorusCol} : x ∈ rCols N ↔ ∃ c < N, x = rCol c := by
  rw [rCols, mem_rColsR]
  constructor
  · rintro ⟨c, -, h, rfl⟩; exact ⟨c, by omega, rfl⟩
  · rintro ⟨c, h, rfl⟩; exact ⟨c, by omega, by omega, rfl⟩

theorem blockColsR_length (b t₀ n : ℕ) : (blockColsR b t₀ n).length = 3 * n := by
  induction n generalizing t₀ with
  | zero => simp [blockColsR]
  | succ n ih =>
    have := ih (t₀ + 1)
    simp only [blockColsR, List.range'_succ, List.flatMap_cons, List.length_append] at this ⊢
    simp only [List.length_cons, List.length_nil] at *
    omega

theorem blockColsR_append (b t₀ n m : ℕ) :
    blockColsR b t₀ (n + m) = blockColsR b t₀ n ++ blockColsR b (t₀ + n) m := by
  unfold blockColsR
  rw [← List.flatMap_append]
  congr 1
  first
  | exact (List.range'_append_1 t₀ n m).symm
  | simp [List.range'_append]

theorem rColsR_append (t₀ n m : ℕ) : rColsR t₀ (n + m) = rColsR t₀ n ++ rColsR (t₀ + n) m := by
  unfold rColsR
  rw [← List.map_append]
  congr 1
  first
  | exact (List.range'_append_1 t₀ n m).symm
  | simp [List.range'_append]

theorem rColsR_length (t₀ n : ℕ) : (rColsR t₀ n).length = n := by simp [rColsR]

theorem rCols_length (N : ℕ) : (rCols N).length = N := rColsR_length 0 N

theorem rCols_succ (N : ℕ) : rCols (N + 1) = rCols N ++ [rCol N] := by
  rw [rCols, rColsR_append]; simp [rCols, rColsR]

theorem wordCols_succ (A b₀ J : ℕ) :
    wordCols A b₀ (J + 1) = blockCols A b₀ ++ wordCols A (b₀ + 1) J := by
  simp [wordCols, List.range'_succ]

theorem wordCols_succ' (A b₀ J : ℕ) :
    wordCols A b₀ (J + 1) = wordCols A b₀ J ++ blockCols A (b₀ + J) := by
  simp [wordCols, ← List.range'_append]

theorem blockCols_zero_eq (A : ℕ) : blockCols A 0 = blockTriples 0 A := rfl

theorem blockCols_split {A b t : ℕ} (ht : t < A) :
    blockCols A b = blockColsR b 0 t ++
      cor b t 0 :: cor b t 1 :: cor b t 2 :: blockColsR b (t + 1) (A - t - 1) := by
  rw [blockCols, show A = t + (1 + (A - t - 1)) by omega, blockColsR_append, blockColsR_append]
  simp only [zero_add, List.append_cancel_left_eq]
  rw [show t + (1 + (A - t - 1)) - t - 1 = A - t - 1 by omega]
  simp [blockColsR]

theorem cor_not_mem_rCols {N b t : ℕ} {c : Fin 3} : cor b t c ∉ rCols N := by
  intro h
  obtain ⟨c', -, h'⟩ := mem_rCols.mp h
  exact cor_ne_rCol _ _ _ _ h'

theorem rCol_not_mem_wordCols {A b₀ J c : ℕ} : rCol c ∉ wordCols A b₀ J := by
  intro h
  obtain ⟨b, -, -, t, -, c', h'⟩ := mem_wordCols.mp h
  exact cor_ne_rCol _ _ _ _ h'.symm

theorem blockColsR_nodup (b t₀ n : ℕ) : (blockColsR b t₀ n).Nodup := by
  unfold blockColsR
  rw [List.nodup_flatMap]
  refine ⟨fun t _ => by simp, ?_⟩
  refine List.Pairwise.imp (fun {t t'} (h : t < t') => ?_) (List.pairwise_lt_range' (s := t₀)
    (n := n) (step := 1) (by omega))
  intro x hx hx'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx hx'
  rcases hx with rfl | rfl | rfl <;> rcases hx' with h | h | h <;> simp only [cor_inj_iff] at h <;>
    omega

theorem blockCols_nodup (A b : ℕ) : (blockCols A b).Nodup := blockColsR_nodup b 0 A

theorem wordCols_nodup (A b₀ J : ℕ) : (wordCols A b₀ J).Nodup := by
  unfold wordCols
  rw [List.nodup_flatMap]
  refine ⟨fun b _ => blockCols_nodup A b, ?_⟩
  refine List.Pairwise.imp (fun {b b'} (h : b < b') => ?_) (List.pairwise_lt_range' (s := b₀)
    (n := J) (step := 1) (by omega))
  intro x hx hx'
  rw [mem_blockCols] at hx hx'
  obtain ⟨t, -, c, rfl⟩ := hx
  obtain ⟨t', -, c', h'⟩ := hx'
  simp only [cor_inj_iff] at h'
  omega

theorem rColsR_nodup (t₀ n : ℕ) : (rColsR t₀ n).Nodup := by
  unfold rColsR
  exact (List.nodup_range').map (fun a b h => by simpa [rCol] using h)

/-! ### Positions of columns -/

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq C]

/-- A column of a prefix of the column list comes before a column of the suffix. -/
theorem cpos_lt_of_mem_append (G : LabeledGrid n C R) {P S : List C} (h : G.cols = P ++ S)
    {x y : C} (hx : x ∈ P) (hy : y ∈ S) : G.cpos x < G.cpos y := by
  have hnd := G.cols_nodup
  rw [h] at hnd
  have hyP : y ∉ P := fun hm => (List.nodup_append.mp hnd).2.2 _ hm _ hy rfl
  unfold cpos
  rw [h, List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem hyP]
  have := List.idxOf_lt_length_iff.mpr hx
  omega

/-- A column of a prefix of the column list has a position below the length of the prefix. -/
theorem cpos_lt_length_of_mem (G : LabeledGrid n C R) {P S : List C} (h : G.cols = P ++ S)
    {x : C} (hx : x ∈ P) : G.cpos x < P.length := by
  unfold cpos
  rw [h, List.idxOf_append_of_mem hx]
  exact List.idxOf_lt_length_iff.mpr hx

/-- A column of a suffix of the column list has a position at least the length of the prefix. -/
theorem length_le_cpos_of_mem (G : LabeledGrid n C R) {P S : List C} (h : G.cols = P ++ S)
    {x : C} (hx : x ∈ S) : P.length ≤ G.cpos x := by
  have hnd := G.cols_nodup
  rw [h] at hnd
  have hxP : x ∉ P := fun hm => (List.nodup_append.mp hnd).2.2 _ hm _ hx rfl
  unfold cpos
  rw [h, List.idxOf_append_of_notMem hxP]
  omega

end LabeledGrid

/-- The position of an `R`-column in a column list beginning with the `R`-columns. -/
theorem cpos_rCol {n N : ℕ} (G : LabeledGrid n TorusCol TorusRow) {S : List TorusCol}
    (h : G.cols = rCols N ++ S) {c : ℕ} (hc : c < N) : G.cpos (rCol c) = c := by
  have : rCols N = rColsR 0 c ++ rCol c :: rColsR (c + 1) (N - c - 1) := by
    rw [rCols, show N = c + (1 + (N - c - 1)) by omega, rColsR_append, rColsR_append]
    simp [rColsR]
  rw [G.cpos_of_cols_eq (l₁ := rColsR 0 c) (l₂ := rColsR (c + 1) (N - c - 1) ++ S)
    (by rw [h, this]; simp), rColsR_length]

/-- The position of a corner in a column list containing its block. -/
theorem cpos_cor {n A b t : ℕ} (G : LabeledGrid n TorusCol TorusRow) {P S : List TorusCol}
    (h : G.cols = P ++ blockCols A b ++ S) (ht : t < A) (c : Fin 3) :
    G.cpos (cor b t c) = P.length + 3 * t + c.val := by
  rw [blockCols_split ht] at h
  set T := blockColsR b (t + 1) (A - t - 1)
  fin_cases c
  · rw [G.cpos_of_cols_eq (l₁ := P ++ blockColsR b 0 t) (l₂ := cor b t 1 :: cor b t 2 :: (T ++ S))
      (by rw [h]; simp)]
    simp [blockColsR_length]
  · rw [G.cpos_of_cols_eq (l₁ := P ++ blockColsR b 0 t ++ [cor b t 0])
      (l₂ := cor b t 2 :: (T ++ S)) (by rw [h]; simp)]
    simp [blockColsR_length]; omega
  · rw [G.cpos_of_cols_eq (l₁ := P ++ blockColsR b 0 t ++ [cor b t 0, cor b t 1]) (l₂ := T ++ S)
      (by rw [h]; simp)]
    simp [blockColsR_length]; omega

/-! ### Order of the rows -/

/-- The level of an arc leaving the corner `(_, t, c)`: four times its height. -/
def arcLv (A t c : ℕ) : ℕ :=
  if c = 0 then 4 * (A - 1 - t) + 2 else if c = 1 then 4 * (A - 1 - t) else 4 * (A - t)

/-- The order of an arc among the rows of its level, when `J` blocks remain and the arcs leaving
the last occurrences of the ranks `r < s` in the first block have been moved up. -/
def arcSub (A J s b t c : ℕ) : ℕ :=
  if b = 0 ∧ (c = 2 ∨ (c = 1 ∧ t = A - 1)) ∧ (if c = 2 then A - t else 0) < s then 4 * J + 4
  else if b + 1 = J ∧ (c = 2 ∨ (c = 1 ∧ t = A - 1)) then 4 * J + 3 else 4 * (J - b) + c

/-- The level of a row: four times its height for an arc, `4 r + 1` for `ι r`, the bottom for
`ϱ 0` and the top for the other `R`-rows. -/
def lvT (A : ℕ) : TorusRow → ℕ
  | Sum.inl t => if t = 0 then 0 else 4 * A + 4 + t
  | Sum.inr (Sum.inl r) => 4 * r + 1
  | Sum.inr (Sum.inr (_, t, c)) => arcLv A t c.val

/-- The order among the rows of one level. -/
def subSw (A J s : ℕ) : TorusRow → ℕ
  | Sum.inr (Sum.inr (b, t, c)) => arcSub A J s b t c.val
  | _ => 0

/-- The row order: by level, then by `subSw`. -/
def hybLtS (A J s : ℕ) (x y : TorusRow) : Prop :=
  lvT A x < lvT A y ∨ (lvT A x = lvT A y ∧ subSw A J s x < subSw A J s y)

@[simp] theorem lvT_rRow (A t : ℕ) : lvT A (rRow t) = if t = 0 then 0 else 4 * A + 4 + t := rfl

@[simp] theorem lvT_iRow (A r : ℕ) : lvT A (iRow r) = 4 * r + 1 := rfl

@[simp] theorem lvT_arc (A b t : ℕ) (c : Fin 3) : lvT A (arc b t c) = arcLv A t c.val := rfl

@[simp] theorem subSw_rRow (A J s t : ℕ) : subSw A J s (rRow t) = 0 := rfl

@[simp] theorem subSw_iRow (A J s r : ℕ) : subSw A J s (iRow r) = 0 := rfl

@[simp] theorem subSw_arc (A J s b t : ℕ) (c : Fin 3) :
    subSw A J s (arc b t c) = arcSub A J s b t c.val := rfl

theorem hybLtS_asymm {A J s : ℕ} {x y : TorusRow} (h : hybLtS A J s x y) :
    ¬ hybLtS A J s y x := by
  unfold hybLtS at *; omega

/-- The rows of the hybrid grid. -/
def HybRow (A k J : ℕ) (x : TorusRow) : Prop :=
  x = rRow 0 ∨ (∃ t, A + 2 ≤ t ∧ t < A + 1 + k ∧ x = rRow t) ∨ (∃ r ≤ A, x = iRow r) ∨
    ∃ b < J, ∃ t < A, ∃ c : Fin 3, x = arc b t c

/-- The labeled grid `G` is the hybrid grid `H_{A+1,k}(β^J)`, with the row order `hybLtS A J 0`
among rows of equal height. -/
structure IsHybrid {n : ℕ} (A k J : ℕ) (G : LabeledGrid n TorusCol TorusRow) : Prop where
  cols : G.cols = hybCols A k J
  O_eq : ∀ c ∈ G.cols, G.O c = hybO A k c
  X_eq : ∀ c ∈ G.cols, G.X c = hybX A k J c
  rows_iff : ∀ x, x ∈ G.rows ↔ HybRow A k J x
  sorted : G.rows.Pairwise (hybLtS A J 0)

/-- Rows that are `R`-rows, rows `ι r`, or arcs of the first `J` blocks. -/
def RowShape (A J : ℕ) (x : TorusRow) : Prop :=
  (∃ t, x = rRow t) ∨ (∃ r, x = iRow r) ∨ ∃ b < J, ∃ t < A, ∃ c : Fin 3, x = arc b t c

/-! ### Exchanging two rows of the same level -/

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

/-- Non-interleaving of two rows, from the positions of their markings. -/
theorem rowsNonint_of_cols (G : LabeledGrid n C R) {x z : R} {ox xx oz xz : C}
    (h1 : ox ∈ G.cols) (h2 : xx ∈ G.cols) (h3 : oz ∈ G.cols) (h4 : xz ∈ G.cols)
    (e1 : G.O ox = x) (e2 : G.X xx = x) (e3 : G.O oz = z) (e4 : G.X xz = z)
    (h : NonintN (G.cpos ox) (G.cpos xx) (G.cpos oz) (G.cpos xz)) : G.RowsNonint x z := by
  intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
  rw [G.O_inj a ha ox h1 (hOa.trans e1.symm), G.X_inj a' ha' xx h2 (hXa.trans e2.symm),
    G.O_inj b hb oz h3 (hOb.trans e3.symm), G.X_inj b' hb' xz h4 (hXb.trans e4.symm)]
  exact h

/-- Two labeled grids with the same columns and markings have the same non-interleaving
relation on rows. -/
theorem rowsNonint_congr {n' : ℕ} (G : LabeledGrid n C R) (G' : LabeledGrid n' C R)
    (hc : G'.cols = G.cols) (hO : G'.O = G.O) (hX : G'.X = G.X) {x z : R} :
    G'.RowsNonint x z ↔ G.RowsNonint x z := by
  unfold RowsNonint cpos
  rw [hc, hO, hX]

/-- **Exchanging two adjacent rows of a sorted list.** If `y` follows `x` in the order `R₀`
with nothing in between, the rows do not interleave, and `R₁` agrees with `R₀` except that it
puts `y` below `x`, then the rows can be exchanged by a commutation. -/
theorem exists_swapRows_sorted (G : LabeledGrid n C R) {R₀ R₁ : R → R → Prop}
    (hasymm : ∀ a b, R₀ a b → ¬ R₀ b a) (hs : G.rows.Pairwise R₀) {x y : R}
    (hx : x ∈ G.rows) (hy : y ∈ G.rows) (hxy : R₀ x y)
    (hbet : ∀ z ∈ G.rows, R₀ x z → R₀ z y → False) (hni : G.RowsNonint x y) (hyx : R₁ y x)
    (hagree : ∀ a ∈ G.rows, ∀ b ∈ G.rows, R₀ a b → ¬(a = x ∧ b = y) → R₁ a b) :
    ∃ G' : LabeledGrid n C R, G'.cols = G.cols ∧ G'.O = G.O ∧ G'.X = G.X ∧
      (∀ z, z ∈ G'.rows ↔ z ∈ G.rows) ∧ G'.rows.Pairwise R₁ ∧ G.toGrid.MovesTo G'.toGrid := by
  have hne : x ≠ y := fun h => hasymm _ _ hxy (h ▸ hxy)
  have hlt : G.rows.idxOf x < G.rows.idxOf y := by
    rcases Nat.lt_trichotomy (G.rows.idxOf x) (G.rows.idxOf y) with h | h | h
    · exact h
    · exact absurd (G.rpos_inj hx h) hne
    · exact absurd (idxOf_rel_of_pairwise hs hx hy h) (hasymm _ _ hxy)
  obtain ⟨m₁, mid, m₂, hsplit⟩ := exists_split_of_idxOf_lt hx hy hlt
  have hs' := hs
  rw [hsplit] at hs'
  have hmid : mid = [] := by
    cases mid with
    | nil => rfl
    | cons z mid' =>
      exfalso
      rw [List.pairwise_append, List.cons_append, List.pairwise_cons, List.pairwise_cons] at hs'
      obtain ⟨-, ⟨hxall, hzall, -⟩, -⟩ := hs'
      exact hbet z (by rw [hsplit]; simp) (hxall z List.mem_cons_self) (hzall y (by simp))
  subst hmid
  have hnd := G.rows_nodup
  rw [hsplit] at hnd
  simp only [List.nil_append] at hsplit hnd hs'
  have hxm₁ : x ∉ m₁ := fun h => (List.nodup_append.mp hnd).2.2 _ h _ (by simp) rfl
  have hnd2 := (List.nodup_append.mp hnd).2.1
  have hxm₂ : x ∉ m₂ := fun h => (List.nodup_cons.mp hnd2).1 (by simp [h])
  have hym₂ : y ∉ m₂ := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1 h
  have hmem : ∀ z, z ∈ G.rows ↔ z ∈ m₁ ∨ z = x ∨ z = y ∨ z ∈ m₂ := fun z => by
    rw [hsplit]; simp
  obtain ⟨G', hc', hr', hO', hX', hmv⟩ := G.exists_moveRowUp (m₁ := m₁) (x := x) (mid := [y])
    (m₂ := m₂) (by rw [hsplit]; rfl) (by simpa using hni)
  refine ⟨G', hc', hO', hX', fun z => by rw [hr', hmem]; simp; tauto, ?_, hmv⟩
  rw [hr']
  rw [List.pairwise_append, List.pairwise_cons, List.pairwise_cons] at hs'
  obtain ⟨hp₁, ⟨hxa, hya, hp₂⟩, hcross⟩ := hs'
  have ag : ∀ a b, a ∈ G.rows → b ∈ G.rows → R₀ a b → a ≠ x ∨ b ≠ y → R₁ a b :=
    fun a b ha hb h hab => hagree a ha b hb h (by tauto)
  have m1 : ∀ a ∈ m₁, a ∈ G.rows := fun a ha => (hmem a).mpr (Or.inl ha)
  have m2 : ∀ a ∈ m₂, a ∈ G.rows := fun a ha => (hmem a).mpr (Or.inr (Or.inr (Or.inr ha)))
  have nx : ∀ a ∈ m₁, a ≠ x := fun a ha e => hxm₁ (e ▸ ha)
  rw [List.pairwise_append (l₁ := m₁ ++ [y]), List.pairwise_append (l₁ := m₁),
    List.pairwise_cons (a := x) (l := m₂)]
  refine ⟨⟨hp₁.imp_of_mem fun ha hb h => ag _ _ (m1 _ ha) (m1 _ hb) h (Or.inl (nx _ ha)),
    List.pairwise_singleton _ _, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact ag _ _ (m1 _ ha) hy (hcross a ha _ (by simp)) (Or.inl (nx _ ha))
  · intro b hb
    exact ag _ _ hx (m2 _ hb) (hxa b (List.mem_cons_of_mem _ hb)) (Or.inr fun e => hym₂ (e ▸ hb))
  · exact hp₂.imp_of_mem fun ha hb h => ag _ _ (m2 _ ha) (m2 _ hb) h
      (Or.inl fun e => hxm₂ (e ▸ ha))
  · intro a ha b hb
    rw [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ag _ _ (m1 _ ha) hx (hcross a ha _ (by simp)) (Or.inl (nx _ ha))
      · exact ag _ _ (m1 _ ha) (m2 _ hb) (hcross a ha _ (by simp [hb])) (Or.inl (nx _ ha))
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hyx
      · exact ag _ _ hy (m2 _ hb) (hya b hb) (Or.inl (Ne.symm hne))

end LabeledGrid

/-! ### Exchanging the last outgoing arcs of the first and the last block -/

theorem lvT_outArc {A b r : ℕ} (hA : 1 ≤ A) (hr : r ≤ A) : lvT A (outArc A b r) = 4 * r := by
  unfold outArc
  split_ifs with h
  · subst h; simp [arcLv]
  · simp [arcLv]; omega

theorem subSw_outArc {A J s b r : ℕ} (hA : 1 ≤ A) (hr : r ≤ A) :
    subSw A J s (outArc A b r) = if b = 0 ∧ r < s then 4 * J + 4 else if b + 1 = J then 4 * J + 3
      else 4 * (J - b) + if r = 0 then 1 else 2 := by
  unfold outArc
  split_ifs with h1 h2 h3 h2 h3 <;> simp [arcSub] <;> split_ifs <;> omega

/-- The only row of the level of `outArc A 0 s` above it is `outArc A (J - 1) s`. -/
theorem eq_of_above_outArc {A J s : ℕ} (hA : 1 ≤ A) (hJ : 2 ≤ J) (hs : s ≤ A) {z : TorusRow}
    (hz : RowShape A J z) (hlv : lvT A z = 4 * s)
    (hsub : subSw A J s (outArc A 0 s) < subSw A J s z) : z = outArc A (J - 1) s := by
  rw [subSw_outArc hA hs] at hsub
  rcases hz with ⟨t, rfl⟩ | ⟨r, rfl⟩ | ⟨b, hb, t, ht, c, rfl⟩
  · simp at hsub
  · simp at hlv; omega
  · simp only [lvT_arc, subSw_arc, arcLv, arcSub] at hlv hsub
    have hc := c.isLt
    unfold outArc
    split_ifs at hlv hsub ⊢ <;>
      (try simp only [arc_inj_iff, Fin.ext_iff, Fin.val_one, Fin.val_two]) <;> omega

theorem subSw_succ_of_ne {A J s : ℕ} {z : TorusRow} (hz : RowShape A J z)
    (hne : z ≠ outArc A 0 s) : subSw A J (s + 1) z = subSw A J s z := by
  rcases hz with ⟨t, rfl⟩ | ⟨r, rfl⟩ | ⟨b, hb, t, ht, c, rfl⟩
  · rfl
  · rfl
  · simp only [subSw_arc, arcSub]
    have hc := c.isLt
    unfold outArc at hne
    split_ifs at hne ⊢ <;>
      simp only [ne_eq, arc_inj_iff, Fin.ext_iff, Fin.val_one, Fin.val_two] at hne <;> omega

namespace LabeledGrid

/-- One exchange of `outArc A 0 s` with `outArc A (J - 1) s`. -/
theorem exists_swapOut {n A J s : ℕ} (hA : 1 ≤ A) (hJ : 2 ≤ J) (hs : s ≤ A)
    (G : LabeledGrid n TorusCol TorusRow) (hshape : ∀ z ∈ G.rows, RowShape A J z)
    (hsort : G.rows.Pairwise (hybLtS A J s)) (h1 : outArc A 0 s ∈ G.rows)
    (h2 : outArc A (J - 1) s ∈ G.rows) (hni : G.RowsNonint (outArc A 0 s) (outArc A (J - 1) s)) :
    ∃ G' : LabeledGrid n TorusCol TorusRow, G'.cols = G.cols ∧ G'.O = G.O ∧ G'.X = G.X ∧
      (∀ z, z ∈ G'.rows ↔ z ∈ G.rows) ∧ G'.rows.Pairwise (hybLtS A J (s + 1)) ∧
      G.toGrid.MovesTo G'.toGrid := by
  have lx := lvT_outArc (b := 0) hA hs
  have ly := lvT_outArc (b := J - 1) hA hs
  have sx : subSw A J s (outArc A 0 s) = 4 * J + (if s = 0 then 1 else 2) := by
    rw [subSw_outArc hA hs, if_neg (by omega), if_neg (by omega), Nat.sub_zero]
  have sy : subSw A J s (outArc A (J - 1) s) = 4 * J + 3 := by
    rw [subSw_outArc hA hs, if_neg (by omega), if_pos (by omega)]
  have sx' : subSw A J (s + 1) (outArc A 0 s) = 4 * J + 4 := by
    rw [subSw_outArc hA hs, if_pos (by omega)]
  have sy' : subSw A J (s + 1) (outArc A (J - 1) s) = 4 * J + 3 := by
    rw [subSw_outArc hA hs, if_neg (by omega), if_pos (by omega)]
  have sxb : subSw A J s (outArc A 0 s) ≤ 4 * J + 2 := by rw [sx]; split_ifs <;> omega
  have above : ∀ z ∈ G.rows, hybLtS A J s (outArc A 0 s) z → lvT A z ≤ 4 * s →
      z = outArc A (J - 1) s := by
    intro z hz h hle
    unfold hybLtS at h
    rcases h with h | ⟨h, h'⟩
    · omega
    · exact eq_of_above_outArc hA hJ hs (hshape z hz) (by omega) h'
  have hne : outArc A 0 s ≠ outArc A (J - 1) s := by
    intro h; rw [h, sy] at sx; split_ifs at sx <;> omega
  refine G.exists_swapRows_sorted (fun a b => hybLtS_asymm) hsort h1 h2 ?_ ?_ hni ?_ ?_
  · unfold hybLtS; right; constructor <;> omega
  · intro z hz hxz hzy
    have := above z hz hxz (by unfold hybLtS at hzy; omega)
    subst this
    exact hybLtS_asymm hzy hzy
  · unfold hybLtS; right; constructor <;> omega
  · intro a ha b hb hab hnab
    unfold hybLtS at hab ⊢
    by_cases hax : a = outArc A 0 s
    · subst hax
      have hbx : b ≠ outArc A (J - 1) s := fun h => hnab ⟨rfl, h⟩
      rcases hab with hab | ⟨hab, hab'⟩
      · exact Or.inl hab
      · exact absurd (above b hb (Or.inr ⟨hab, hab'⟩) (by omega)) hbx
    · rw [subSw_succ_of_ne (hshape a ha) hax]
      by_cases hbx : b = outArc A 0 s
      · subst hbx
        rcases hab with hab | ⟨hab, hab'⟩
        · exact Or.inl hab
        · right; refine ⟨hab, ?_⟩; omega
      · rw [subSw_succ_of_ne (hshape b hb) hbx]; exact hab

/-- All exchanges of `outArc A 0 s` with `outArc A (J - 1) s`, for `s ≤ A`. -/
theorem exists_swapOuts {n A J : ℕ} (hA : 1 ≤ A) (hJ : 2 ≤ J)
    (G : LabeledGrid n TorusCol TorusRow) (hshape : ∀ z ∈ G.rows, RowShape A J z)
    (hsort : G.rows.Pairwise (hybLtS A J 0))
    (hmem : ∀ s ≤ A, outArc A 0 s ∈ G.rows ∧ outArc A (J - 1) s ∈ G.rows)
    (hni : ∀ s ≤ A, G.RowsNonint (outArc A 0 s) (outArc A (J - 1) s)) :
    ∃ G' : LabeledGrid n TorusCol TorusRow, G'.cols = G.cols ∧ G'.O = G.O ∧ G'.X = G.X ∧
      (∀ z, z ∈ G'.rows ↔ z ∈ G.rows) ∧ G'.rows.Pairwise (hybLtS A J (A + 1)) ∧
      G.toGrid.MovesTo G'.toGrid := by
  suffices H : ∀ s ≤ A + 1, ∃ G' : LabeledGrid n TorusCol TorusRow, G'.cols = G.cols ∧
      G'.O = G.O ∧ G'.X = G.X ∧ (∀ z, z ∈ G'.rows ↔ z ∈ G.rows) ∧
      G'.rows.Pairwise (hybLtS A J s) ∧ G.toGrid.MovesTo G'.toGrid from H (A + 1) le_rfl
  intro s
  induction s with
  | zero => exact fun _ => ⟨G, rfl, rfl, rfl, fun _ => Iff.rfl, hsort,
      GridDiagram.MovesTo.refl _⟩
  | succ s ih =>
    intro hs
    obtain ⟨G₁, hc₁, hO₁, hX₁, hm₁, hs₁, hmv₁⟩ := ih (by omega)
    obtain ⟨G₂, hc₂, hO₂, hX₂, hm₂, hs₂, hmv₂⟩ := G₁.exists_swapOut hA hJ (by omega)
      (fun z hz => hshape z ((hm₁ z).mp hz)) hs₁ ((hm₁ _).mpr (hmem s (by omega)).1)
      ((hm₁ _).mpr (hmem s (by omega)).2)
      ((rowsNonint_congr G G₁ hc₁ hO₁ hX₁).mpr (hni s (by omega)))
    exact ⟨G₂, hc₂.trans hc₁, hO₂.trans hO₁, hX₂.trans hX₁, fun z => (hm₂ z).trans (hm₁ z),
      hs₂, hmv₁.trans hmv₂⟩

end LabeledGrid

end OnLeConjecture.KnotTheory
