/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupBlocks
public import OnLeConjecture.KnotFloer.GridExteriorCyclicSeam
public import OnLeConjecture.KnotFloer.GridExteriorScissorSteps
public import OnLeConjecture.KnotTheory.EndpointCleanupSort

/-!
# Relocation of the auxiliary blocks

This file proves that the auxiliary `2 × 2` blocks of the cleanup of the scissor endpoint can be
moved to any position by grid moves, as in the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 10, "An auxiliary `2 × 2` block can then be placed at
the prescribed location by ordinary moves").

* `blockInsert_movesTo_blockInsert`: a single block inserted into any grid at the position `(c, q)`
  is related by grid moves to the block at any other position `(c', q')`. The grid of a block
  insertion is presented as a labeled grid (`blockLabeled`), and the columns and then the rows are
  sorted (`LabeledGrid.movesTo_withCols_of_inverted`, `LabeledGrid.movesTo_withRows_of_inverted`):
  every column or row of the block has its two markings in consecutive rows or columns, so it does
  not interleave any other column or row.
* `blockInsert_blockInsert_comm`: two block insertions commute, the second block lying south-west
  of the first.
* `FrameTower.exists_canonStack`: every frame tower is related by grid moves to the canonical stack
  with the same number of blocks.
* `CanonStack.fourMarkTower`: the canonical stack is a four-mark tower (`FourMarkTower`) whose
  blocks are all inserted at the column `0`, when the `X` marking of column `0` lies in row `0`.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

/-! ### Inserting two entries into a list -/

section InsTwo

variable {α : Type*}

/-- The list `l` with the two entries `x, y` inserted at the position `p`. -/
def insTwo (p : ℕ) (l : List α) (x y : α) : List α := l.take p ++ [x, y] ++ l.drop p

variable {p : ℕ} {l : List α} {x y : α}

theorem length_insTwo (hp : p ≤ l.length) : (insTwo p l x y).length = l.length + 2 := by
  simp [insTwo, List.length_take, List.length_drop]
  omega

theorem perm_insTwo : (insTwo p l x y).Perm (l ++ [x, y]) := by
  unfold insTwo
  have h : (l.take p ++ ([x, y] ++ l.drop p)).Perm (l.take p ++ (l.drop p ++ [x, y])) :=
    List.Perm.append_left _ List.perm_append_comm
  rw [← List.append_assoc, ← List.append_assoc, List.take_append_drop] at h
  exact h

theorem mem_insTwo {a : α} : a ∈ insTwo p l x y ↔ a ∈ l ∨ a = x ∨ a = y := by
  rw [perm_insTwo.mem_iff]
  simp

theorem getElem_insTwo_lt (hp : p ≤ l.length) {k : ℕ} (hk : k < p) :
    (insTwo p l x y)[k]'(by rw [length_insTwo hp]; omega) = l[k]'(by omega) := by
  simp only [insTwo, List.append_assoc]
  rw [List.getElem_append_left (by simp; omega)]
  simp

theorem getElem_insTwo_eq (hp : p ≤ l.length) :
    (insTwo p l x y)[p]'(by rw [length_insTwo hp]; omega) = x := by
  simp only [insTwo, List.append_assoc]
  rw [List.getElem_append_right (by simp)]
  all_goals simp [List.length_take, Nat.min_eq_left hp]

theorem getElem_insTwo_succ (hp : p ≤ l.length) :
    (insTwo p l x y)[p + 1]'(by rw [length_insTwo hp]; omega) = y := by
  simp only [insTwo, List.append_assoc]
  rw [List.getElem_append_right (by simp)]
  all_goals simp [List.length_take, Nat.min_eq_left hp]

theorem getElem_insTwo_ge (hp : p ≤ l.length) {k : ℕ} (hk : p + 2 ≤ k)
    (hk' : k < (insTwo p l x y).length) :
    (insTwo p l x y)[k] = l[k - 2]'(by rw [length_insTwo hp] at hk'; omega) := by
  have hlen : (l.take p).length = p := by simp [List.length_take, Nat.min_eq_left hp]
  simp only [insTwo, List.append_assoc]
  rw [List.getElem_append_right (by simp [hlen]; omega)]
  rw [List.getElem_append_right (by simp [hlen]; omega)]
  simp only [List.getElem_drop, List.length_cons, List.length_nil, hlen]
  congr 1
  omega

end InsTwo

/-! ### A single block as a labeled grid -/

section BlockLabeled

variable {n : ℕ}

/-- The base labels `0, …, n - 1` of a grid of size `n`, in order. -/
def baseLabels (n : ℕ) : List ℕ := List.range n

/-- The labels of a block insertion at the position `p`: the base labels with the block labels
`n` and `n + 1` inserted at `p`. -/
def insLabels (n p : ℕ) : List ℕ := insTwo p (baseLabels n) n (n + 1)

theorem length_insLabels {p : ℕ} (hp : p ≤ n) : (insLabels n p).length = n + 2 := by
  rw [insLabels, length_insTwo (by simpa [baseLabels] using hp)]
  simp [baseLabels]

theorem nodup_insLabels (p : ℕ) : (insLabels n p).Nodup := by
  rw [insLabels, perm_insTwo.nodup_iff]
  refine List.nodup_append.mpr ⟨List.nodup_range, by simp, ?_⟩
  intro a ha b hb
  simp only [baseLabels, List.mem_range] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

theorem mem_insLabels (p : ℕ) (a : ℕ) : a ∈ insLabels n p ↔ a < n + 2 := by
  rw [insLabels, mem_insTwo]
  simp only [baseLabels, List.mem_range]
  omega

theorem getElem_insLabels {p : ℕ} (hp : p ≤ n) {k : ℕ} (hk : k < (insLabels n p).length) :
    (insLabels n p)[k] =
      if k < p then k else if k = p then n else if k = p + 1 then n + 1 else k - 2 := by
  have hp' : p ≤ (baseLabels n).length := by simpa [baseLabels] using hp
  have hlen := length_insLabels hp
  split_ifs with h1 h2 h3
  · have e := getElem_insTwo_lt (x := n) (y := n + 1) hp' h1
    simp only [baseLabels, List.getElem_range] at e
    exact e
  · simp only [h2]; exact getElem_insTwo_eq hp'
  · simp only [h3]; exact getElem_insTwo_succ hp'
  · have e := getElem_insTwo_ge (x := n) (y := n + 1) hp' (k := k) (by omega) hk
    simp only [baseLabels, List.getElem_range] at e
    exact e

/-- Positions of the labels in `insLabels n p`. -/
theorem idxOf_insLabels {p : ℕ} (hp : p ≤ n) {a : ℕ} (ha : a < n + 2) :
    (insLabels n p).idxOf a =
      if a < n then blockShift p a else if a = n then p else p + 1 := by
  have hlen := length_insLabels (n := n) hp
  have key : ∀ k (hk : k < (insLabels n p).length), (insLabels n p)[k] = a →
      (insLabels n p).idxOf a = k := by
    intro k hk he
    rw [← he]
    exact (nodup_insLabels p).idxOf_getElem k hk
  split_ifs with h1 h2
  · unfold blockShift
    split_ifs with h3
    · exact key a (by omega) (by rw [getElem_insLabels hp]; simp [h3])
    · exact key (a + 2) (by omega) (by
        rw [getElem_insLabels hp, if_neg (by omega), if_neg (by omega), if_neg (by omega)]; rfl)
  · exact key p (by omega) (by rw [getElem_insLabels hp]; simp [h2])
  · exact key (p + 1) (by omega) (by rw [getElem_insLabels hp]; simp; omega)

/-- The `O` labels of a block insertion. -/
def blockLabelO (G : GridDiagram n) (a : ℕ) : ℕ := if h : a < n then (G.O ⟨a, h⟩).val else a

/-- The `X` labels of a block insertion. -/
def blockLabelX (G : GridDiagram n) (a : ℕ) : ℕ :=
  if h : a < n then (G.X ⟨a, h⟩).val else if a = n then n + 1 else n

/-- The grid of `blockInsert G c q` as a labeled grid: the base columns and rows are labeled by
`0, …, n - 1`, and the two columns and rows of the block by `n` and `n + 1`. -/
def blockLabeled (G : GridDiagram n) (c q : ℕ) (hc : c ≤ n) (hq : q ≤ n) :
    LabeledGrid (n + 2) ℕ ℕ where
  cols := insLabels n c
  rows := insLabels n q
  O := blockLabelO G
  X := blockLabelX G
  cols_length := length_insLabels hc
  rows_length := length_insLabels hq
  cols_nodup := nodup_insLabels c
  rows_nodup := nodup_insLabels q
  O_mem a ha := by
    rw [mem_insLabels] at ha ⊢
    unfold blockLabelO
    split_ifs with h
    · have := (G.O ⟨a, h⟩).isLt; omega
    · omega
  X_mem a ha := by
    rw [mem_insLabels] at ha ⊢
    unfold blockLabelX
    split_ifs with h
    · have := (G.X ⟨a, h⟩).isLt; omega
    · omega
    · omega
  O_inj a ha b hb h := by
    rw [mem_insLabels] at ha hb
    unfold blockLabelO at h
    split_ifs at h with h1 h2 h2
    · exact congrArg Fin.val (G.O.toPerm.injective (Fin.ext h))
    · have := (G.O ⟨a, h1⟩).isLt; omega
    · have := (G.O ⟨b, h2⟩).isLt; omega
    · exact h
  X_inj a ha b hb h := by
    rw [mem_insLabels] at ha hb
    unfold blockLabelX at h
    split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 <;> first
      | exact congrArg Fin.val (G.X.toPerm.injective (Fin.ext h))
      | omega
  O_ne_X a ha := by
    rw [mem_insLabels] at ha
    unfold blockLabelO blockLabelX
    split_ifs with h1 h2
    · intro h
      exact G.disjoint ⟨a, h1⟩ (Fin.ext h)
    · omega
    · omega

variable (G : GridDiagram n) {c q : ℕ} (hc : c ≤ n) (hq : q ≤ n)

theorem blockLabeled_O : (blockLabeled G c q hc hq).O = blockLabelO G := rfl

theorem blockLabeled_X : (blockLabeled G c q hc hq).X = blockLabelX G := rfl

/-- **The labeled presentation of a block insertion.** -/
theorem toGrid_blockLabeled :
    (blockLabeled G c q hc hq).toGrid = blockInsert G ⟨c, by omega⟩ ⟨q, by omega⟩ := by
  have hcol : ∀ k : Fin (n + 2), (blockLabeled G c q hc hq).colAt k =
      if k.val < c then k.val else if k.val = c then n else if k.val = c + 1 then n + 1
      else k.val - 2 := fun k => by
    rw [LabeledGrid.colAt]
    exact getElem_insLabels hc _
  have hrows : ∀ a, a < n + 2 → (blockLabeled G c q hc hq).rpos a =
      if a < n then blockShift q a else if a = n then q else q + 1 :=
    fun a ha => idxOf_insLabels hq ha
  apply gridDiagram_ext_gridRowVal
  · intro k hk
    rw [gridRowVal_blockInsert_O, gridRowVal_mk _ _ hk, LabeledGrid.toGrid_O_val, hcol]
    simp only
    by_cases h1 : k < c
    · have hb : blockBack c k = k := by unfold blockBack; rw [if_pos h1]
      rw [if_pos h1, if_neg (by omega), if_neg (by omega), if_pos hk, hb,
        gridRowVal_mk _ _ (by omega)]
      rw [blockLabeled_O]; unfold blockLabelO
      rw [dif_pos (by omega), hrows _ (by have := (G.O ⟨k, by omega⟩).isLt; omega),
        if_pos (G.O ⟨k, by omega⟩).isLt]
    · by_cases h2 : k = c
      · rw [if_neg h1, if_pos h2, if_pos h2]
        rw [blockLabeled_O]; unfold blockLabelO
        rw [dif_neg (by omega), hrows _ (by omega), if_neg (by omega), if_pos rfl]
      · by_cases h3 : k = c + 1
        · rw [if_neg h1, if_neg h2, if_pos h3, if_neg h2, if_pos h3]
          rw [blockLabeled_O]; unfold blockLabelO
          rw [dif_neg (by omega), hrows _ (by omega), if_neg (by omega), if_neg (by omega)]
        · have hb : blockBack c k = k - 2 := by unfold blockBack; rw [if_neg h1]
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h2, if_neg h3, if_pos hk, hb,
            gridRowVal_mk _ _ (by omega)]
          rw [blockLabeled_O]; unfold blockLabelO
          rw [dif_pos (by omega), hrows _ (by have := (G.O ⟨k - 2, by omega⟩).isLt; omega),
            if_pos (G.O ⟨k - 2, by omega⟩).isLt]
  · intro k hk
    rw [gridRowVal_blockInsert_X, gridRowVal_mk _ _ hk, LabeledGrid.toGrid_X_val, hcol]
    simp only
    by_cases h1 : k < c
    · have hb : blockBack c k = k := by unfold blockBack; rw [if_pos h1]
      rw [if_pos h1, if_neg (by omega), if_neg (by omega), if_pos hk, hb,
        gridRowVal_mk _ _ (by omega)]
      rw [blockLabeled_X]; unfold blockLabelX
      rw [dif_pos (by omega), hrows _ (by have := (G.X ⟨k, by omega⟩).isLt; omega),
        if_pos (G.X ⟨k, by omega⟩).isLt]
    · by_cases h2 : k = c
      · rw [if_neg h1, if_pos h2, if_pos h2]
        rw [blockLabeled_X]; unfold blockLabelX
        rw [dif_neg (by omega), if_pos rfl, hrows _ (by omega), if_neg (by omega),
          if_neg (by omega)]
      · by_cases h3 : k = c + 1
        · rw [if_neg h1, if_neg h2, if_pos h3, if_neg h2, if_pos h3]
          rw [blockLabeled_X]; unfold blockLabelX
          rw [dif_neg (by omega), if_neg (by omega), hrows _ (by omega), if_neg (by omega),
            if_pos rfl]
        · have hb : blockBack c k = k - 2 := by unfold blockBack; rw [if_neg h1]
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h2, if_neg h3, if_pos hk, hb,
            gridRowVal_mk _ _ (by omega)]
          rw [blockLabeled_X]; unfold blockLabelX
          rw [dif_pos (by omega), hrows _ (by have := (G.X ⟨k - 2, by omega⟩).isLt; omega),
            if_pos (G.X ⟨k - 2, by omega⟩).isLt]

end BlockLabeled


/-! ### Moving one block -/

section MoveBlock

variable {n : ℕ}

theorem perm_insLabels (p p' : ℕ) : (insLabels n p').Perm (insLabels n p) :=
  perm_insTwo.trans perm_insTwo.symm

/-- The positions of two base labels are in the order of the labels. -/
theorem idxOf_insLabels_lt_iff {p : ℕ} (hp : p ≤ n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    (insLabels n p).idxOf a < (insLabels n p).idxOf b ↔ a < b := by
  rw [idxOf_insLabels hp (by omega), idxOf_insLabels hp (by omega), if_pos ha, if_pos hb]
  unfold blockShift
  split_ifs <;> omega

/-- In a reordering between two block positions, an inverted pair consists of a base label and a
block label. -/
theorem inverted_insLabels {p p' : ℕ} (hp : p ≤ n) (hp' : p' ≤ n) {a b : ℕ} (ha : a < n + 2)
    (hb : b < n + 2) (h1 : (insLabels n p).idxOf a < (insLabels n p).idxOf b)
    (h2 : (insLabels n p').idxOf b < (insLabels n p').idxOf a) :
    (a < n ∧ n ≤ b) ∨ (n ≤ a ∧ b < n) := by
  by_cases ha' : a < n <;> by_cases hb' : b < n
  · exact absurd ((idxOf_insLabels_lt_iff hp' hb' ha').mp h2)
      (not_lt.mpr ((idxOf_insLabels_lt_iff hp ha' hb').mp h1).le)
  · exact Or.inl ⟨ha', by omega⟩
  · exact Or.inr ⟨by omega, hb'⟩
  · exfalso
    rw [idxOf_insLabels hp ha, idxOf_insLabels hp hb] at h1
    rw [idxOf_insLabels hp' ha, idxOf_insLabels hp' hb] at h2
    simp only [if_neg ha', if_neg hb'] at h1 h2
    split_ifs at h1 h2 <;> omega

/-- **Relocation of one block.** A block inserted into a grid at the position `(c, q)` is related
by grid moves to the block inserted at any other position `(c', q')`. -/
theorem blockInsert_movesTo_blockInsert (G : GridDiagram n) {c q c' q' : ℕ} (hc : c ≤ n)
    (hq : q ≤ n) (hc' : c' ≤ n) (hq' : q' ≤ n) :
    (blockInsert G ⟨c, by omega⟩ ⟨q, by omega⟩).MovesTo
      (blockInsert G ⟨c', by omega⟩ ⟨q', by omega⟩) := by
  rw [← toGrid_blockLabeled G hc hq, ← toGrid_blockLabeled G hc' hq']
  set L := blockLabeled G c q hc hq with hL
  have hrpos : ∀ a, a < n + 2 → L.rpos a =
      if a < n then blockShift q a else if a = n then q else q + 1 :=
    fun a ha => idxOf_insLabels hq ha
  have hOlt : ∀ a, a < n → blockLabelO G a < n := fun a ha => by
    unfold blockLabelO; rw [dif_pos ha]; exact (G.O ⟨a, ha⟩).isLt
  have hXlt : ∀ a, a < n → blockLabelX G a < n := fun a ha => by
    unfold blockLabelX; rw [dif_pos ha]; exact (G.X ⟨a, ha⟩).isLt
  -- sort the columns
  have hm1 := L.movesTo_withCols_of_inverted (insLabels n c') (perm_insLabels c c')
    (fun a ha b hb h1 h2 => by
      have ha2 : a < n + 2 := (mem_insLabels c a).mp ha
      have hb2 : b < n + 2 := (mem_insLabels c b).mp hb
      have key : ∀ x y, x < n + 2 → y < n + 2 → n ≤ x → y < n → L.ColsNonint x y := by
        intro x y hx hy hxn hyn
        have hxm : x ∈ L.cols := (mem_insLabels c x).mpr hx
        have hym : y ∈ L.cols := (mem_insLabels c y).mpr hy
        have hOx : L.O x = x := by
          change blockLabelO G x = x; unfold blockLabelO; rw [dif_neg (by omega)]
        have hXx : L.X x = if x = n then n + 1 else n := by
          change blockLabelX G x = _; unfold blockLabelX; rw [dif_neg (by omega)]
        have hOy : L.O y < n := hOlt y hyn
        have hXy : L.X y < n := hXlt y hyn
        refine L.colsNonint_of_short hxm hym ?_ (by omega) ?_ (by omega) ?_
        · rw [hOx, hXx, hrpos _ hx, hrpos _ (by split_ifs <;> omega)]
          split_ifs <;> omega
        · rw [hXx]; split_ifs <;> omega
        · rw [hXx]; split_ifs <;> omega
      rcases inverted_insLabels hc hc' ha2 hb2 h1 h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact (L.colsNonint_comm).mp (key b a hb2 ha2 h4 h3)
      · exact key a b ha2 hb2 h3 h4)
  set L₁ := L.withCols (insLabels n c') (perm_insLabels c c')
  have hcpos : ∀ a, a < n + 2 → L₁.cpos a =
      if a < n then blockShift c' a else if a = n then c' else c' + 1 :=
    fun a ha => idxOf_insLabels hc' ha
  -- sort the rows
  have hm2 := L₁.movesTo_withRows_of_inverted (insLabels n q') (perm_insLabels q q')
    (fun a ha b hb h1 h2 => by
      have ha2 : a < n + 2 := (mem_insLabels q a).mp ha
      have hb2 : b < n + 2 := (mem_insLabels q b).mp hb
      have key : ∀ x y, x < n + 2 → y < n + 2 → n ≤ x → y < n → L₁.RowsNonint x y := by
        intro x y hx hy hxn hyn
        have hxm : x ∈ L₁.cols := (mem_insLabels c' x).mpr hx
        have hx'm : (if x = n then n + 1 else n) ∈ L₁.cols :=
          (mem_insLabels c' _).mpr (by split_ifs <;> omega)
        have hOx : L₁.O x = x := by
          change blockLabelO G x = x; unfold blockLabelO; rw [dif_neg (by omega)]
        have hXx' : L₁.X (if x = n then n + 1 else n) = x := by
          change blockLabelX G _ = x; unfold blockLabelX
          split_ifs <;> omega
        refine L₁.rowsNonint_of_short hxm hx'm hOx hXx' ?_ (by omega) ?_ ?_
        · rw [hcpos _ hx, hcpos _ (by split_ifs <;> omega)]
          split_ifs <;> omega
        · change y ≠ blockLabelO G _; unfold blockLabelO; split_ifs <;> omega
        · change y ≠ blockLabelX G x; unfold blockLabelX; split_ifs <;> omega
      rcases inverted_insLabels hq hq' ha2 hb2 h1 h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact (L₁.rowsNonint_comm).mp (key b a hb2 ha2 h4 h3)
      · exact key a b ha2 hb2 h3 h4)
  have he : (L₁.withRows (insLabels n q') (perm_insLabels q q')).toGrid =
      (blockLabeled G c' q' hc' hq').toGrid :=
    LabeledGrid.toGrid_eq_of_data _ _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
  rw [← he]
  exact hm1.trans hm2

end MoveBlock


/-! ### Commuting two block insertions -/

/-- Two block insertions commute, on natural numbers. -/
theorem blockFun_blockFun_comm (f : ℕ → ℕ) {N c q u v i j u' v' k : ℕ} (hcN : c ≤ N) (hic : i ≤ c)
    (hjq : j ≤ q) (hu : q ≤ u) (hv : q ≤ v) (hu' : u' < j + 2) (hv' : v' < j + 2) :
    blockFun (blockFun f N c q u v) (N + 2) i j u' v' k =
      blockFun (blockFun f N i j u' v') (N + 2) (c + 2) (q + 2) (u + 2) (v + 2) k := by
  unfold blockFun
  by_cases h1 : k = i
  · have hb : blockBack (c + 2) k = i := by unfold blockBack; split_ifs <;> omega
    simp only [if_pos h1, if_neg (show k ≠ c + 2 by omega), if_neg (show k ≠ c + 2 + 1 by omega),
      hb, ↓reduceIte]
    rw [if_pos (by omega)]
    unfold blockShift; rw [if_pos (by omega)]
  · by_cases h2 : k = i + 1
    · have hb : blockBack (c + 2) k = i + 1 := by unfold blockBack; split_ifs <;> omega
      simp only [if_neg h1, if_pos h2, if_neg (show k ≠ c + 2 by omega),
        if_neg (show k ≠ c + 2 + 1 by omega), hb, if_neg (show i + 1 ≠ i by omega), ↓reduceIte]
      rw [if_pos (by omega)]
      unfold blockShift; rw [if_pos (by omega)]
    · by_cases h3 : k = c + 2
      · have hb : blockBack i k = c := by unfold blockBack; split_ifs <;> omega
        simp only [if_neg h1, if_neg h2, if_pos h3, hb, ↓reduceIte]
        rw [if_pos (by omega)]
        unfold blockShift; rw [if_neg (by omega)]
      · by_cases h4 : k = c + 2 + 1
        · have hb : blockBack i k = c + 1 := by unfold blockBack; split_ifs <;> omega
          simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4, hb,
            if_neg (show c + 1 ≠ c by omega), ↓reduceIte]
          rw [if_pos (by omega)]
          unfold blockShift; rw [if_neg (by omega)]
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          by_cases h5 : k < N + 2 + 2
          · have hb1 : blockBack i k ≠ c := by unfold blockBack; split_ifs <;> omega
            have hb2 : blockBack i k ≠ c + 1 := by unfold blockBack; split_ifs <;> omega
            have hb3 : blockBack (c + 2) k ≠ i := by unfold blockBack; split_ifs <;> omega
            have hb4 : blockBack (c + 2) k ≠ i + 1 := by unfold blockBack; split_ifs <;> omega
            have hb5 : blockBack c (blockBack i k) = blockBack i (blockBack (c + 2) k) := by
              unfold blockBack; split_ifs <;> omega
            simp only [if_pos h5, if_neg hb1, if_neg hb2, if_neg hb3, if_neg hb4,
              if_pos (show blockBack i k < N + 2 by unfold blockBack; split_ifs <;> omega),
              if_pos (show blockBack (c + 2) k < N + 2 by unfold blockBack; split_ifs <;> omega),
              hb5]
            generalize f (blockBack i (blockBack (c + 2) k)) = w
            unfold blockShift
            split_ifs <;> omega
          · simp only [if_neg h5]

/-- **Two block insertions commute.** A block inserted south-west of an earlier block can be
inserted first. -/
theorem blockInsert_blockInsert_comm {n : ℕ} (G : GridDiagram n) {c q i j : ℕ} (hcn : c ≤ n)
    (hqn : q ≤ n) (hic : i ≤ c) (hjq : j ≤ q) :
    blockInsert (blockInsert G ⟨c, by omega⟩ ⟨q, by omega⟩) ⟨i, by omega⟩ ⟨j, by omega⟩ =
      blockInsert (blockInsert G ⟨i, by omega⟩ ⟨j, by omega⟩) ⟨c + 2, by omega⟩
        ⟨q + 2, by omega⟩ := by
  apply gridDiagram_ext_gridRowVal
  · intro k _
    rw [gridRowVal_blockInsert_O_eq, gridRowVal_blockInsert_O_eq, gridRowVal_blockInsert_O_eq,
      gridRowVal_blockInsert_O_eq]
    exact blockFun_blockFun_comm _ hcn hic hjq le_rfl (by omega) (by omega) (by omega)
  · intro k _
    rw [gridRowVal_blockInsert_X_eq, gridRowVal_blockInsert_X_eq, gridRowVal_blockInsert_X_eq,
      gridRowVal_blockInsert_X_eq]
    exact blockFun_blockFun_comm _ hcn hic hjq (by omega) le_rfl (by omega) (by omega)

/-! ### Relocation of a frame tower to the canonical stack -/

/-- Grids that agree as elements of `Σ k, GridDiagram k` have equal block insertions at the same
positions. -/
theorem blockInsert_sigma_congr {b b' : ℕ} {X : GridDiagram (b + 1)} {X' : GridDiagram (b' + 1)}
    (h : (⟨b + 1, X⟩ : Σ k, GridDiagram k) = ⟨b' + 1, X'⟩) {c q : ℕ} (hc : c ≤ b + 1)
    (hq : q ≤ b + 1) :
    (⟨b + 1 + 2, blockInsert X ⟨c, by omega⟩ ⟨q, by omega⟩⟩ : Σ k, GridDiagram k) =
      ⟨b' + 1 + 2, blockInsert X' ⟨c, by
        have := (Sigma.mk.inj_iff.mp h).1; omega⟩ ⟨q, by
        have := (Sigma.mk.inj_iff.mp h).1; omega⟩⟩ := by
  obtain ⟨hb, hX⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : b = b' := by omega
  obtain rfl := eq_of_heq hX
  rfl

/-- **A block below a canonical stack.** If `X` is the canonical stack with `U` blocks over the
block insertion of `G` at the position `(c, q)`, then `X` is the block insertion at the position
`(c + 2 U, q + 2 U)` into the canonical stack with `U` blocks over `G`. -/
theorem CanonStack.commute {b : ℕ} {G : GridDiagram (b + 1)} {c q : ℕ} (hc : c ≤ b + 1)
    (hq : q ≤ b + 1) {U b₁ : ℕ} {X : GridDiagram (b₁ + 1)}
    (h : CanonStack (blockInsert G ⟨c, by omega⟩ ⟨q, by omega⟩) U X) :
    ∃ (b₀ : ℕ) (X₀ : GridDiagram (b₀ + 1)) (hc₀ : c + 2 * U ≤ b₀ + 1)
      (hq₀ : q + 2 * U ≤ b₀ + 1), CanonStack G U X₀ ∧
      (⟨b₁ + 1, X⟩ : Σ k, GridDiagram k) =
        ⟨b₀ + 1 + 2, blockInsert X₀ ⟨c + 2 * U, by omega⟩ ⟨q + 2 * U, by omega⟩⟩ := by
  induction h with
  | base => exact ⟨b, G, by omega, by omega, CanonStack.base, rfl⟩
  | @insert U b₂ X₁ h₁ hk ih =>
    obtain ⟨b₀, X₀, hc₀, hq₀, hX₀, e⟩ := ih
    have hs := hX₀.size
    have hs₁ := h₁.size
    refine ⟨b₀ + 2, blockInsert X₀ ⟨2 * U, by omega⟩ ⟨2 * U, by omega⟩, by omega, by omega,
      hX₀.insert (by omega), ?_⟩
    rw [blockInsert_sigma_congr e (by omega) (by omega),
      blockInsert_blockInsert_comm X₀ (by omega) (by omega) (by omega) (by omega)]
    congr 2

/-- **Relocation.** Every frame tower followed by a canonical stack is related by grid moves to a
canonical stack over the base of the tower, with all the blocks. -/
theorem FrameTower.exists_canonStack_of {a : ℕ} {T : GridDiagram (a + 1)} {k b : ℕ}
    {G : GridDiagram (b + 1)} (h : FrameTower T k G) :
    ∀ {U b' : ℕ} {X : GridDiagram (b' + 1)}, CanonStack G U X →
      ∃ (b'' : ℕ) (Y : GridDiagram (b'' + 1)), CanonStack T (U + k) Y ∧ X.MovesTo Y := by
  induction h with
  | base => exact fun hX => ⟨_, _, hX, GridDiagram.MovesTo.refl _⟩
  | @insert k b₀ G₀ h₀ c q hc hcb hq hqb ih =>
    intro U b' X hX
    obtain ⟨b₁, X₀, hc₀, hq₀, hX₀, e⟩ := CanonStack.commute (G := G₀) (by omega) (by omega) hX
    have hs := hX₀.size
    obtain ⟨b'', Y, hY, hm⟩ := ih (hX₀.insert (by omega))
    refine ⟨b'', Y, by rw [show U + (k + 1) = U + 1 + k by omega]; exact hY, ?_⟩
    refine (movesTo_of_sigma_eq e).trans ((blockInsert_movesTo_blockInsert X₀ (by omega)
      (by omega) (by omega) (by omega)).trans hm)

/-- **Relocation of a frame tower.** Every frame tower is related by grid moves to the canonical
stack with the same number of blocks over the same base. -/
theorem FrameTower.exists_canonStack {a : ℕ} {T : GridDiagram (a + 1)} {k b : ℕ}
    {G : GridDiagram (b + 1)} (h : FrameTower T k G) :
    ∃ (b' : ℕ) (Y : GridDiagram (b' + 1)), CanonStack T k Y ∧ G.MovesTo Y := by
  obtain ⟨b', Y, hY, hm⟩ := h.exists_canonStack_of CanonStack.base
  exact ⟨b', Y, by simpa using hY, hm⟩

/-! ### The canonical stack as a four-mark tower -/

/-- A four-mark insertion is the block insertion at the column `c` and the row of its `X`
marking. -/
theorem isFourMarkInsertion_iff_blockInsert {n : ℕ} (G : GridDiagram n) (c : Fin n)
    (G' : GridDiagram (n + 2)) :
    IsFourMarkInsertion G c G' ↔ G' = blockInsert G c.castSucc (G.X c).castSucc := by
  constructor
  · rintro ⟨hO, hX⟩
    ext1
    · exact hO
    · exact hX
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- **A canonical stack as a four-mark tower.** If the `X` marking of column `0` lies in row `0`,
then the canonical stack is a four-mark tower whose blocks are all inserted at the column `0`. -/
theorem CanonStack.fourMarkTower {a : ℕ} {T : GridDiagram (a + 1)} (hT : T.X 0 = 0) {k b : ℕ}
    {G : GridDiagram (b + 1)} (h : CanonStack T k G) :
    ∃ e : Fin (a + 1) → Fin (b + 1), FourMarkTower T k G e ∧ (e 0).val = 2 * k ∧
      (G.X (e 0)).val = 2 * k := by
  induction h with
  | base => exact ⟨id, FourMarkTower.base, rfl, by simp [hT]⟩
  | @insert k b G h' hk ih =>
    obtain ⟨e, he, he0, hX0⟩ := ih
    have hc : (e 0).castSucc = (⟨2 * k, by omega⟩ : Fin (b + 1 + 1)) := Fin.ext (by simp [he0])
    have hq : (G.X (e 0)).castSucc = (⟨2 * k, by omega⟩ : Fin (b + 1 + 1)) :=
      Fin.ext (by simp [hX0])
    have hins : IsFourMarkInsertion G (e 0)
        (blockInsert G ⟨2 * k, by omega⟩ ⟨2 * k, by omega⟩) := by
      rw [isFourMarkInsertion_iff_blockInsert, hc, hq]
    refine ⟨_, FourMarkTower.insert he 0 hins, ?_, ?_⟩
    · rw [val_succAbove_eq_natSuccAbove, val_succAbove_eq_natSuccAbove]
      simp only [Fin.val_succ, Fin.val_castSucc, he0]
      unfold natSuccAbove
      split_ifs <;> omega
    · have hv : ((e 0).castSucc.succ.succAbove ((e 0).castSucc.succAbove (e 0))).val =
          2 * k + 2 := by
        rw [val_succAbove_eq_natSuccAbove, val_succAbove_eq_natSuccAbove]
        simp only [Fin.val_succ, Fin.val_castSucc, he0]
        unfold natSuccAbove
        split_ifs <;> omega
      have hbb : blockBack (2 * k) (2 * k + 2) = 2 * k := by unfold blockBack; split_ifs <;> omega
      have hX0' : gridRowVal G.X (2 * k) = 2 * k := by
        have := gridRowVal_val G.X (e 0)
        rw [he0, hX0] at this
        exact this
      have h1 := gridRowVal_blockInsert_X G ⟨2 * k, by omega⟩ ⟨2 * k, by omega⟩ (2 * k + 2)
      simp only [hbb, hX0'] at h1
      have h2 : gridRowVal (blockInsert G ⟨2 * k, by omega⟩ ⟨2 * k, by omega⟩).X (2 * k + 2) =
          2 * k + 2 := by
        rw [h1]
        unfold blockShift
        split_ifs <;> omega
      rw [← gridRowVal_val, hv, h2]
      ring

end OnLeConjecture.KnotFloer.GridFull
