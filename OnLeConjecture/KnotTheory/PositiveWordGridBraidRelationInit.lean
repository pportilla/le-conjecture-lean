/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationMatching

/-! # The initial grid of a word with a block of three letters

For a word `w` and a key `κ` on the corners of `w`, `cornerGrid w κ` is the labeled grid whose
column and row labels are the corners of `w`, with columns in the standard order, rows sorted by
`κ`, `O`-markings on the identity and `X`-markings on the inverse of the cyclic matching. It is an
admissible grid of `w` when `κ` refines the arc rows (`cornerGrid_admissible`).

For a word `B ++ t` with a block `B` of three letters and a window state `S` satisfying the
finite checks `BraidWindow.InitOK`, the relabeled grid `BraidWindow.initGrid` realizes `S`
(`BraidWindow.initGrid_real`) and is related to `wordGrid (B ++ t)` by grid moves
(`BraidWindow.initGrid_movesTo`). This is the initial window of
`docs/route-n/J09-word-grid-moves.tex`, Proposition *braid*. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-! ### Corner grids -/

section CornerGrid

variable {m : ℕ} (w : PositiveAdjacentWord m)

/-- The corners of a word in the standard column order. -/
def cornerCols : List (Fin w.length × Fin 3) :=
  (List.finRange (w.length * 3)).map finProdFinEquiv.symm

theorem mem_cornerCols (p : Fin w.length × Fin 3) : p ∈ cornerCols w :=
  List.mem_map.mpr ⟨finProdFinEquiv p, List.mem_finRange _, by simp⟩

theorem cornerCols_nodup : (cornerCols w).Nodup :=
  (List.nodup_finRange _).map finProdFinEquiv.symm.injective

theorem cornerCols_length : (cornerCols w).length = w.length * 3 := by simp [cornerCols]

variable (κ : Fin w.length × Fin 3 → ℕ)

/-- The corners of a word sorted by a key. -/
def cornerRows : List (Fin w.length × Fin 3) :=
  (cornerCols w).mergeSort (fun a b => decide (κ a ≤ κ b))

theorem mem_cornerRows (p : Fin w.length × Fin 3) : p ∈ cornerRows w κ := by
  rw [cornerRows, List.mem_mergeSort]; exact mem_cornerCols w p

theorem cornerRows_nodup : (cornerRows w κ).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (cornerCols_nodup w)

theorem cornerRows_sorted : (cornerRows w κ).Pairwise (fun a b => κ a ≤ κ b) := by
  have := List.pairwise_mergeSort (le := fun a b => decide (κ a ≤ κ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (cornerCols w)
  exact this.imp (fun h => by simpa using h)

/-- The corner grid of a word with rows sorted by a key. -/
def cornerGrid : LabeledGrid (w.length * 3) (Fin w.length × Fin 3) (Fin w.length × Fin 3) where
  cols := cornerCols w
  rows := cornerRows w κ
  O := id
  X := (positiveRectilinearWordMatching w).symm
  cols_length := cornerCols_length w
  rows_length := by rw [cornerRows, List.length_mergeSort, cornerCols_length]
  cols_nodup := cornerCols_nodup w
  rows_nodup := cornerRows_nodup w κ
  O_mem c _ := mem_cornerRows w κ c
  X_mem c _ := mem_cornerRows w κ _
  O_inj a _ b _ h := h
  X_inj a _ b _ h := (positiveRectilinearWordMatching w).symm.injective h
  O_ne_X c _ h := by
    apply positiveRectilinearWordMatching_ne_self w c
    have h' : c = (positiveRectilinearWordMatching w).symm c := h
    conv_lhs => rw [h']
    exact Equiv.apply_symm_apply _ _

theorem cornerGrid_colAt (k : Fin (w.length * 3)) :
    (cornerGrid w κ).colAt k = finProdFinEquiv.symm k := by
  simp [LabeledGrid.colAt, cornerGrid, cornerCols]

/-- Twice the arc row of a corner, as a natural number. -/
def lvl2 (p : Fin w.length × Fin 3) : ℕ :=
  2 * (w[p.1.val]).val + if p.2 = 0 then 1 else if p.2 = 1 then 0 else 2

theorem two_mul_arcRow (p : Fin w.length × Fin 3) :
    2 * positiveRectilinearWordArcRow w p = (lvl2 w p : ℝ) := by
  obtain ⟨h, c⟩ := p
  rw [positiveRectilinearWordArcRow, ← positiveRectilinearOutgoingArc_row]
  fin_cases c
  · simp [positiveRectilinearHorizontalArcRow, lvl2]; ring
  · simp [positiveRectilinearHorizontalArcRow, adjacentLower, lvl2]
  · simp [positiveRectilinearHorizontalArcRow, adjacentUpper, lvl2]; ring

theorem lvl2_lt_of_arcRow_lt {p q : Fin w.length × Fin 3}
    (h : positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q) :
    lvl2 w p < lvl2 w q := by
  have h2 : 2 * positiveRectilinearWordArcRow w p < 2 * positiveRectilinearWordArcRow w q := by
    linarith
  rw [two_mul_arcRow, two_mul_arcRow] at h2
  exact_mod_cast h2

/-- A corner grid whose key refines the arc rows is admissible. -/
theorem cornerGrid_admissible
    (hmono : ∀ p q, lvl2 w p < lvl2 w q → κ p < κ q) :
    IsAdmissibleWordGrid w (cornerGrid w κ).toGrid where
  X_eq a := by
    apply Fin.ext
    rw [LabeledGrid.toGrid_X_val, LabeledGrid.toGrid_O_val, cornerGrid_colAt, cornerGrid_colAt]
    simp [cornerGrid]
  O_lt_of_arcRow_lt a b h := by
    rw [Fin.lt_def, LabeledGrid.toGrid_O_val, LabeledGrid.toGrid_O_val, cornerGrid_colAt,
      cornerGrid_colAt]
    simp only [Equiv.symm_apply_apply]
    change (cornerGrid w κ).rpos a < (cornerGrid w κ).rpos b
    exact idxOf_lt_of_level (cornerRows_sorted w κ) (mem_cornerRows w κ a)
      (mem_cornerRows w κ b) (hmono a b (lvl2_lt_of_arcRow_lt w h))

end CornerGrid

namespace BraidWindow

/-! ### Finite checks on an initial window state -/

/-- The position in the window of the corner `(h, c)`. -/
def cidx (h : ℕ) (c : Fin 3) : ℕ := 3 * h + c.val

/-- The corner of a window position. -/
def kc (k : ℕ) : ℕ × Fin 3 := (k / 3, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩)

theorem kc_cidx (h : ℕ) (c : Fin 3) : kc (cidx h c) = (h, c) := by
  have := c.isLt
  simp only [kc, cidx, Prod.mk.injEq]
  exact ⟨by omega, Fin.ext (by simp)⟩

theorem cidx_kc (k : ℕ) : cidx (kc k).1 (kc k).2 = k := by
  simp only [kc, cidx]; omega

theorem cidx_lt {h : ℕ} (hh : h < 3) (c : Fin 3) : cidx h c < 9 := by
  have := c.isLt; simp only [cidx]; omega

theorem kc_lt {k : ℕ} (hk : k < 9) : (kc k).1 < 3 := by simp only [kc]; omega

/-- The corners of a block of three letters. -/
def corners9 : List (ℕ × Fin 3) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

theorem mem_corners9 {h : ℕ} (hh : h < 3) (c : Fin 3) : (h, c) ∈ corners9 := by
  interval_cases h <;> fin_cases c <;> simp [corners9]

theorem lt_of_mem_corners9 {p : ℕ × Fin 3} (hp : p ∈ corners9) : p.1 < 3 := by
  simp only [corners9, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The `O`-labels of the window columns. -/
def Ol (S : WState) : List ℕ := S.cols.map Prod.fst

/-- The `X`-labels of the window columns. -/
def Xl (S : WState) : List ℕ := S.cols.map Prod.snd

/-- Twice the relative level of the arc leaving the corner `(h, c)`. -/
def outLvl (offs : List ℕ) (h : ℕ) (c : Fin 3) : ℕ :=
  2 * offs.getD h 0 + if c = 0 then 1 else if c = 1 then 0 else 2

/-- Twice the relative level of the arc entering the corner `(h, c)`. -/
def inLvl (offs : List ℕ) (h : ℕ) (c : Fin 3) : ℕ :=
  2 * offs.getD h 0 + if c = 0 then 0 else if c = 1 then 2 else 1

/-- The relative rank of the integer arc entering the corner `(h, c)`. -/
def inRel (offs : List ℕ) (h : ℕ) (c : Fin 3) : ℕ := offs.getD h 0 + if c = 1 then 1 else 0

/-- Twice the relative level of a window label. -/
def lvlRel (S : WState) (offs : List ℕ) (x : ℕ) : ℕ :=
  if x ∈ Ol S then outLvl offs (kc ((Ol S).idxOf x)).1 (kc ((Ol S).idxOf x)).2
  else inLvl offs (kc ((Xl S).idxOf x)).1 (kc ((Xl S).idxOf x)).2

/-- The flag of a relative rank. -/
def flagOf (flags : List Bool) (e : ℕ) : Bool := flags.getD e false

/-- The check of a block corner against the block matching `BM`. -/
def bmOK (S : WState) (offs : List ℕ) (flags : List Bool) (p : ℕ × Fin 3) : Bool :=
  match BM offs (flagOf flags) p.1 p.2 with
  | some q => decide (q.1 < 3) && (S.col (cidx q.1 q.2)).2 == (S.col (cidx p.1 p.2)).1
  | none => (S.col (cidx p.1 p.2)).1 == 30 + rankOff offs p.1 p.2

/-- The finite checks on an initial window state `S` of a block with rank offsets `offs` and
flags `flags` of the ranks occurring outside the block. -/
def InitOK (S : WState) (offs : List ℕ) (flags : List Bool) : Prop :=
  S.cols.length = 9 ∧ (Ol S).Nodup ∧ (Xl S).Nodup ∧ S.rows.Nodup ∧ S.rows.length < 16 ∧
  (∀ p ∈ corners9, (S.col (cidx p.1 p.2)).1 ∈ S.rows ∧ (S.col (cidx p.1 p.2)).2 ∈ S.rows) ∧
  (∀ x ∈ S.rows, x ∈ Ol S ∨ x ∈ Xl S) ∧
  (∀ p ∈ corners9, bmOK S offs flags p = true) ∧
  (∀ p ∈ corners9, ∀ p' ∈ corners9, (S.col (cidx p.1 p.2)).2 = (S.col (cidx p'.1 p'.2)).1 →
    BM offs (flagOf flags) p'.1 p'.2 = some p) ∧
  (∀ p ∈ corners9, (S.col (cidx p.1 p.2)).2 ∉ Ol S →
    (S.col (cidx p.1 p.2)).2 = 20 + inRel offs p.1 p.2) ∧
  S.rows.Pairwise (fun a b => lvlRel S offs a ≤ lvlRel S offs b)

instance (S : WState) (offs : List ℕ) (flags : List Bool) : Decidable (InitOK S offs flags) := by
  unfold InitOK; infer_instance

/-! ### Labels of the window columns -/

theorem col_eq_getElem (S : WState) {k : ℕ} (hk : k < S.cols.length) :
    S.col k = S.cols[k] := by
  simp [WState.col, List.getD_eq_getElem?_getD, hk]

theorem ol_getElem (S : WState) {k : ℕ} (hk : k < S.cols.length) :
    (Ol S)[k]'(by simp [Ol, hk]) = (S.col k).1 := by
  simp [Ol, col_eq_getElem S hk]

theorem xl_getElem (S : WState) {k : ℕ} (hk : k < S.cols.length) :
    (Xl S)[k]'(by simp [Xl, hk]) = (S.col k).2 := by
  simp [Xl, col_eq_getElem S hk]

theorem mem_ol (S : WState) {k : ℕ} (hk : k < S.cols.length) : (S.col k).1 ∈ Ol S := by
  rw [← ol_getElem S hk]; exact List.getElem_mem _

theorem mem_xl (S : WState) {k : ℕ} (hk : k < S.cols.length) : (S.col k).2 ∈ Xl S := by
  rw [← xl_getElem S hk]; exact List.getElem_mem _

theorem ol_idxOf (S : WState) (hn : (Ol S).Nodup) {k : ℕ} (hk : k < S.cols.length) :
    (Ol S).idxOf (S.col k).1 = k := by
  rw [← ol_getElem S hk]; exact List.Nodup.idxOf_getElem hn _ _

theorem xl_idxOf (S : WState) (hn : (Xl S).Nodup) {k : ℕ} (hk : k < S.cols.length) :
    (Xl S).idxOf (S.col k).2 = k := by
  rw [← xl_getElem S hk]; exact List.Nodup.idxOf_getElem hn _ _

theorem exists_of_mem_ol (S : WState) {x : ℕ} (hx : x ∈ Ol S) :
    (Ol S).idxOf x < S.cols.length ∧ (S.col ((Ol S).idxOf x)).1 = x := by
  have h1 : (Ol S).idxOf x < (Ol S).length := List.idxOf_lt_length_iff.mpr hx
  have h1' : (Ol S).idxOf x < S.cols.length := by simpa [Ol] using h1
  refine ⟨h1', ?_⟩
  rw [← ol_getElem S h1']; exact List.getElem_idxOf h1

theorem exists_of_mem_xl (S : WState) {x : ℕ} (hx : x ∈ Xl S) :
    (Xl S).idxOf x < S.cols.length ∧ (S.col ((Xl S).idxOf x)).2 = x := by
  have h1 : (Xl S).idxOf x < (Xl S).length := List.idxOf_lt_length_iff.mpr hx
  have h1' : (Xl S).idxOf x < S.cols.length := by simpa [Xl] using h1
  refine ⟨h1', ?_⟩
  rw [← xl_getElem S h1']; exact List.getElem_idxOf h1

/-! ### The initial grid -/

section InitGrid

variable {m : ℕ} (w : PositiveAdjacentWord m) (S : WState)

/-- The corner with given coordinates, clamped to the word. -/
def cornerOf (hL : 0 < w.length) (q : ℕ × Fin 3) : Fin w.length × Fin 3 :=
  (⟨min q.1 (w.length - 1), by omega⟩, q.2)

theorem cornerOf_eq (hL : 0 < w.length) {q : ℕ × Fin 3} (hq : q.1 < w.length) :
    cornerOf w hL q = (⟨q.1, hq⟩, q.2) := by
  simp only [cornerOf, Prod.mk.injEq, Fin.mk.injEq, and_true]; omega

theorem cornerOf_self (hL : 0 < w.length) (p : Fin w.length × Fin 3) :
    cornerOf w hL (p.1.val, p.2) = p := cornerOf_eq w hL p.1.isLt

/-- The column label of a corner: window positions for the first three letters. -/
def fCol (p : Fin w.length × Fin 3) : BCol :=
  if p.1.val < 3 then Sum.inl (cidx p.1.val p.2) else Sum.inr (p.1.val, p.2)

/-- The corner of a column label. -/
def fColInv (hL : 0 < w.length) : BCol → Fin w.length × Fin 3
  | Sum.inl k => cornerOf w hL (kc k)
  | Sum.inr q => cornerOf w hL q

theorem fColInv_fCol (hL : 0 < w.length) (p : Fin w.length × Fin 3) :
    fColInv w hL (fCol w p) = p := by
  unfold fCol
  split_ifs with h
  · simp only [fColInv, kc_cidx]; exact cornerOf_self w hL p
  · exact cornerOf_self w hL p

/-- The row label of the arc leaving a corner: the window label for arcs with a marking in the
window, and the corner itself for the other arcs. -/
def gRow (p : Fin w.length × Fin 3) : BRow :=
  if p.1.val < 3 then Sum.inl (S.col (cidx p.1.val p.2)).1
  else if (positiveRectilinearWordMatching w p).1.val < 3 then
    Sum.inl (S.col (cidx (positiveRectilinearWordMatching w p).1.val
      (positiveRectilinearWordMatching w p).2)).2
  else Sum.inr (p.1.val, p.2)

/-- The corner of a row label. -/
def gRowInv (hL : 0 < w.length) : BRow → Fin w.length × Fin 3
  | Sum.inl x => if x ∈ Ol S then cornerOf w hL (kc ((Ol S).idxOf x))
      else (positiveRectilinearWordMatching w).symm (cornerOf w hL (kc ((Xl S).idxOf x)))
  | Sum.inr q => cornerOf w hL q

/-- The base of the keys of the rows. -/
def BIG (L : ℕ) : ℕ := 3 * L + 17

/-- The tie-breaking part of the key of a row label. -/
def tbR : BRow → ℕ
  | Sum.inl x => S.ri x
  | Sum.inr q => 16 + cidx q.1 q.2

/-- The key of the arc leaving a corner. -/
def kappa (p : Fin w.length × Fin 3) : ℕ := lvl2 w p * BIG w.length + tbR S (gRow w S p)

theorem tb_lt (hS16 : S.rows.length < 16) (p : Fin w.length × Fin 3) :
    tbR S (gRow w S p) < BIG w.length := by
  have hp := p.1.isLt
  have hc := p.2.isLt
  have hri : ∀ x, S.ri x < 16 := fun x => by
    have := List.idxOf_le_length (a := x) (l := S.rows); simp only [WState.ri]; omega
  unfold gRow
  split_ifs
  · simp only [tbR, BIG]; have := hri (S.col (cidx p.1.val p.2)).1; omega
  · simp only [tbR, BIG]; have := hri (S.col (cidx (positiveRectilinearWordMatching w p).1.val
      (positiveRectilinearWordMatching w p).2)).2; omega
  · simp only [tbR, BIG, cidx]; omega

theorem kappa_mono (hS16 : S.rows.length < 16) (p q : Fin w.length × Fin 3)
    (h : lvl2 w p < lvl2 w q) : kappa w S p < kappa w S q := by
  have h1 := tb_lt w S hS16 p
  have h2 : (lvl2 w p + 1) * BIG w.length ≤ lvl2 w q * BIG w.length := Nat.mul_le_mul_right _ h
  rw [Nat.add_one_mul] at h2
  unfold kappa
  omega

theorem key_inj {N a a' r r' : ℕ} (hr : r < N) (hr' : r' < N) (h : a * N + r = a' * N + r') :
    a = a' ∧ r = r' := by
  have hN : 0 < N := by omega
  have e1 : (a * N + r) / N = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hr, Nat.add_zero]
  have e2 : (a' * N + r') / N = a' := by
    rw [Nat.mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hr', Nat.add_zero]
  have ha : a = a' := by rw [← e1, ← e2, h]
  subst ha
  exact ⟨rfl, by omega⟩

variable {i : Fin (m - 1)} {offs : List ℕ} {B t : PositiveAdjacentWord m} {flags : List Bool}

theorem BlockHyp.len_pos {fl : ℕ → Bool} (hB : BlockHyp i offs B t fl) : 0 < (B ++ t).length := by
  rw [List.length_append, hB.len]; omega

theorem BlockHyp.len_append {fl : ℕ → Bool} (hB : BlockHyp i offs B t fl) :
    (B ++ t).length = 3 + t.length := by
  rw [List.length_append, hB.len]

/-- A window `X`-label of an arc coming from outside the block is not an `O`-label. -/
theorem xlabel_not_mem_ol (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (p : Fin (B ++ t).length × Fin 3) (hp : 3 ≤ p.1.val)
    (hq : (positiveRectilinearWordMatching (B ++ t) p).1.val < 3) :
    (S.col (cidx (positiveRectilinearWordMatching (B ++ t) p).1.val
      (positiveRectilinearWordMatching (B ++ t) p).2)).2 ∉ Ol S := by
  obtain ⟨hlen, -, -, -, -, -, -, -, hC1', -, -⟩ := hS
  intro hmem
  obtain ⟨hj, hjx⟩ := exists_of_mem_ol S hmem
  have hj9 : (Ol S).idxOf (S.col (cidx (positiveRectilinearWordMatching (B ++ t) p).1.val
      (positiveRectilinearWordMatching (B ++ t) p).2)).2 < 9 := by omega
  have hk3 := kc_lt hj9
  have hbm := hC1' (_, _) (mem_corners9 hq (positiveRectilinearWordMatching (B ++ t) p).2) _
    (mem_corners9 hk3 (kc _).2) (by rw [cidx_kc, hjx])
  have hkL : (kc ((Ol S).idxOf (S.col (cidx (positiveRectilinearWordMatching (B ++ t) p).1.val
      (positiveRectilinearWordMatching (B ++ t) p).2)).2)).1 < (B ++ t).length := by
    have := hB.len_append; omega
  obtain ⟨hq3, -, hM⟩ := hB.blockM_some hkL hk3 _ hbm
  have h2 := (positiveRectilinearWordMatching (B ++ t)).injective (hM.trans rfl)
  have := congrArg (fun z => z.1.val) h2
  simp only at this
  omega

theorem gRowInv_gRow (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (p : Fin (B ++ t).length × Fin 3) :
    gRowInv (B ++ t) S hB.len_pos (gRow (B ++ t) S p) = p := by
  have hS' := hS
  obtain ⟨hlen, holn, hxln, -, -, -, -, -, -, -, -⟩ := hS'
  unfold gRow
  split_ifs with h1 h2
  · have hk : cidx p.1.val p.2 < S.cols.length := by rw [hlen]; exact cidx_lt h1 p.2
    simp only [gRowInv, if_pos (mem_ol S hk), ol_idxOf S holn hk, kc_cidx]
    exact cornerOf_self _ _ p
  · have hk : cidx (positiveRectilinearWordMatching (B ++ t) p).1.val
        (positiveRectilinearWordMatching (B ++ t) p).2 < S.cols.length := by
      rw [hlen]; exact cidx_lt h2 _
    simp only [gRowInv, if_neg (xlabel_not_mem_ol S hB hS p (by omega) h2),
      xl_idxOf S hxln hk, kc_cidx]
    rw [cornerOf_self]; exact Equiv.symm_apply_apply _ _
  · simp only [gRowInv]; exact cornerOf_self _ _ p

/-- The arc entering a block corner carries the `X`-label of its window column. -/
theorem gRow_symm_block (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (q : Fin (B ++ t).length × Fin 3) (hq : q.1.val < 3) :
    gRow (B ++ t) S ((positiveRectilinearWordMatching (B ++ t)).symm q) =
      Sum.inl (S.col (cidx q.1.val q.2)).2 := by
  obtain ⟨hlen, -, -, -, -, -, -, hbm, -, -, -⟩ := hS
  have hMp : positiveRectilinearWordMatching (B ++ t)
      ((positiveRectilinearWordMatching (B ++ t)).symm q) = q := Equiv.apply_symm_apply _ _
  generalize (positiveRectilinearWordMatching (B ++ t)).symm q = p at hMp ⊢
  unfold gRow
  split_ifs with h1 h2
  · have hb := hbm (p.1.val, p.2) (mem_corners9 h1 p.2)
    unfold bmOK at hb
    rcases hBM : BM offs (flagOf flags) p.1.val p.2 with _ | q'
    · have := hB.blockM_none p.1.isLt h1 p.2 hBM
      simp only [Fin.eta, Prod.mk.eta, hMp] at this
      omega
    · rw [hBM] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      obtain ⟨-, hX⟩ := hb
      obtain ⟨hq3, -, hM⟩ := hB.blockM_some p.1.isLt h1 p.2 hBM
      simp only [Fin.eta, Prod.mk.eta, hMp] at hM
      rw [← hX, hM]
  · rw [hMp]
  · exfalso; rw [hMp] at h2; exact h2 hq

theorem gRow_inl_mem (_hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    {p : Fin (B ++ t).length × Fin 3} {x : ℕ} (h : gRow (B ++ t) S p = Sum.inl x) : x ∈ S.rows := by
  obtain ⟨hlen, -, -, -, -, hmr, -, -, -, -, -⟩ := hS
  unfold gRow at h
  split_ifs at h with h1 h2
  · simp only [Sum.inl.injEq] at h; subst h
    exact (hmr _ (mem_corners9 h1 p.2)).1
  · simp only [Sum.inl.injEq] at h; subst h
    exact (hmr _ (mem_corners9 h2 _)).2

theorem kappa_inj (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    {p q : Fin (B ++ t).length × Fin 3} (h : kappa (B ++ t) S p = kappa (B ++ t) S q) : p = q := by
  have hS16 : S.rows.length < 16 := hS.2.2.2.2.1
  obtain ⟨-, htb⟩ := key_inj (tb_lt _ S hS16 p) (tb_lt _ S hS16 q) h
  have hg : gRow (B ++ t) S p = gRow (B ++ t) S q := by
    rcases hgp : gRow (B ++ t) S p with x | a <;> rcases hgq : gRow (B ++ t) S q with y | b <;>
      rw [hgp, hgq] at htb <;> simp only [tbR] at htb
    · have hx := gRow_inl_mem S hB hS hgp
      rw [WState.ri, WState.ri, List.idxOf_inj hx] at htb
      rw [htb]
    · have hx := gRow_inl_mem S hB hS hgp
      have := List.idxOf_lt_length_iff.mpr hx
      simp only [WState.ri] at htb; omega
    · have hy := gRow_inl_mem S hB hS hgq
      have := List.idxOf_lt_length_iff.mpr hy
      simp only [WState.ri] at htb; omega
    · have hab : cidx a.1 a.2 = cidx b.1 b.2 := by omega
      have := congrArg kc hab
      rw [kc_cidx, kc_cidx] at this
      simp only [Prod.mk.eta] at this
      rw [this]
  rw [← gRowInv_gRow S hB hS p, hg, gRowInv_gRow S hB hS q]

/-- The initial grid of `B ++ t` for the window state `S`. -/
def initGrid (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags) :
    LabeledGrid ((B ++ t).length * 3) BCol BRow :=
  (cornerGrid (B ++ t) (kappa (B ++ t) S)).relabel (fCol (B ++ t)) (fColInv (B ++ t) hB.len_pos)
    (gRow (B ++ t) S) (gRowInv (B ++ t) S hB.len_pos) (fun c _ => fColInv_fCol _ _ c)
    (fun r _ => gRowInv_gRow S hB hS r)

/-- The initial grid is related to the selected grid of `B ++ t`. -/
theorem initGrid_movesTo (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags) :
    (initGrid S hB hS).toGrid.MovesTo (wordGrid (B ++ t)) := by
  rw [initGrid, LabeledGrid.toGrid_relabel]
  exact (cornerGrid_admissible _ _ (kappa_mono _ S hS.2.2.2.2.1)).movesTo_wordGrid

end InitGrid

/-! ### The initial grid realizes the initial window state -/

section InitReal

variable {m : ℕ} (S : WState) {i : Fin (m - 1)} {offs : List ℕ} {B t : PositiveAdjacentWord m}
  {flags : List Bool}

/-- The outside columns of a word of length `L`. -/
def outsideQ (L : ℕ) : List (ℕ × Fin 3) := (List.range' 9 (L * 3 - 9)).map kc

theorem finRange_map_eq {β : Type*} (n : ℕ) (F : ℕ → β) :
    (List.finRange n).map (fun k => F k.val) = (List.range n).map F := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp

theorem fCol_symm (w : PositiveAdjacentWord m) (k : Fin (w.length * 3)) :
    fCol w (finProdFinEquiv.symm k) = if k.val < 9 then Sum.inl k.val else Sum.inr (kc k.val) := by
  have h := GridMoves.finProdFinEquiv_val_three (finProdFinEquiv.symm k)
  rw [Equiv.apply_symm_apply] at h
  have hc := (finProdFinEquiv.symm k).2.isLt
  unfold fCol
  split_ifs with h1 h2 h2
  · congr 1; simp only [cidx]; omega
  · exfalso; omega
  · exfalso; omega
  · congr 1

theorem cornerCols_map_fCol (w : PositiveAdjacentWord m) (hL : 3 ≤ w.length) :
    (cornerCols w).map (fCol w) =
      (List.range 9).map Sum.inl ++ (outsideQ w.length).map Sum.inr := by
  rw [cornerCols, List.map_map]
  have e1 : (List.finRange (w.length * 3)).map (fCol w ∘ finProdFinEquiv.symm) =
      (List.range (w.length * 3)).map
        (fun k => if k < 9 then (Sum.inl k : BCol) else Sum.inr (kc k)) := by
    rw [← finRange_map_eq]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, fCol_symm]
  rw [e1]
  have e2 : List.range (w.length * 3) = List.range' 0 9 ++ List.range' 9 (w.length * 3 - 9) := by
    rw [List.range_eq_range']
    have := List.range'_append (s := 0) (m := 9) (n := w.length * 3 - 9) (step := 1)
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [this]; congr 1; omega
  rw [e2, List.map_append, outsideQ, List.map_map, List.range_eq_range']
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range'_1] at hk
  simp [show ¬ k < 9 by omega]

theorem gRow_fColInv_inl (hB : BlockHyp i offs B t (flagOf flags)) {k : ℕ} (hk : k < 9) :
    gRow (B ++ t) S (fColInv (B ++ t) hB.len_pos (Sum.inl k)) = Sum.inl (S.col k).1 := by
  have h3 := kc_lt hk
  simp only [fColInv]
  rw [cornerOf_eq _ _ (by have := hB.len_append; omega)]
  unfold gRow
  rw [if_pos h3]
  simp only [cidx_kc]

theorem gRow_symm_fColInv_inl (hB : BlockHyp i offs B t (flagOf flags))
    (hS : InitOK S offs flags) {k : ℕ} (hk : k < 9) :
    gRow (B ++ t) S ((positiveRectilinearWordMatching (B ++ t)).symm
      (fColInv (B ++ t) hB.len_pos (Sum.inl k))) = Sum.inl (S.col k).2 := by
  have h3 := kc_lt hk
  simp only [fColInv]
  rw [cornerOf_eq _ _ (by have := hB.len_append; omega), gRow_symm_block S hB hS _ h3]
  simp only [cidx_kc]

theorem initGrid_O (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (c : BCol) : (initGrid S hB hS).O c = gRow (B ++ t) S (fColInv (B ++ t) hB.len_pos c) := rfl

theorem initGrid_X (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (c : BCol) : (initGrid S hB hS).X c = gRow (B ++ t) S
      ((positiveRectilinearWordMatching (B ++ t)).symm (fColInv (B ++ t) hB.len_pos c)) := rfl

theorem initGrid_rows (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags) :
    (initGrid S hB hS).rows = (cornerRows (B ++ t) (kappa (B ++ t) S)).map (gRow (B ++ t) S) :=
  rfl

theorem initGrid_cols (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags) :
    (initGrid S hB hS).cols = (cornerCols (B ++ t)).map (fCol (B ++ t)) := rfl

/-- The level of a window label is the level of its arc. -/
theorem lvl_of_gRow (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    {p : Fin (B ++ t).length × Fin 3} {x : ℕ} (h : gRow (B ++ t) S p = Sum.inl x) :
    lvl2 (B ++ t) p = 2 * i.val + lvlRel S offs x := by
  have hS' := hS
  obtain ⟨hlen, holn, hxln, -, -, -, -, -, -, -, -⟩ := hS'
  unfold gRow at h
  split_ifs at h with h1 h2
  · simp only [Sum.inl.injEq] at h; subst h
    have hk : cidx p.1.val p.2 < S.cols.length := by rw [hlen]; exact cidx_lt h1 p.2
    unfold lvlRel
    rw [if_pos (mem_ol S hk), ol_idxOf S holn hk, kc_cidx]
    dsimp only
    have hv := hB.val p.1.val (by rw [hB.len]; exact h1)
    have hget : (B ++ t)[p.1.val] = B[p.1.val]'(by rw [hB.len]; exact h1) :=
      List.getElem_append_left _
    unfold lvl2 outLvl
    rw [hget, hv]
    split_ifs <;> omega
  · simp only [Sum.inl.injEq] at h; subst h
    have hnot := xlabel_not_mem_ol S hB hS p (by omega) h2
    have hc0 : p.2 ≠ 0 := by
      intro h0
      have := positiveRectilinearWordMatching_middle (B ++ t) p.1
      rw [← h0] at this
      simp only [Prod.mk.eta] at this
      rw [this] at h2
      exact h1 h2
    obtain ⟨hq2, hrank⟩ := matching_inRank (B ++ t) p hc0
    have hk : cidx (positiveRectilinearWordMatching (B ++ t) p).1.val
        (positiveRectilinearWordMatching (B ++ t) p).2 < S.cols.length := by
      rw [hlen]; exact cidx_lt h2 _
    unfold lvlRel
    rw [if_neg hnot, xl_idxOf S hxln hk, kc_cidx]
    dsimp only
    unfold inRank outRank at hrank
    generalize positiveRectilinearWordMatching (B ++ t) p = q at *
    have hv := hB.val q.1.val (by rw [hB.len]; exact h2)
    have hget : (B ++ t)[q.1.val] = B[q.1.val]'(by rw [hB.len]; exact h2) :=
      List.getElem_append_left _
    rw [hget, hv] at hrank
    unfold lvl2 inLvl
    have := p.2.isLt
    have := q.2.isLt
    have hp2 : p.2.val ≠ 0 := fun e => hc0 (Fin.ext e)
    have hq2' : q.2.val ≠ 2 := fun e => hq2 (Fin.ext e)
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two] at hrank ⊢
    split_ifs at hrank ⊢ <;> omega

theorem kappa_inl (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    {p : Fin (B ++ t).length × Fin 3} {x : ℕ} (h : gRow (B ++ t) S p = Sum.inl x) :
    kappa (B ++ t) S p = (2 * i.val + lvlRel S offs x) * BIG (B ++ t).length + S.ri x := by
  unfold kappa
  rw [lvl_of_gRow S hB hS h, h]
  rfl

theorem eq_of_pairwise_key {α : Type*} {K : α → ℕ} {l₁ l₂ : List α}
    (h₁ : l₁.Pairwise (fun a b => K a < K b)) (h₂ : l₂.Pairwise (fun a b => K a < K b))
    (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ := by
  have n₁ : l₁.Nodup := h₁.imp (fun h e => by subst e; exact lt_irrefl _ h)
  have n₂ : l₂.Nodup := h₂.imp (fun h e => by subst e; exact lt_irrefl _ h)
  exact List.Perm.eq_of_pairwise (fun a b _ _ h h' => absurd (h.trans h') (lt_irrefl _)) h₁ h₂
    ((List.perm_ext_iff_of_nodup n₁ n₂).mpr hmem)

theorem pairwise_idxOf_lt {α : Type*} [DecidableEq α] {l : List α} (hn : l.Nodup) :
    l.Pairwise (fun a b => l.idxOf a < l.idxOf b) := by
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  rw [List.Nodup.idxOf_getElem hn, List.Nodup.idxOf_getElem hn]
  exact hab

/-- The rows of the initial grid are sorted by the keys of their corners. -/
theorem initGrid_rows_pairwise (hB : BlockHyp i offs B t (flagOf flags))
    (hS : InitOK S offs flags) :
    (initGrid S hB hS).rows.Pairwise (fun r r' =>
      kappa (B ++ t) S (gRowInv (B ++ t) S hB.len_pos r) <
        kappa (B ++ t) S (gRowInv (B ++ t) S hB.len_pos r')) := by
  rw [initGrid_rows, List.pairwise_map]
  have h := (cornerRows_sorted (B ++ t) (kappa (B ++ t) S)).and
    (List.nodup_iff_pairwise_ne.mp (cornerRows_nodup (B ++ t) (kappa (B ++ t) S)))
  refine h.imp fun {a b} hab => ?_
  rw [gRowInv_gRow S hB hS, gRowInv_gRow S hB hS]
  exact lt_of_le_of_ne hab.1 (fun e => hab.2 (kappa_inj S hB hS e))

theorem mem_initGrid_rows (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (r : BRow) : r ∈ (initGrid S hB hS).rows ↔ ∃ p, gRow (B ++ t) S p = r := by
  rw [initGrid_rows, List.mem_map]
  exact ⟨fun ⟨p, _, hp⟩ => ⟨p, hp⟩, fun ⟨p, hp⟩ => ⟨p, mem_cornerRows _ _ p, hp⟩⟩

theorem initGrid_lefts (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags) :
    lefts (initGrid S hB hS).rows = S.rows := by
  have hS' := hS
  obtain ⟨hlen, -, -, hrn, -, -, hrm, -, -, -, hsort⟩ := hS'
  let K : ℕ → ℕ := fun x => (2 * i.val + lvlRel S offs x) * BIG (B ++ t).length + S.ri x
  apply eq_of_pairwise_key (K := K)
  · have h := (List.Pairwise.and_mem.mp (initGrid_rows_pairwise S hB hS))
    refine h.filterMap _ ?_
    rintro a a' ⟨ha, ha', hlt⟩ b hb b' hb'
    rcases a with x | e
    · rcases a' with y | e'
      · simp only [Sum.getLeft?_inl, Option.some.injEq] at hb hb'
        subst hb; subst hb'
        obtain ⟨p, hp⟩ := (mem_initGrid_rows S hB hS _).mp ha
        obtain ⟨p', hp'⟩ := (mem_initGrid_rows S hB hS _).mp ha'
        rw [← hp, ← hp', gRowInv_gRow S hB hS, gRowInv_gRow S hB hS, kappa_inl S hB hS hp,
          kappa_inl S hB hS hp'] at hlt
        exact hlt
      · simp at hb'
    · simp at hb
  · have h1 := hsort.and (pairwise_idxOf_lt hrn)
    refine h1.imp fun {a b} hab => ?_
    have := Nat.mul_le_mul_right (BIG (B ++ t).length)
      (show 2 * i.val + lvlRel S offs a ≤ 2 * i.val + lvlRel S offs b by omega)
    simp only [K, WState.ri]
    omega
  · intro x
    rw [mem_lefts, mem_initGrid_rows]
    constructor
    · rintro ⟨p, hp⟩; exact gRow_inl_mem S hB hS hp
    · intro hx
      rcases hrm x hx with ho | hxl
      · obtain ⟨hj, hjx⟩ := exists_of_mem_ol S ho
        exact ⟨_, (gRow_fColInv_inl S hB (k := (Ol S).idxOf x) (by omega)).trans (by rw [hjx])⟩
      · obtain ⟨hj, hjx⟩ := exists_of_mem_xl S hxl
        exact ⟨_, (gRow_symm_fColInv_inl S hB hS (k := (Xl S).idxOf x) (by omega)).trans
          (by rw [hjx])⟩

/-- The initial grid realizes the initial window state. -/
theorem initGrid_real (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags) :
    Real S (initGrid S hB hS) (List.range 9) (outsideQ (B ++ t).length) where
  cols := cornerCols_map_fCol _ (by have := hB.len_append; omega)
  len := by simp [hS.1]
  marks p hp := by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
    simp only [List.length_zip, List.length_range] at hk
    have hk9 : k < 9 := by omega
    simp only [List.getElem_zip, List.getElem_range]
    rw [← col_eq_getElem S (by rw [hS.1]; exact hk9)]
    exact ⟨gRow_fColInv_inl S hB hk9, gRow_symm_fColInv_inl S hB hS hk9⟩
  rows := initGrid_lefts S hB hS

end InitReal

end BraidWindow

end OnLeConjecture.KnotTheory
