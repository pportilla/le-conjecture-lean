/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesBlock
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationInit

/-! # The initial grid of a signed word with a block of letters

For a signed word `v` and a key `κ` on its corners, `SignedGrid.sCornerGrid v κ` has the corners
of `v` as column and row labels, rows sorted by `κ`, `O`-markings on the identity and
`X`-markings on the inverse of the matching `SignedGrid.sM v`. It is a signed word grid of `v`
when `κ` refines the outgoing heights (`SignedGrid.sCornerGrid_signed`).

For a word `B ++ t` with a block `B` of `K` signed letters and a window state `S` satisfying the
finite checks `SignedGrid.InitOKS`, the relabeled grid `SignedGrid.sInitGrid` realizes `S`
(`SignedGrid.sInitGrid_real`) and is a signed word grid of `B ++ t`
(`SignedGrid.sInitGrid_signed`). This is the signed version of `BraidWindow.initGrid`. All
results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

/-! ### Corner grids of signed words -/

section CornerGrid

variable (v : SignedAdjacentWord m)

/-- The corners of a signed word in the standard column order. -/
def sCols : List (Fin v.length × Fin 3) :=
  (List.finRange (v.length * 3)).map finProdFinEquiv.symm

theorem mem_sCols (p : Fin v.length × Fin 3) : p ∈ sCols v :=
  List.mem_map.mpr ⟨finProdFinEquiv p, List.mem_finRange _, by simp⟩

theorem sCols_nodup : (sCols v).Nodup :=
  (List.nodup_finRange _).map finProdFinEquiv.symm.injective

theorem sCols_length : (sCols v).length = v.length * 3 := by simp [sCols]

variable (κ : Fin v.length × Fin 3 → ℕ)

/-- The corners of a signed word sorted by a key. -/
def sRows : List (Fin v.length × Fin 3) :=
  (sCols v).mergeSort (fun a b => decide (κ a ≤ κ b))

theorem mem_sRows (p : Fin v.length × Fin 3) : p ∈ sRows v κ := by
  rw [sRows, List.mem_mergeSort]; exact mem_sCols v p

theorem sRows_nodup : (sRows v κ).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (sCols_nodup v)

theorem sRows_sorted : (sRows v κ).Pairwise (fun a b => κ a ≤ κ b) := by
  have := List.pairwise_mergeSort (le := fun a b => decide (κ a ≤ κ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (sCols v)
  exact this.imp (fun h => by simpa using h)

/-- The corner grid of a signed word with rows sorted by a key. -/
def sCornerGrid : LabeledGrid (v.length * 3) (Fin v.length × Fin 3) (Fin v.length × Fin 3) where
  cols := sCols v
  rows := sRows v κ
  O := id
  X := (sM v).symm
  cols_length := sCols_length v
  rows_length := by rw [sRows, List.length_mergeSort, sCols_length]
  cols_nodup := sCols_nodup v
  rows_nodup := sRows_nodup v κ
  O_mem c _ := mem_sRows v κ c
  X_mem c _ := mem_sRows v κ _
  O_inj a _ b _ h := h
  X_inj a _ b _ h := (sM v).symm.injective h
  O_ne_X c _ h := by
    have h' : c = (sM v).symm c := h
    have e : sM v c = c := by
      conv_lhs => rw [h']
      exact Equiv.apply_symm_apply _ _
    have := sM_height v c
    rw [e] at this
    exact oHeight2_ne_xHeight2 v c this.symm

theorem sCornerGrid_colAt (k : Fin (v.length * 3)) :
    (sCornerGrid v κ).colAt k = finProdFinEquiv.symm k := by
  simp [LabeledGrid.colAt, sCornerGrid, sCols]

/-- A corner grid whose key refines the outgoing heights is a signed word grid. -/
theorem sCornerGrid_signed (hmono : ∀ p q, v.oHeight2 p < v.oHeight2 q → κ p < κ q) :
    IsSignedWordGrid v (sCornerGrid v κ).toGrid := by
  rw [isSignedWordGrid_iff]
  constructor
  · intro a b h
    rw [Fin.lt_def, LabeledGrid.toGrid_O_val, LabeledGrid.toGrid_O_val, sCornerGrid_colAt,
      sCornerGrid_colAt]
    simp only [Equiv.symm_apply_apply]
    change (sCornerGrid v κ).rpos a < (sCornerGrid v κ).rpos b
    exact idxOf_lt_of_level (sRows_sorted v κ) (mem_sRows v κ a) (mem_sRows v κ b)
      (hmono a b h)
  · intro q
    apply Fin.ext
    rw [LabeledGrid.toGrid_X_val, LabeledGrid.toGrid_O_val, sCornerGrid_colAt, sCornerGrid_colAt]
    simp [sCornerGrid]

end CornerGrid

/-! ### Finite checks on an initial window state -/

/-- The corners of a block of `K` letters. -/
def cornersK (K : ℕ) : List (ℕ × Fin 3) :=
  (List.range K).flatMap fun h => [(h, 0), (h, 1), (h, 2)]

theorem mem_cornersK {K h : ℕ} (hh : h < K) (c : Fin 3) : (h, c) ∈ cornersK K := by
  simp only [cornersK, List.mem_flatMap, List.mem_range]
  refine ⟨h, hh, ?_⟩
  fin_cases c <;> simp

theorem lt_of_mem_cornersK {K : ℕ} {p : ℕ × Fin 3} (hp : p ∈ cornersK K) : p.1 < K := by
  simp only [cornersK, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨h, hh, hp⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact hh

theorem cidx_ltK {K h : ℕ} (hh : h < K) (c : Fin 3) : cidx h c < 3 * K := by
  have := c.isLt; simp only [cidx]; omega

theorem kc_ltK {K k : ℕ} (hk : k < 3 * K) : (kc k).1 < K := by simp only [kc]; omega

/-- Twice the relative height of a window label. -/
def lvlRelS (S : WState) (offs : List ℕ) (sg : List Bool) (x : ℕ) : ℕ :=
  if x ∈ Ol S then outLvlS offs sg (kc ((Ol S).idxOf x)).1 (kc ((Ol S).idxOf x)).2
  else inLvlS offs sg (kc ((Xl S).idxOf x)).1 (kc ((Xl S).idxOf x)).2

/-- The check of a block corner against the block matching `BMs`. -/
def bmOKS (K : ℕ) (S : WState) (offs : List ℕ) (sg : List Bool) (flags : List Bool)
    (p : ℕ × Fin 3) : Bool :=
  match BMs K offs sg (flagOf flags) p.1 p.2 with
  | some q => decide (q.1 < K) && (S.col (cidx q.1 q.2)).2 == (S.col (cidx p.1 p.2)).1
  | none => (S.col (cidx p.1 p.2)).1 == 30 + rankOffS offs sg p.1 p.2

/-- The finite checks on an initial window state of a block of `K` signed letters. -/
def InitOKS (K : ℕ) (S : WState) (offs : List ℕ) (sg : List Bool) (flags : List Bool) : Prop :=
  S.cols.length = 3 * K ∧ (Ol S).Nodup ∧ (Xl S).Nodup ∧ S.rows.Nodup ∧ S.rows.length < 16 ∧
  (∀ p ∈ cornersK K, (S.col (cidx p.1 p.2)).1 ∈ S.rows ∧ (S.col (cidx p.1 p.2)).2 ∈ S.rows) ∧
  (∀ x ∈ S.rows, x ∈ Ol S ∨ x ∈ Xl S) ∧
  (∀ p ∈ cornersK K, bmOKS K S offs sg flags p = true) ∧
  (∀ p ∈ cornersK K, ∀ p' ∈ cornersK K, (S.col (cidx p.1 p.2)).2 = (S.col (cidx p'.1 p'.2)).1 →
    BMs K offs sg (flagOf flags) p'.1 p'.2 = some p) ∧
  (∀ p ∈ cornersK K, (S.col (cidx p.1 p.2)).2 ∉ Ol S →
    (S.col (cidx p.1 p.2)).2 = 20 + inRelS offs sg p.1 p.2) ∧
  S.rows.Pairwise (fun a b => lvlRelS S offs sg a ≤ lvlRelS S offs sg b)

instance (K : ℕ) (S : WState) (offs : List ℕ) (sg : List Bool) (flags : List Bool) :
    Decidable (InitOKS K S offs sg flags) := by
  unfold InitOKS; infer_instance

/-! ### The initial grid -/

section InitGrid

variable {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
  {B t : SignedAdjacentWord m} (S : WState)

variable (K) in
/-- The column label of a corner: window positions for the first `K` letters. -/
def sfCol (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) : BCol :=
  if p.1.val < K then Sum.inl (cidx p.1.val p.2) else Sum.inr (p.1.val, p.2)

/-- The corner with given coordinates, clamped to the word. -/
def sCornerOf (v : SignedAdjacentWord m) (hL : 0 < v.length) (q : ℕ × Fin 3) :
    Fin v.length × Fin 3 :=
  (⟨min q.1 (v.length - 1), by omega⟩, q.2)

theorem sCornerOf_eq (v : SignedAdjacentWord m) (hL : 0 < v.length) {q : ℕ × Fin 3}
    (hq : q.1 < v.length) : sCornerOf v hL q = (⟨q.1, hq⟩, q.2) := by
  simp only [sCornerOf, Prod.mk.injEq, Fin.mk.injEq, and_true]; omega

theorem sCornerOf_self (v : SignedAdjacentWord m) (hL : 0 < v.length) (p : Fin v.length × Fin 3) :
    sCornerOf v hL (p.1.val, p.2) = p := sCornerOf_eq v hL p.1.isLt

/-- The corner of a column label. -/
def sfColInv (v : SignedAdjacentWord m) (hL : 0 < v.length) : BCol → Fin v.length × Fin 3
  | Sum.inl k => sCornerOf v hL (kc k)
  | Sum.inr q => sCornerOf v hL q

theorem sfColInv_sfCol (v : SignedAdjacentWord m) (hL : 0 < v.length) (p : Fin v.length × Fin 3) :
    sfColInv v hL (sfCol K v p) = p := by
  unfold sfCol
  split_ifs with h
  · simp only [sfColInv, kc_cidx]; exact sCornerOf_self v hL p
  · exact sCornerOf_self v hL p

variable (K) in
/-- The row label of the arc leaving a corner. -/
def sgRow (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) : BRow :=
  if p.1.val < K then Sum.inl (S.col (cidx p.1.val p.2)).1
  else if (sM v p).1.val < K then Sum.inl (S.col (cidx (sM v p).1.val (sM v p).2)).2
  else Sum.inr (p.1.val, p.2)

/-- The corner of a row label. -/
def sgRowInv (v : SignedAdjacentWord m) (hL : 0 < v.length) : BRow → Fin v.length × Fin 3
  | Sum.inl x => if x ∈ Ol S then sCornerOf v hL (kc ((Ol S).idxOf x))
      else (sM v).symm (sCornerOf v hL (kc ((Xl S).idxOf x)))
  | Sum.inr q => sCornerOf v hL q

variable (K) in
/-- The key of the arc leaving a corner. -/
def skappa (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) : ℕ :=
  v.oHeight2 p * BIG v.length + tbR S (sgRow K S v p)

theorem stb_lt (v : SignedAdjacentWord m) (hS16 : S.rows.length < 16) (p : Fin v.length × Fin 3) :
    tbR S (sgRow K S v p) < BIG v.length := by
  have hp := p.1.isLt
  have hc := p.2.isLt
  have hri : ∀ x, S.ri x < 16 := fun x => by
    have := List.idxOf_le_length (a := x) (l := S.rows); simp only [WState.ri]; omega
  unfold sgRow
  split_ifs
  · simp only [tbR, BIG]; have := hri (S.col (cidx p.1.val p.2)).1; omega
  · simp only [tbR, BIG]; have := hri (S.col (cidx (sM v p).1.val (sM v p).2)).2; omega
  · simp only [tbR, BIG, cidx]; omega

theorem skappa_mono (v : SignedAdjacentWord m) (hS16 : S.rows.length < 16)
    (p q : Fin v.length × Fin 3) (h : v.oHeight2 p < v.oHeight2 q) :
    skappa K S v p < skappa K S v q := by
  have h1 := stb_lt (K := K) S v hS16 p
  have h2 : (v.oHeight2 p + 1) * BIG v.length ≤ v.oHeight2 q * BIG v.length :=
    Nat.mul_le_mul_right _ h
  rw [Nat.add_one_mul] at h2
  unfold skappa
  omega

/-- A window `X`-label of an arc coming from outside the block is not an `O`-label. -/
theorem sxlabel_not_mem_ol (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (p : Fin (B ++ t).length × Fin 3) (hp : K ≤ p.1.val)
    (hq : (sM (B ++ t) p).1.val < K) :
    (S.col (cidx (sM (B ++ t) p).1.val (sM (B ++ t) p).2)).2 ∉ Ol S := by
  obtain ⟨hlen, -, -, -, -, -, -, -, hC1', -, -⟩ := hS
  intro hmem
  obtain ⟨hj, hjx⟩ := exists_of_mem_ol S hmem
  have hj9 : (Ol S).idxOf (S.col (cidx (sM (B ++ t) p).1.val (sM (B ++ t) p).2)).2 < 3 * K := by
    omega
  have hk3 := kc_ltK hj9
  have hbm := hC1' (_, _) (mem_cornersK hq (sM (B ++ t) p).2) _
    (mem_cornersK hk3 (kc _).2) (by rw [cidx_kc, hjx])
  have hkL : (kc ((Ol S).idxOf (S.col (cidx (sM (B ++ t) p).1.val
      (sM (B ++ t) p).2)).2)).1 < (B ++ t).length := by
    have := hB.len_append; omega
  obtain ⟨hq3, -, hM⟩ := hB.blockMs_some hk3 hkL _ hbm
  have h2 := (sM (B ++ t)).injective (hM.trans rfl)
  have := congrArg (fun z => z.1.val) h2
  simp only at this
  omega

theorem sgRowInv_sgRow (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (p : Fin (B ++ t).length × Fin 3) :
    sgRowInv S (B ++ t) hB.len_pos (sgRow K S (B ++ t) p) = p := by
  have hS' := hS
  obtain ⟨hlen, holn, hxln, -, -, -, -, -, -, -, -⟩ := hS'
  unfold sgRow
  split_ifs with h1 h2
  · have hk : cidx p.1.val p.2 < S.cols.length := by rw [hlen]; exact cidx_ltK h1 p.2
    simp only [sgRowInv, if_pos (mem_ol S hk), ol_idxOf S holn hk, kc_cidx]
    exact sCornerOf_self _ _ p
  · have hk : cidx (sM (B ++ t) p).1.val (sM (B ++ t) p).2 < S.cols.length := by
      rw [hlen]; exact cidx_ltK h2 _
    simp only [sgRowInv, if_neg (sxlabel_not_mem_ol S hB hS p (by omega) h2),
      xl_idxOf S hxln hk, kc_cidx]
    rw [sCornerOf_self]; exact Equiv.symm_apply_apply _ _
  · simp only [sgRowInv]; exact sCornerOf_self _ _ p

/-- The arc entering a block corner carries the `X`-label of its window column. -/
theorem sgRow_symm_block (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (q : Fin (B ++ t).length × Fin 3) (hq : q.1.val < K) :
    sgRow K S (B ++ t) ((sM (B ++ t)).symm q) = Sum.inl (S.col (cidx q.1.val q.2)).2 := by
  obtain ⟨hlen, -, -, -, -, -, -, hbm, -, -, -⟩ := hS
  have hMp : sM (B ++ t) ((sM (B ++ t)).symm q) = q := Equiv.apply_symm_apply _ _
  generalize (sM (B ++ t)).symm q = p at hMp ⊢
  unfold sgRow
  split_ifs with h1 h2
  · have hb := hbm (p.1.val, p.2) (mem_cornersK h1 p.2)
    unfold bmOKS at hb
    rcases hBM : BMs K offs sg (flagOf flags) p.1.val p.2 with _ | q'
    · have := hB.blockMs_none h1 p.1.isLt p.2 hBM
      simp only [Fin.eta, Prod.mk.eta, hMp] at this
      omega
    · rw [hBM] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      obtain ⟨-, hX⟩ := hb
      obtain ⟨hq3, -, hM⟩ := hB.blockMs_some h1 p.1.isLt p.2 hBM
      simp only [Fin.eta, Prod.mk.eta, hMp] at hM
      rw [← hX, hM]
  · rw [hMp]
  · exfalso; rw [hMp] at h2; exact h2 hq

theorem sgRow_inl_mem (hS : InitOKS K S offs sg flags) {v : SignedAdjacentWord m}
    {p : Fin v.length × Fin 3} {x : ℕ} (h : sgRow K S v p = Sum.inl x) : x ∈ S.rows := by
  obtain ⟨hlen, -, -, -, -, hmr, -, -, -, -, -⟩ := hS
  unfold sgRow at h
  split_ifs at h with h1 h2
  · simp only [Sum.inl.injEq] at h; subst h
    exact (hmr _ (mem_cornersK h1 p.2)).1
  · simp only [Sum.inl.injEq] at h; subst h
    exact (hmr _ (mem_cornersK h2 _)).2

theorem skappa_inj (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {p q : Fin (B ++ t).length × Fin 3}
    (h : skappa K S (B ++ t) p = skappa K S (B ++ t) q) : p = q := by
  have hS16 : S.rows.length < 16 := hS.2.2.2.2.1
  obtain ⟨-, htb⟩ := key_inj (stb_lt S _ hS16 p) (stb_lt S _ hS16 q) h
  have hg : sgRow K S (B ++ t) p = sgRow K S (B ++ t) q := by
    rcases hgp : sgRow K S (B ++ t) p with x | a <;> rcases hgq : sgRow K S (B ++ t) q with y | b <;>
      rw [hgp, hgq] at htb <;> simp only [tbR] at htb
    · have hx := sgRow_inl_mem S hS hgp
      rw [WState.ri, WState.ri, List.idxOf_inj hx] at htb
      rw [htb]
    · have hx := sgRow_inl_mem S hS hgp
      have := List.idxOf_lt_length_iff.mpr hx
      simp only [WState.ri] at htb; omega
    · have hy := sgRow_inl_mem S hS hgq
      have := List.idxOf_lt_length_iff.mpr hy
      simp only [WState.ri] at htb; omega
    · have hab : cidx a.1 a.2 = cidx b.1 b.2 := by omega
      have := congrArg kc hab
      rw [kc_cidx, kc_cidx] at this
      simp only [Prod.mk.eta] at this
      rw [this]
  rw [← sgRowInv_sgRow S hB hS p, hg, sgRowInv_sgRow S hB hS q]

/-- The initial grid of `B ++ t` for the window state `S`. -/
def sInitGrid (hB : BlockS K E i offs sg B t (flagOf flags)) (hS : InitOKS K S offs sg flags) :
    LabeledGrid ((B ++ t).length * 3) BCol BRow :=
  (sCornerGrid (B ++ t) (skappa K S (B ++ t))).relabel (sfCol K (B ++ t))
    (sfColInv (B ++ t) hB.len_pos) (sgRow K S (B ++ t)) (sgRowInv S (B ++ t) hB.len_pos)
    (fun c _ => sfColInv_sfCol _ _ c) (fun r _ => sgRowInv_sgRow S hB hS r)

/-- The initial grid is a signed word grid of `B ++ t`. -/
theorem sInitGrid_signed (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) : IsSignedWordGrid (B ++ t) (sInitGrid S hB hS).toGrid := by
  rw [sInitGrid, LabeledGrid.toGrid_relabel]
  exact sCornerGrid_signed _ _ (skappa_mono S _ hS.2.2.2.2.1)

end InitGrid

/-! ### The initial grid realizes the initial window state -/

section InitReal

variable {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
  {B t : SignedAdjacentWord m} (S : WState)

/-- The outside columns of a word of length `L` with a block of `K` letters. -/
def outsideQK (K L : ℕ) : List (ℕ × Fin 3) := (List.range' (3 * K) (L * 3 - 3 * K)).map kc

theorem sfCol_symm (v : SignedAdjacentWord m) (k : Fin (v.length * 3)) :
    sfCol K v (finProdFinEquiv.symm k) =
      if k.val < 3 * K then Sum.inl k.val else Sum.inr (kc k.val) := by
  have h := GridMoves.finProdFinEquiv_val_three (finProdFinEquiv.symm k)
  rw [Equiv.apply_symm_apply] at h
  have hc := (finProdFinEquiv.symm k).2.isLt
  unfold sfCol
  split_ifs with h1 h2 h2
  · congr 1; simp only [cidx]; omega
  · exfalso; omega
  · exfalso; omega
  · congr 1

theorem sCols_map_sfCol (v : SignedAdjacentWord m) (hL : K ≤ v.length) :
    (sCols v).map (sfCol K v) =
      (List.range (3 * K)).map Sum.inl ++ (outsideQK K v.length).map Sum.inr := by
  rw [sCols, List.map_map]
  have e1 : (List.finRange (v.length * 3)).map (sfCol K v ∘ finProdFinEquiv.symm) =
      (List.range (v.length * 3)).map
        (fun k => if k < 3 * K then (Sum.inl k : BCol) else Sum.inr (kc k)) := by
    rw [← finRange_map_eq]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, sfCol_symm]
  rw [e1]
  have e2 : List.range (v.length * 3) =
      List.range' 0 (3 * K) ++ List.range' (3 * K) (v.length * 3 - 3 * K) := by
    rw [List.range_eq_range']
    have := List.range'_append (s := 0) (m := 3 * K) (n := v.length * 3 - 3 * K) (step := 1)
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [this]; congr 1; omega
  rw [e2, List.map_append, outsideQK, List.map_map, List.range_eq_range']
  congr 1
  · apply List.map_congr_left
    intro k hk
    rw [List.mem_range'_1] at hk
    simp [show k < 3 * K by omega]
  · apply List.map_congr_left
    intro k hk
    rw [List.mem_range'_1] at hk
    simp [show ¬ k < 3 * K by omega]

theorem sgRow_fColInv_inl (hB : BlockS K E i offs sg B t (flagOf flags)) {k : ℕ} (hk : k < 3 * K) :
    sgRow K S (B ++ t) (sfColInv (B ++ t) hB.len_pos (Sum.inl k)) = Sum.inl (S.col k).1 := by
  have h3 := kc_ltK hk
  simp only [sfColInv]
  rw [sCornerOf_eq _ _ (by have := hB.len_append; omega)]
  unfold sgRow
  rw [if_pos h3]
  simp only [cidx_kc]

theorem sgRow_symm_fColInv_inl (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {k : ℕ} (hk : k < 3 * K) :
    sgRow K S (B ++ t) ((sM (B ++ t)).symm (sfColInv (B ++ t) hB.len_pos (Sum.inl k))) =
      Sum.inl (S.col k).2 := by
  have h3 := kc_ltK hk
  simp only [sfColInv]
  rw [sCornerOf_eq _ _ (by have := hB.len_append; omega), sgRow_symm_block S hB hS _ h3]
  simp only [cidx_kc]

theorem sInitGrid_O (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (c : BCol) :
    (sInitGrid S hB hS).O c = sgRow K S (B ++ t) (sfColInv (B ++ t) hB.len_pos c) := rfl

theorem sInitGrid_X (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (c : BCol) :
    (sInitGrid S hB hS).X c =
      sgRow K S (B ++ t) ((sM (B ++ t)).symm (sfColInv (B ++ t) hB.len_pos c)) := rfl

theorem sInitGrid_rows (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) :
    (sInitGrid S hB hS).rows =
      (sRows (B ++ t) (skappa K S (B ++ t))).map (sgRow K S (B ++ t)) := rfl

/-- The height of a window label is the height of its arc. -/
theorem slvl_of_gRow (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {p : Fin (B ++ t).length × Fin 3} {x : ℕ}
    (h : sgRow K S (B ++ t) p = Sum.inl x) :
    (B ++ t).oHeight2 p = 2 * i + lvlRelS S offs sg x := by
  have hS' := hS
  obtain ⟨hlen, holn, hxln, -, -, -, -, -, -, -, -⟩ := hS'
  unfold sgRow at h
  split_ifs at h with h1 h2
  · simp only [Sum.inl.injEq] at h; subst h
    have hk : cidx p.1.val p.2 < S.cols.length := by rw [hlen]; exact cidx_ltK h1 p.2
    unfold lvlRelS
    rw [if_pos (mem_ol S hk), ol_idxOf S holn hk, kc_cidx]
    dsimp only
    rw [← hB.oH_block' h1 p.1.isLt p.2]
  · simp only [Sum.inl.injEq] at h; subst h
    have hnot := sxlabel_not_mem_ol S hB hS p (by omega) h2
    have hk : cidx (sM (B ++ t) p).1.val (sM (B ++ t) p).2 < S.cols.length := by
      rw [hlen]; exact cidx_ltK h2 _
    unfold lvlRelS
    rw [if_neg hnot, xl_idxOf S hxln hk, kc_cidx]
    dsimp only
    rw [← hB.xH_block' h2 (sM (B ++ t) p).1.isLt (sM (B ++ t) p).2, ← sM_height]

theorem skappa_inl (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {p : Fin (B ++ t).length × Fin 3} {x : ℕ}
    (h : sgRow K S (B ++ t) p = Sum.inl x) :
    skappa K S (B ++ t) p = (2 * i + lvlRelS S offs sg x) * BIG (B ++ t).length + S.ri x := by
  unfold skappa
  rw [slvl_of_gRow S hB hS h, h]
  rfl

/-- The rows of the initial grid are sorted by the keys of their corners. -/
theorem sInitGrid_rows_pairwise (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) :
    (sInitGrid S hB hS).rows.Pairwise (fun r r' =>
      skappa K S (B ++ t) (sgRowInv S (B ++ t) hB.len_pos r) <
        skappa K S (B ++ t) (sgRowInv S (B ++ t) hB.len_pos r')) := by
  rw [sInitGrid_rows, List.pairwise_map]
  have h := (sRows_sorted (B ++ t) (skappa K S (B ++ t))).and
    (List.nodup_iff_pairwise_ne.mp (sRows_nodup (B ++ t) (skappa K S (B ++ t))))
  refine h.imp fun {a b} hab => ?_
  rw [sgRowInv_sgRow S hB hS, sgRowInv_sgRow S hB hS]
  exact lt_of_le_of_ne hab.1 (fun e => hab.2 (skappa_inj S hB hS e))

theorem mem_sInitGrid_rows (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (r : BRow) :
    r ∈ (sInitGrid S hB hS).rows ↔ ∃ p, sgRow K S (B ++ t) p = r := by
  rw [sInitGrid_rows, List.mem_map]
  exact ⟨fun ⟨p, _, hp⟩ => ⟨p, hp⟩, fun ⟨p, hp⟩ => ⟨p, mem_sRows _ _ p, hp⟩⟩

theorem sInitGrid_lefts (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) : lefts (sInitGrid S hB hS).rows = S.rows := by
  have hS' := hS
  obtain ⟨hlen, -, -, hrn, -, -, hrm, -, -, -, hsort⟩ := hS'
  let Kx : ℕ → ℕ := fun x => (2 * i + lvlRelS S offs sg x) * BIG (B ++ t).length + S.ri x
  apply eq_of_pairwise_key (K := Kx)
  · have h := (List.Pairwise.and_mem.mp (sInitGrid_rows_pairwise S hB hS))
    refine h.filterMap _ ?_
    rintro a a' ⟨ha, ha', hlt⟩ b hb b' hb'
    rcases a with x | e
    · rcases a' with y | e'
      · simp only [Sum.getLeft?_inl, Option.some.injEq] at hb hb'
        subst hb; subst hb'
        obtain ⟨p, hp⟩ := (mem_sInitGrid_rows S hB hS _).mp ha
        obtain ⟨p', hp'⟩ := (mem_sInitGrid_rows S hB hS _).mp ha'
        rw [← hp, ← hp', sgRowInv_sgRow S hB hS, sgRowInv_sgRow S hB hS, skappa_inl S hB hS hp,
          skappa_inl S hB hS hp'] at hlt
        exact hlt
      · simp at hb'
    · simp at hb
  · have h1 := hsort.and (pairwise_idxOf_lt hrn)
    refine h1.imp fun {a b} hab => ?_
    have := Nat.mul_le_mul_right (BIG (B ++ t).length)
      (show 2 * i + lvlRelS S offs sg a ≤ 2 * i + lvlRelS S offs sg b by omega)
    simp only [Kx, WState.ri]
    omega
  · intro x
    rw [mem_lefts, mem_sInitGrid_rows]
    constructor
    · rintro ⟨p, hp⟩; exact sgRow_inl_mem S hS hp
    · intro hx
      rcases hrm x hx with ho | hxl
      · obtain ⟨hj, hjx⟩ := exists_of_mem_ol S ho
        exact ⟨_, (sgRow_fColInv_inl S hB (k := (Ol S).idxOf x) (by omega)).trans (by rw [hjx])⟩
      · obtain ⟨hj, hjx⟩ := exists_of_mem_xl S hxl
        exact ⟨_, (sgRow_symm_fColInv_inl S hB hS (k := (Xl S).idxOf x) (by omega)).trans
          (by rw [hjx])⟩

/-- The initial grid realizes the initial window state. -/
theorem sInitGrid_real (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) :
    Real S (sInitGrid S hB hS) (List.range (3 * K)) (outsideQK K (B ++ t).length) where
  cols := sCols_map_sfCol _ (by have := hB.len_append; omega)
  len := by simp [hS.1]
  marks p hp := by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
    simp only [List.length_zip, List.length_range] at hk
    have hk9 : k < 3 * K := by omega
    simp only [List.getElem_zip, List.getElem_range]
    rw [← col_eq_getElem S (by rw [hS.1]; exact hk9)]
    exact ⟨sgRow_fColInv_inl S hB hk9, sgRow_symm_fColInv_inl S hB hS hk9⟩
  rows := sInitGrid_lefts S hB hS

end InitReal

end OnLeConjecture.KnotTheory.SignedGrid
