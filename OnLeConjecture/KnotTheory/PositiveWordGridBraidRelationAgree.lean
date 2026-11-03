/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationInit

/-! # The initial grids of `B₁ ++ t` and `B₂ ++ t` agree outside the window

For two blocks `B₁` and `B₂` of three letters involving the same ranks, and initial window states
satisfying `BraidWindow.InitOK` and the finite comparison `BraidWindow.PairOK`, the initial grids
of `B₁ ++ t` and `B₂ ++ t` have the same markings in the outside columns
(`BraidWindow.agree_O`, `BraidWindow.agree_X`) and the same connecting and external rows in the
same order (`BraidWindow.agree_rows`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.BraidWindow

open TauCeti

/-! ### Labels of the outside arcs -/

section Outside

variable {m : ℕ} (S : WState) {i : Fin (m - 1)} {offs : List ℕ} {B t : PositiveAdjacentWord m}
  {flags : List Bool}

theorem corner_ne_zero_of_in {w : PositiveAdjacentWord m} (p : Fin w.length × Fin 3)
    (hp : 3 ≤ p.1.val) (hq : (positiveRectilinearWordMatching w p).1.val < 3) : p.2 ≠ 0 := by
  intro h0
  have := positiveRectilinearWordMatching_middle w p.1
  rw [← h0] at this
  simp only [Prod.mk.eta] at this
  rw [this] at hq
  dsimp only at hq
  omega

/-- The label of an arc leaving an outside corner. -/
theorem gRow_out (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (p : Fin (B ++ t).length × Fin 3) (hp : 3 ≤ p.1.val) :
    gRow (B ++ t) S p = if (positiveRectilinearWordMatching (B ++ t) p).1.val < 3 then
      Sum.inl (20 + (outRank (B ++ t) p - i.val)) else Sum.inr (p.1.val, p.2) := by
  have hC2 := hS.2.2.2.2.2.2.2.2.2.1
  unfold gRow
  rw [if_neg (by omega)]
  split_ifs with h2
  · have hnot := xlabel_not_mem_ol S hB hS p hp h2
    have hc0 := corner_ne_zero_of_in p hp h2
    obtain ⟨-, hrank⟩ := matching_inRank (B ++ t) p hc0
    have h20 := hC2 _ (mem_corners9 h2 _) hnot
    dsimp only at h20
    rw [h20, ← hrank]
    generalize positiveRectilinearWordMatching (B ++ t) p = q at *
    have hv := hB.val q.1.val (by rw [hB.len]; exact h2)
    have hget : (B ++ t)[q.1.val] = B[q.1.val]'(by rw [hB.len]; exact h2) :=
      List.getElem_append_left _
    unfold inRank inRel
    rw [hget, hv]
    congr 2
    split_ifs <;> omega
  · rfl

/-- The label of an arc entering an outside corner. -/
theorem gRow_symm_out (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (q : Fin (B ++ t).length × Fin 3) (hq : 3 ≤ q.1.val) :
    gRow (B ++ t) S ((positiveRectilinearWordMatching (B ++ t)).symm q) =
      if ((positiveRectilinearWordMatching (B ++ t)).symm q).1.val < 3 then
        Sum.inl (30 + (inRank (B ++ t) q - i.val))
      else Sum.inr (((positiveRectilinearWordMatching (B ++ t)).symm q).1.val,
        ((positiveRectilinearWordMatching (B ++ t)).symm q).2) := by
  have hbm := hS.2.2.2.2.2.2.2.1
  have hMp : positiveRectilinearWordMatching (B ++ t)
      ((positiveRectilinearWordMatching (B ++ t)).symm q) = q := Equiv.apply_symm_apply _ _
  generalize (positiveRectilinearWordMatching (B ++ t)).symm q = p at hMp ⊢
  unfold gRow
  split_ifs with h1 h2
  · have hb := hbm (p.1.val, p.2) (mem_corners9 h1 p.2)
    unfold bmOK at hb
    rcases hBM : BM offs (flagOf flags) p.1.val p.2 with _ | q'
    · rw [hBM] at hb
      simp only [beq_iff_eq] at hb
      rw [hb]
      have hc0 : p.2 ≠ 0 := by
        intro h0
        have := positiveRectilinearWordMatching_middle (B ++ t) p.1
        rw [← h0] at this
        simp only [Prod.mk.eta] at this
        rw [this] at hMp
        rw [← hMp] at hq
        exact absurd hq (by simp only; omega)
      obtain ⟨-, hrank⟩ := matching_inRank (B ++ t) p hc0
      rw [hMp] at hrank
      rw [hrank]
      have hv := hB.val p.1.val (by rw [hB.len]; exact h1)
      have hget : (B ++ t)[p.1.val] = B[p.1.val]'(by rw [hB.len]; exact h1) :=
        List.getElem_append_left _
      unfold outRank rankOff
      rw [hget, hv]
      congr 2
      split_ifs <;> omega
    · exfalso
      obtain ⟨hq3, hq'3, hM⟩ := hB.blockM_some p.1.isLt h1 p.2 hBM
      simp only [Fin.eta, Prod.mk.eta, hMp] at hM
      rw [hM] at hq
      exact absurd hq (by simp only; omega)
  · exfalso; rw [hMp] at h2; omega
  · rfl

theorem mem_rows_inr (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (a : ℕ × Fin 3) : Sum.inr a ∈ (initGrid S hB hS).rows ↔
      ∃ h : a.1 < (B ++ t).length, 3 ≤ a.1 ∧
        3 ≤ (positiveRectilinearWordMatching (B ++ t) (⟨a.1, h⟩, a.2)).1.val := by
  rw [mem_initGrid_rows]
  constructor
  · rintro ⟨p, hp⟩
    unfold gRow at hp
    split_ifs at hp with h1 h2
    simp only [Sum.inr.injEq] at hp
    subst hp
    exact ⟨p.1.isLt, by omega, by simp only [Fin.eta, Prod.mk.eta]; omega⟩
  · rintro ⟨h, h3, hM⟩
    refine ⟨(⟨a.1, h⟩, a.2), ?_⟩
    unfold gRow
    rw [if_neg (by simp only; omega), if_neg (by omega)]

theorem mem_rows_inl (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags)
    (x : ℕ) : Sum.inl x ∈ (initGrid S hB hS).rows ↔ x ∈ S.rows := by
  rw [← mem_lefts, initGrid_lefts]

end Outside

/-! ### Comparison of two initial grids -/

/-- The connecting labels. -/
def connL : List ℕ := [20, 21, 22, 30, 31, 32]

theorem mem_connL {x : ℕ} (h : isConn x = true) : x ∈ connL := by
  unfold isConn at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [connL, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The finite comparison of two initial window states: the same connecting labels, at the same
levels and in the same order. -/
def PairOK (S₁ : WState) (offs₁ : List ℕ) (S₂ : WState) (offs₂ : List ℕ) : Prop :=
  (∀ x ∈ connL, x ∈ S₁.rows ↔ x ∈ S₂.rows) ∧
  (∀ x ∈ connL, x ∈ S₁.rows → lvlRel S₁ offs₁ x = lvlRel S₂ offs₂ x) ∧
  (∀ x ∈ connL, ∀ y ∈ connL, x ∈ S₁.rows → y ∈ S₁.rows →
    (S₁.ri x < S₁.ri y ↔ S₂.ri x < S₂.ri y))

instance (S₁ : WState) (offs₁ : List ℕ) (S₂ : WState) (offs₂ : List ℕ) :
    Decidable (PairOK S₁ offs₁ S₂ offs₂) := by
  unfold PairOK; infer_instance

theorem getElem_append_three {m : ℕ} {B₁ B₂ t : PositiveAdjacentWord m} (h₁ : B₁.length = 3)
    (h₂ : B₂.length = 3) (k : ℕ) (hk₁ : k < (B₁ ++ t).length) (hk₂ : k < (B₂ ++ t).length)
    (hk : 3 ≤ k) : (B₁ ++ t)[k] = (B₂ ++ t)[k] := by
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
  simp only [h₁, h₂]

theorem lex_transfer {N a a' b₁ b₁' b₂ b₂' : ℕ} (h₁ : b₁ < N) (h₂' : b₂' < N)
    (h : b₂ < b₂' → b₁ < b₁') (hlt : a * N + b₂ < a' * N + b₂') : a * N + b₁ < a' * N + b₁' := by
  rcases Nat.lt_trichotomy a a' with ha | ha | ha
  · have := Nat.mul_le_mul_right N (show a + 1 ≤ a' by omega)
    rw [Nat.add_one_mul] at this
    omega
  · subst ha
    have := h (by omega)
    omega
  · have := Nat.mul_le_mul_right N (show a' + 1 ≤ a by omega)
    rw [Nat.add_one_mul] at this
    omega

section Agree

variable {m : ℕ} (S₁ S₂ : WState) {i : Fin (m - 1)} {offs₁ offs₂ : List ℕ}
  {B₁ B₂ t : PositiveAdjacentWord m} {flags : List Bool}

/-- The key of a row label of an initial grid, as a formula. -/
def Kf (S : WState) (offs : List ℕ) (iv : ℕ) (t : PositiveAdjacentWord m) (N : ℕ) : BRow → ℕ
  | Sum.inl x => (2 * iv + lvlRel S offs x) * N + S.ri x
  | Sum.inr a => (2 * ((t[a.1 - 3]?).map Fin.val).getD 0 +
      (if a.2 = 0 then 1 else if a.2 = 1 then 0 else 2)) * N + (16 + cidx a.1 a.2)

theorem rows_pairwise_Kf {offs : List ℕ} {B : PositiveAdjacentWord m} (S : WState)
    (hB : BlockHyp i offs B t (flagOf flags)) (hS : InitOK S offs flags) :
    (initGrid S hB hS).rows.Pairwise (fun r r' =>
      Kf S offs i.val t (BIG (3 + t.length)) r < Kf S offs i.val t (BIG (3 + t.length)) r') := by
  have h := List.Pairwise.and_mem.mp (initGrid_rows_pairwise S hB hS)
  refine h.imp fun {r r'} ⟨hr, hr', hlt⟩ => ?_
  have hBIG : BIG (B ++ t).length = BIG (3 + t.length) := by rw [hB.len_append]
  have hK : ∀ r ∈ (initGrid S hB hS).rows, kappa (B ++ t) S (gRowInv (B ++ t) S hB.len_pos r) =
      Kf S offs i.val t (BIG (3 + t.length)) r := by
    intro r hr
    obtain ⟨p, hp⟩ := (mem_initGrid_rows S hB hS r).mp hr
    rw [← hp, gRowInv_gRow S hB hS]
    rw [hp]
    rcases r with x | a
    · rw [kappa_inl S hB hS hp, hBIG]; rfl
    · unfold gRow at hp
      split_ifs at hp with h1 h2
      simp only [Sum.inr.injEq] at hp
      subst hp
      unfold kappa
      have hget : (B ++ t)[p.1.val] = t[p.1.val - 3]'(by have := hB.len_append; omega) := by
        rw [List.getElem_append_right (by rw [hB.len]; omega)]
        simp only [hB.len]
      have hopt : t[p.1.val - 3]? = some (t[p.1.val - 3]'(by have := hB.len_append; omega)) :=
        List.getElem?_eq_getElem _
      unfold gRow
      rw [if_neg h1, if_neg h2, hBIG]
      simp only [Kf, tbR, lvl2, hget, hopt, Option.map_some, Option.getD_some]
  rw [← hK r hr, ← hK r' hr']
  exact hlt

/-- The outside agreement of the matchings of `B₁ ++ t` and `B₂ ++ t`. -/
structure AgreeHyp (hB₁ : BlockHyp i offs₁ B₁ t (flagOf flags))
    (hB₂ : BlockHyp i offs₂ B₂ t (flagOf flags)) : Prop where
  blk : ∀ r : Fin m, (∃ k, ∃ h₁ : k < (B₁ ++ t).length, k < 3 ∧
      (r = adjacentLower (B₁ ++ t)[k] ∨ r = adjacentUpper (B₁ ++ t)[k])) ↔
    (∃ k, ∃ h₂ : k < (B₂ ++ t).length, k < 3 ∧
      (r = adjacentLower (B₂ ++ t)[k] ∨ r = adjacentUpper (B₂ ++ t)[k]))

variable {hB₁ : BlockHyp i offs₁ B₁ t (flagOf flags)} {hB₂ : BlockHyp i offs₂ B₂ t (flagOf flags)}

theorem AgreeHyp.symm (ha : AgreeHyp hB₁ hB₂) : AgreeHyp hB₂ hB₁ := ⟨fun r => (ha.blk r).symm⟩

theorem AgreeHyp.out (ha : AgreeHyp hB₁ hB₂) {h : ℕ} (h₁ : h < (B₁ ++ t).length)
    (h₂ : h < (B₂ ++ t).length) (hh3 : 3 ≤ h) (c : Fin 3) :
    (3 ≤ (positiveRectilinearWordMatching (B₁ ++ t) (⟨h, h₁⟩, c)).1.val ↔
        3 ≤ (positiveRectilinearWordMatching (B₂ ++ t) (⟨h, h₂⟩, c)).1.val) ∧
      (3 ≤ (positiveRectilinearWordMatching (B₁ ++ t) (⟨h, h₁⟩, c)).1.val →
        (positiveRectilinearWordMatching (B₁ ++ t) (⟨h, h₁⟩, c)).1.val =
          (positiveRectilinearWordMatching (B₂ ++ t) (⟨h, h₂⟩, c)).1.val ∧
        (positiveRectilinearWordMatching (B₁ ++ t) (⟨h, h₁⟩, c)).2 =
          (positiveRectilinearWordMatching (B₂ ++ t) (⟨h, h₂⟩, c)).2) :=
  matching_outside_agree (B₁ ++ t) (B₂ ++ t) (getElem_append_three hB₁.len hB₂.len)
    (by rw [hB₁.len_append, hB₂.len_append]) ha.blk h₁ h₂ hh3 c

theorem AgreeHyp.symm_out (ha : AgreeHyp hB₁ hB₂) {h : ℕ} (h₁ : h < (B₁ ++ t).length)
    (h₂ : h < (B₂ ++ t).length) (hh3 : 3 ≤ h) (c : Fin 3)
    (hs : 3 ≤ ((positiveRectilinearWordMatching (B₁ ++ t)).symm (⟨h, h₁⟩, c)).1.val) :
    ((positiveRectilinearWordMatching (B₁ ++ t)).symm (⟨h, h₁⟩, c)).1.val =
        ((positiveRectilinearWordMatching (B₂ ++ t)).symm (⟨h, h₂⟩, c)).1.val ∧
      ((positiveRectilinearWordMatching (B₁ ++ t)).symm (⟨h, h₁⟩, c)).2 =
        ((positiveRectilinearWordMatching (B₂ ++ t)).symm (⟨h, h₂⟩, c)).2 := by
  set a := (positiveRectilinearWordMatching (B₁ ++ t)).symm (⟨h, h₁⟩, c) with ha_def
  have hMa : positiveRectilinearWordMatching (B₁ ++ t) a = (⟨h, h₁⟩, c) := by
    rw [ha_def]; exact Equiv.apply_symm_apply _ _
  have ha₂ : a.1.val < (B₂ ++ t).length := by
    have := a.1.isLt; have := hB₁.len_append; have := hB₂.len_append; omega
  have ag := ha.out a.1.isLt ha₂ hs a.2
  simp only [Fin.eta, Prod.mk.eta, hMa] at ag
  obtain ⟨hiff, himp⟩ := ag
  obtain ⟨e1, e2⟩ := himp hh3
  have hM₂ : positiveRectilinearWordMatching (B₂ ++ t) (⟨a.1.val, ha₂⟩, a.2) = (⟨h, h₂⟩, c) := by
    apply Prod.ext
    · exact Fin.ext e1.symm
    · exact e2.symm
  rw [← hM₂, Equiv.symm_apply_apply]
  exact ⟨rfl, rfl⟩

theorem agree_O (hS₁ : InitOK S₁ offs₁ flags) (hS₂ : InitOK S₂ offs₂ flags)
    (ha : AgreeHyp hB₁ hB₂) {q : ℕ × Fin 3} (hq : q ∈ outsideQ (3 + t.length)) :
    (initGrid S₁ hB₁ hS₁).O (Sum.inr q) = (initGrid S₂ hB₂ hS₂).O (Sum.inr q) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL₁ := hB₁.len_append
  have hL₂ := hB₂.len_append
  have h3 : 3 ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B₁ ++ t).length := by simp only [kc]; omega
  have h₂ : (kc k).1 < (B₂ ++ t).length := by simp only [kc]; omega
  rw [initGrid_O, initGrid_O]
  simp only [fColInv]
  rw [cornerOf_eq _ _ h₁, cornerOf_eq _ _ h₂, gRow_out S₁ hB₁ hS₁ _ h3, gRow_out S₂ hB₂ hS₂ _ h3]
  have ag := ha.out h₁ h₂ h3 (kc k).2
  have hor : outRank (B₁ ++ t) (⟨(kc k).1, h₁⟩, (kc k).2) =
      outRank (B₂ ++ t) (⟨(kc k).1, h₂⟩, (kc k).2) := by
    unfold outRank
    simp only
    rw [getElem_append_three hB₁.len hB₂.len _ h₁ h₂ h3]
  by_cases hc : (positiveRectilinearWordMatching (B₁ ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).1.val < 3
  · have hc' :
        (positiveRectilinearWordMatching (B₂ ++ t) (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < 3 := by
      by_contra hh
      have := ag.1.mpr (by omega)
      omega
    rw [if_pos hc, if_pos hc', hor]
  · have hc' : ¬ (positiveRectilinearWordMatching (B₂ ++ t) (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < 3 :=
      fun hh => hc (by have := ag.1; omega)
    rw [if_neg hc, if_neg hc']

theorem agree_X (hS₁ : InitOK S₁ offs₁ flags) (hS₂ : InitOK S₂ offs₂ flags)
    (ha : AgreeHyp hB₁ hB₂) {q : ℕ × Fin 3} (hq : q ∈ outsideQ (3 + t.length)) :
    (initGrid S₁ hB₁ hS₁).X (Sum.inr q) = (initGrid S₂ hB₂ hS₂).X (Sum.inr q) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL₁ := hB₁.len_append
  have hL₂ := hB₂.len_append
  have h3 : 3 ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B₁ ++ t).length := by simp only [kc]; omega
  have h₂ : (kc k).1 < (B₂ ++ t).length := by simp only [kc]; omega
  rw [initGrid_X, initGrid_X]
  simp only [fColInv]
  rw [cornerOf_eq _ _ h₁, cornerOf_eq _ _ h₂, gRow_symm_out S₁ hB₁ hS₁ _ h3,
    gRow_symm_out S₂ hB₂ hS₂ _ h3]
  have hir : inRank (B₁ ++ t) (⟨(kc k).1, h₁⟩, (kc k).2) =
      inRank (B₂ ++ t) (⟨(kc k).1, h₂⟩, (kc k).2) := by
    unfold inRank
    simp only
    rw [getElem_append_three hB₁.len hB₂.len _ h₁ h₂ h3]
  have s₁ := ha.symm_out h₁ h₂ h3 (kc k).2
  have s₂ := ha.symm.symm_out h₂ h₁ h3 (kc k).2
  by_cases hc : ((positiveRectilinearWordMatching (B₁ ++ t)).symm
      (⟨(kc k).1, h₁⟩, (kc k).2)).1.val < 3
  · have hc' : ((positiveRectilinearWordMatching (B₂ ++ t)).symm
        (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < 3 := by
      by_contra hh
      have := (s₂ (by omega)).1
      omega
    rw [if_pos hc, if_pos hc', hir]
  · obtain ⟨e1, e2⟩ := s₁ (by omega)
    have hc' : ¬ ((positiveRectilinearWordMatching (B₂ ++ t)).symm
        (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < 3 := by omega
    rw [if_neg hc, if_neg hc', e1, e2]

theorem agree_rows (hS₁ : InitOK S₁ offs₁ flags) (hS₂ : InitOK S₂ offs₂ flags)
    (ha : AgreeHyp hB₁ hB₂) (hP : PairOK S₁ offs₁ S₂ offs₂) :
    (initGrid S₁ hB₁ hS₁).rows.filter nonInt = (initGrid S₂ hB₂ hS₂).rows.filter nonInt := by
  obtain ⟨hPm, hPl, hPo⟩ := hP
  set N := BIG (3 + t.length) with hN
  have hN16 : 16 ≤ N := by simp only [hN, BIG]; omega
  have hri : ∀ (S : WState) x, S.rows.length < 16 → S.ri x < 16 := fun S x h => by
    have := List.idxOf_le_length (a := x) (l := S.rows); simp only [WState.ri]; omega
  have hS₁16 : S₁.rows.length < 16 := hS₁.2.2.2.2.1
  have hS₂16 : S₂.rows.length < 16 := hS₂.2.2.2.2.1
  apply eq_of_pairwise_key (K := Kf S₁ offs₁ i.val t N)
  · exact (rows_pairwise_Kf S₁ hB₁ hS₁).filter _
  · have h := List.Pairwise.and_mem.mp ((rows_pairwise_Kf S₂ hB₂ hS₂).filter nonInt)
    refine h.imp fun {r r'} ⟨hr, hr', hlt⟩ => ?_
    rw [List.mem_filter] at hr hr'
    have hlev : ∀ x, Sum.inl x ∈ (initGrid S₂ hB₂ hS₂).rows → nonInt (Sum.inl x) = true →
        2 * i.val + lvlRel S₂ offs₂ x = 2 * i.val + lvlRel S₁ offs₁ x ∧ x ∈ S₁.rows := by
      intro x hx hc
      have hxc := mem_connL hc
      have hx₂ := (mem_rows_inl S₂ hB₂ hS₂ x).mp hx
      have hx₁ := (hPm x hxc).mpr hx₂
      exact ⟨by rw [hPl x hxc hx₁], hx₁⟩
    have hbd : ∀ a, Sum.inr a ∈ (initGrid S₂ hB₂ hS₂).rows → 16 + cidx a.1 a.2 < N := by
      intro a ha'
      obtain ⟨h, -, -⟩ := (mem_rows_inr S₂ hB₂ hS₂ a).mp ha'
      rw [hB₂.len_append] at h
      have := a.2.isLt
      simp only [hN, BIG, cidx]
      omega
    rcases r with x | a <;> rcases r' with y | b
    · obtain ⟨ex, hx₁⟩ := hlev x hr.1 hr.2
      obtain ⟨ey, hy₁⟩ := hlev y hr'.1 hr'.2
      simp only [Kf] at hlt ⊢
      rw [ex, ey] at hlt
      exact lex_transfer ((hri S₁ x hS₁16).trans_le hN16) ((hri S₂ y hS₂16).trans_le hN16)
        (fun h => (hPo x (mem_connL hr.2) y (mem_connL hr'.2) hx₁ hy₁).mpr h) hlt
    · obtain ⟨ex, -⟩ := hlev x hr.1 hr.2
      simp only [Kf] at hlt ⊢
      rw [ex] at hlt
      have := hri S₁ x hS₁16
      exact lex_transfer (by omega) (hbd b hr'.1) (fun _ => by omega) hlt
    · obtain ⟨ey, -⟩ := hlev y hr'.1 hr'.2
      simp only [Kf] at hlt ⊢
      rw [ey] at hlt
      have := hri S₂ y hS₂16
      exact lex_transfer (hbd a hr.1) (by omega) (fun h => by omega) hlt
    · exact hlt
  · intro r
    rw [List.mem_filter, List.mem_filter]
    rcases r with x | a
    · rw [mem_rows_inl, mem_rows_inl]
      constructor
      · rintro ⟨hx, hc⟩; exact ⟨(hPm x (mem_connL hc)).mp hx, hc⟩
      · rintro ⟨hx, hc⟩; exact ⟨(hPm x (mem_connL hc)).mpr hx, hc⟩
    · rw [mem_rows_inr, mem_rows_inr]
      have hL₁ := hB₁.len_append
      have hL₂ := hB₂.len_append
      constructor
      · rintro ⟨⟨h₁, h3, hM⟩, hc⟩
        have h₂ : a.1 < (B₂ ++ t).length := by omega
        exact ⟨⟨h₂, h3, (ha.out h₁ h₂ h3 a.2).1.mp hM⟩, hc⟩
      · rintro ⟨⟨h₂, h3, hM⟩, hc⟩
        have h₁ : a.1 < (B₁ ++ t).length := by omega
        exact ⟨⟨h₁, h3, (ha.out h₁ h₂ h3 a.2).1.mpr hM⟩, hc⟩

end Agree

end OnLeConjecture.KnotTheory.BraidWindow
