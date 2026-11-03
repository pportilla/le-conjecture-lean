/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesAgree
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationFinal

/-! # From two window sequences to signed word grids

Let `B₁ ++ t` and `B₂ ++ t` be signed words whose blocks `B₁`, `B₂` of `K` letters involve the
same ranks, with initial window states satisfying `SignedGrid.InitOKS` and `SignedGrid.PairOKS`.
If the window sequences lead to final states that agree after renaming internal labels
(`BraidWindow.FinalOK`), then some signed word grids of `B₁ ++ t` and `B₂ ++ t` are related by
grid moves (`SignedGrid.sgrids_of_windows`). This is the signed version of
`BraidWindow.wordGrid_movesTo_of_windows`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

/-! ### Outside markings of the initial grids are connecting or external -/

section OutsideConn

variable {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
  {B t : SignedAdjacentWord m} (S : WState)

theorem sInitGrid_O_inr_nonInt (hE : E ≤ 2) (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K (K + t.length)) :
    nonInt ((sInitGrid S hB hS).O (Sum.inr q)) = true := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL := hB.len_append
  have h3 : K ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B ++ t).length := by simp only [kc]; omega
  rw [sInitGrid_O]
  simp only [sfColInv]
  rw [sCornerOf_eq _ _ h₁, sgRow_out S hB hS _ h3]
  split_ifs with hc
  · have hc0 := scorner_ne_zero_of_in _ h3 hc
    have hx := hB.xH_block' hc (sM (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).1.isLt
      (sM (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).2
    have hx' : (B ++ t).xHeight2 (sM (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)) =
        2 * i + inLvlS offs sg (sM (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).1.val
          (sM (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).2 := hx
    rw [sM_height] at hx'
    have hq2 : (sM (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).2 ≠ 2 := fun e => by
      have h1 := (xHeight2_odd_iff _ _).mpr e
      rw [sM_height] at h1
      exact hc0 ((oHeight2_odd_iff _ _).mp h1)
    have hle := hB.offs_le _ hc
    rw [hx']
    unfold inLvlS inRelS
    rw [if_neg hq2]
    simp only [nonInt]
    apply isConn_add (Or.inl rfl)
    generalize (sM (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).1.val = h at hle ⊢
    split_ifs <;> omega
  · rfl

theorem sInitGrid_X_inr_nonInt (hE : E ≤ 2) (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K (K + t.length)) :
    nonInt ((sInitGrid S hB hS).X (Sum.inr q)) = true := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL := hB.len_append
  have h3 : K ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B ++ t).length := by simp only [kc]; omega
  rw [sInitGrid_X]
  simp only [sfColInv]
  rw [sCornerOf_eq _ _ h₁, sgRow_symm_out S hB hS _ h3]
  split_ifs with hc
  · have hMp : sM (B ++ t) ((sM (B ++ t)).symm (⟨(kc k).1, h₁⟩, (kc k).2)) =
        (⟨(kc k).1, h₁⟩, (kc k).2) := Equiv.apply_symm_apply _ _
    generalize (sM (B ++ t)).symm (⟨(kc k).1, h₁⟩, (kc k).2) = p at hc hMp ⊢
    have hc0 : p.2 ≠ 0 := by
      intro h0
      have := sM_middle (B ++ t) p.1
      rw [← h0] at this
      simp only [Prod.mk.eta] at this
      rw [this] at hMp
      have := congrArg (fun z => z.1.val) hMp
      simp only at this
      omega
    have hO := hB.oH_block hc p.1.isLt hc0
    simp only [Fin.eta, Prod.mk.eta] at hO
    rw [← hMp, sM_height, hO]
    have hle := hB.offs_le _ hc
    have hr := rankOffS_le offs sg p.1.val p.2
    simp only [nonInt]
    apply isConn_add (Or.inr rfl)
    omega
  · rfl

theorem soutsideQ_len {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {fl : ℕ → Bool}
    {B t : SignedAdjacentWord m} (hB : BlockS K E i offs sg B t fl) :
    outsideQK K (B ++ t).length = outsideQK K (K + t.length) := by
  rw [hB.len_append]

end OutsideConn

section Final

variable {K E i : ℕ} {offs₁ offs₂ : List ℕ} {sg₁ sg₂ : List Bool} {flags : List Bool}
  {B₁ B₂ t : SignedAdjacentWord m}

/-- **Two window sequences give grid moves.** -/
theorem sgrids_of_windows (hE : E ≤ 2) (hB₁ : BlockS K E i offs₁ sg₁ B₁ t (flagOf flags))
    (hB₂ : BlockS K E i offs₂ sg₂ B₂ t (flagOf flags)) (ha : AgreeS hB₁ hB₂) (S₁ S₂ : WState)
    (hS₁ : InitOKS K S₁ offs₁ sg₁ flags) (hS₂ : InitOKS K S₂ offs₂ sg₂ flags)
    (hP : PairOKS S₁ offs₁ sg₁ S₂ offs₂ sg₂)
    {ms₁ ms₂ : List WMove} {F₁ F₂ : WState} (hr₁ : run S₁ ms₁ = some F₁)
    (hr₂ : run S₂ ms₂ = some F₂) {σ : List (ℕ × ℕ)} (hF : FinalOK F₁ F₂ σ) :
    ∃ (G₁ : GridDiagram ((B₁ ++ t).length * 3)) (G₂ : GridDiagram ((B₂ ++ t).length * 3)),
      IsSignedWordGrid (B₁ ++ t) G₁ ∧ IsSignedWordGrid (B₂ ++ t) G₂ ∧ G₁.MovesTo G₂ := by
  obtain ⟨hren, hinv, hσ⟩ := hF
  set Q := outsideQK K (K + t.length) with hQ
  have hR₁ := sInitGrid_real S₁ hB₁ hS₁
  rw [soutsideQ_len hB₁] at hR₁
  have hR₂ := sInitGrid_real S₂ hB₂ hS₂
  rw [soutsideQ_len hB₂] at hR₂
  obtain ⟨n₁, W₁, H₁, hH₁, hso₁, hmv₁⟩ := run_sound hR₁ hr₁
  obtain ⟨n₂, W₂, H₂, hH₂, hso₂, hmv₂⟩ := run_sound hR₂ hr₂
  have hFc : F₁.cols = F₂.cols.map fun c => (relab σ c.1, relab σ c.2) := by
    rw [← hren]; rfl
  have hFr : F₁.rows = F₂.rows.map (relab σ) := by rw [← hren]; rfl
  have hlenW : W₂.length = W₁.length := by
    rw [hH₁.len, hH₂.len, hFc, List.length_map]
  have hn : n₂ = n₁ := by
    have e1 := H₁.cols_length
    have e2 := H₂.cols_length
    rw [hH₁.cols] at e1
    rw [hH₂.cols] at e2
    simp only [List.length_append, List.length_map] at e1 e2
    omega
  subst hn
  have hW₁ := hH₁.W_nodup
  have hW₂ := hH₂.W_nodup
  -- the renamed final grid of the second word
  have hf : ∀ c ∈ H₂.cols, colMap W₁ W₂ (colMap W₂ W₁ c) = c := by
    intro c hc
    rcases hH₂.mem_cols hc with ⟨k, hk, rfl⟩ | hq
    · rw [colMap_getElem hW₂ hlenW hk, colMap_getElem hW₁ hlenW.symm (by omega)]
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hq; rfl
  have hg : ∀ r ∈ H₂.rows, gSig (σ.map Prod.swap) (gSig σ r) = r := by
    intro r hr
    rcases r with x | e
    · have hx : x ∈ F₂.rows := by rw [← hH₂.rows]; exact mem_lefts.mpr hr
      simp only [gSig, hinv x hx]
    · rfl
  let H₂' := H₂.relabel (colMap W₂ W₁) (colMap W₁ W₂) (gSig σ) (gSig (σ.map Prod.swap)) hf hg
  have hcols₂' : H₂'.cols = W₁.map Sum.inl ++ Q.map Sum.inr := by
    change H₂.cols.map (colMap W₂ W₁) = _
    rw [hH₂.cols, List.map_append, colMap_map hW₂ hlenW, List.map_map]
    rfl
  -- outside markings of the final grids
  have hout₁ : ∀ q ∈ Q, H₁.O (Sum.inr q) = (sInitGrid S₁ hB₁ hS₁).O (Sum.inr q) ∧
      H₁.X (Sum.inr q) = (sInitGrid S₁ hB₁ hS₁).X (Sum.inr q) := hso₁.1
  have hout₂ : ∀ q ∈ Q, H₂.O (Sum.inr q) = (sInitGrid S₂ hB₂ hS₂).O (Sum.inr q) ∧
      H₂.X (Sum.inr q) = (sInitGrid S₂ hB₂ hS₂).X (Sum.inr q) := hso₂.1
  have hnon₁ : ∀ q ∈ Q, nonInt (H₁.O (Sum.inr q)) = true ∧ nonInt (H₁.X (Sum.inr q)) = true :=
    fun q hq => by
      rw [(hout₁ q hq).1, (hout₁ q hq).2]
      exact ⟨sInitGrid_O_inr_nonInt S₁ hE hB₁ hS₁ hq, sInitGrid_X_inr_nonInt S₁ hE hB₁ hS₁ hq⟩
  have hmv := LabeledGrid.movesTo_of_shuffle freeR (fun r => r.isLeft)
    (fun r hr => by rcases r with x | e <;> simp_all [freeR]) H₁ H₂'
    (by rw [hH₁.cols, hcols₂'])
    (fun c hc => by
      change H₁.O c = gSig σ (H₂.O (colMap W₁ W₂ c))
      rcases hH₁.mem_cols hc with ⟨k, hk, rfl⟩ | hq
      · rw [colMap_getElem hW₁ hlenW.symm hk, hH₁.O_w k hk, hH₂.O_w k (by omega)]
        have hk' : k < F₂.cols.length := by rw [← hH₂.len]; omega
        simp only [gSig, WState.col, hFc, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some]
      · obtain ⟨q, hqQ, rfl⟩ := List.mem_map.mp hq
        change H₁.O (Sum.inr q) = gSig σ (H₂.O (Sum.inr q))
        rw [(hout₁ q hqQ).1, (hout₂ q hqQ).1, sagree_O S₁ S₂ hS₁ hS₂ ha hqQ,
          gSig_nonInt hσ (sInitGrid_O_inr_nonInt S₂ hE hB₂ hS₂ hqQ)])
    (fun c hc => by
      change H₁.X c = gSig σ (H₂.X (colMap W₁ W₂ c))
      rcases hH₁.mem_cols hc with ⟨k, hk, rfl⟩ | hq
      · rw [colMap_getElem hW₁ hlenW.symm hk, hH₁.X_w k hk, hH₂.X_w k (by omega)]
        have hk' : k < F₂.cols.length := by rw [← hH₂.len]; omega
        simp only [gSig, WState.col, hFc, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some]
      · obtain ⟨q, hqQ, rfl⟩ := List.mem_map.mp hq
        change H₁.X (Sum.inr q) = gSig σ (H₂.X (Sum.inr q))
        rw [(hout₁ q hqQ).2, (hout₂ q hqQ).2, sagree_X S₁ S₂ hS₁ hS₂ ha hqQ,
          gSig_nonInt hσ (sInitGrid_X_inr_nonInt S₂ hE hB₂ hS₂ hqQ)])
    (fun a b hfa hwb => by
      rcases a with x | e
      · rcases b with y | b
        · simp at hwb
        · exact rowsNonint_free hH₁ hnon₁ (by simpa [freeR] using hfa) b
      · simp [freeR] at hfa)
    (by
      rw [List.filter_congr (fun r _ => not_freeR r), List.filter_congr (fun r _ => not_freeR r),
        hso₁.2, sagree_rows S₁ S₂ hS₁ hS₂ ha hP, ← hso₂.2]
      change _ = (H₂.rows.map (gSig σ)).filter nonInt
      rw [List.filter_map]
      have e1 : (nonInt ∘ gSig σ) = nonInt := funext (nonInt_gSig hσ)
      rw [e1]
      symm
      have hfix : ∀ r ∈ H₂.rows.filter nonInt, gSig σ r = r :=
        fun r hr => gSig_nonInt hσ (List.mem_filter.mp hr).2
      exact (List.map_congr_left (g := fun r => r) hfix).trans (List.map_id' _))
    (by
      rw [filter_isLeft, filter_isLeft, hH₁.rows]
      change _ = (lefts (H₂.rows.map (gSig σ))).map Sum.inl
      rw [lefts_map_gSig, hH₂.rows, ← hFr])
  have hmv' : H₂'.toGrid = H₂.toGrid := LabeledGrid.toGrid_relabel _ _ _ _ _ _ _
  rw [hmv'] at hmv
  exact ⟨_, _, sInitGrid_signed S₁ hB₁ hS₁, sInitGrid_signed S₂ hB₂ hS₂,
    (hmv₁.trans hmv).trans hmv₂.symm⟩

end Final

end OnLeConjecture.KnotTheory.SignedGrid
