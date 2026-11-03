/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationAgree
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationSound

/-! # From two window sequences to grid moves

Let `B₁ ++ t` and `B₂ ++ t` be words whose blocks `B₁`, `B₂` of three letters involve the same
ranks, with initial window states `S₁`, `S₂` satisfying the finite checks `InitOK` and `PairOK`.
If the window sequences `ms₁`, `ms₂` lead from `S₁`, `S₂` to final states `F₁`, `F₂` that agree
after renaming internal labels (`FinalOK`), then the selected grids of `B₁ ++ t` and `B₂ ++ t`
are related by grid moves (`BraidWindow.wordGrid_movesTo_of_windows`). This is the final step of
the proof of `docs/route-n/J09-word-grid-moves.tex`, Proposition *braid*: the final grids agree
outside the window, and their internal rows commute with the external rows. All results are
unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.BraidWindow

open TauCeti

/-! ### Renaming window labels -/

/-- Renaming of window labels along a finite list of pairs. -/
def relab (σ : List (ℕ × ℕ)) (n : ℕ) : ℕ := (σ.lookup n).getD n

/-- Renaming of a window state. -/
def renameS (σ : List (ℕ × ℕ)) (S : WState) : WState :=
  ⟨S.cols.map fun c => (relab σ c.1, relab σ c.2), S.rows.map (relab σ)⟩

theorem relab_cases (σ : List (ℕ × ℕ)) (x : ℕ) :
    relab σ x = x ∨ ∃ pr ∈ σ, pr.1 = x ∧ relab σ x = pr.2 := by
  induction σ with
  | nil => left; simp [relab]
  | cons pr σ ih =>
    obtain ⟨k, b⟩ := pr
    by_cases hk : x = k
    · subst hk
      right
      exact ⟨(x, b), by simp, rfl, by simp [relab, List.lookup]⟩
    · have hb : (x == k) = false := by simp [hk]
      have he : relab ((k, b) :: σ) x = relab σ x := by
        simp only [relab, List.lookup, hb]
      rw [he]
      rcases ih with h | ⟨pr, hpr, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨pr, by simp [hpr], h1, h2⟩

/-- The final checks: the final states agree after renaming internal labels. -/
def FinalOK (F₁ F₂ : WState) (σ : List (ℕ × ℕ)) : Prop :=
  renameS σ F₂ = F₁ ∧ (∀ x ∈ F₂.rows, relab (σ.map Prod.swap) (relab σ x) = x) ∧
    (∀ pr ∈ σ, isConn pr.1 = false ∧ isConn pr.2 = false)

instance (F₁ F₂ : WState) (σ : List (ℕ × ℕ)) : Decidable (FinalOK F₁ F₂ σ) := by
  unfold FinalOK; infer_instance

theorem isConn_relab {σ : List (ℕ × ℕ)} (hσ : ∀ pr ∈ σ, isConn pr.1 = false ∧ isConn pr.2 = false)
    (x : ℕ) : isConn (relab σ x) = isConn x := by
  rcases relab_cases σ x with h | ⟨pr, hpr, h1, h2⟩
  · rw [h]
  · rw [h2, (hσ pr hpr).2, ← h1, (hσ pr hpr).1]

theorem relab_conn {σ : List (ℕ × ℕ)} (hσ : ∀ pr ∈ σ, isConn pr.1 = false ∧ isConn pr.2 = false)
    {x : ℕ} (hx : isConn x = true) : relab σ x = x := by
  rcases relab_cases σ x with h | ⟨pr, hpr, h1, h2⟩
  · exact h
  · have := (hσ pr hpr).1; rw [h1, hx] at this; simp at this

/-- Renaming of row labels. -/
def gSig (σ : List (ℕ × ℕ)) : BRow → BRow
  | Sum.inl x => Sum.inl (relab σ x)
  | Sum.inr q => Sum.inr q

/-- Renaming of window column labels from `W₂` to `W₁`. -/
def colMap (W₂ W₁ : List ℕ) : BCol → BCol
  | Sum.inl a => if a ∈ W₂ then Sum.inl (W₁.getD (W₂.idxOf a) 0) else Sum.inl a
  | Sum.inr q => Sum.inr q

theorem colMap_getElem {W₂ W₁ : List ℕ} (hn : W₂.Nodup) (hlen : W₂.length = W₁.length) {k : ℕ}
    (hk : k < W₂.length) : colMap W₂ W₁ (Sum.inl W₂[k]) = Sum.inl (W₁[k]'(by omega)) := by
  simp only [colMap, if_pos (List.getElem_mem hk), List.Nodup.idxOf_getElem hn,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < W₁.length by omega),
    Option.getD_some]

theorem colMap_map {W₂ W₁ : List ℕ} (hn : W₂.Nodup) (hlen : W₂.length = W₁.length) :
    (W₂.map (Sum.inl : ℕ → BCol)).map (colMap W₂ W₁) = W₁.map Sum.inl := by
  apply List.ext_getElem (by simp [hlen])
  intro k h1 h2
  simp only [List.getElem_map]
  exact colMap_getElem hn hlen (by simpa using h1)

theorem filter_isLeft (l : List BRow) :
    l.filter (fun r => r.isLeft) = (lefts l).map Sum.inl := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rcases r with x | e
    · rw [List.filter_cons_of_pos (by rfl), ih, lefts_cons_inl, List.map_cons]
    · rw [List.filter_cons_of_neg (by simp), ih, lefts_cons_inr]

theorem lefts_map_gSig (σ : List (ℕ × ℕ)) (l : List BRow) :
    lefts (l.map (gSig σ)) = (lefts l).map (relab σ) := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rcases r with x | e
    · simp only [List.map_cons, gSig, lefts_cons_inl, ih]
    · simp only [List.map_cons, gSig, lefts_cons_inr, ih]

theorem nonInt_gSig {σ : List (ℕ × ℕ)}
    (hσ : ∀ pr ∈ σ, isConn pr.1 = false ∧ isConn pr.2 = false) (r : BRow) :
    nonInt (gSig σ r) = nonInt r := by
  rcases r with x | e
  · simp only [gSig, nonInt, isConn_relab hσ]
  · rfl

theorem gSig_nonInt {σ : List (ℕ × ℕ)}
    (hσ : ∀ pr ∈ σ, isConn pr.1 = false ∧ isConn pr.2 = false) {r : BRow}
    (hr : nonInt r = true) : gSig σ r = r := by
  rcases r with x | e
  · simp only [gSig, relab_conn hσ hr]
  · rfl

/-! ### Outside markings of the initial grids are connecting or external -/

section OutsideConn

variable {m : ℕ} (S : WState) {i : Fin (m - 1)} {offs : List ℕ} {B t : PositiveAdjacentWord m}
  {flags : List Bool}

theorem isConn_add {a e : ℕ} (ha : a = 20 ∨ a = 30) (he : e ≤ 2) : isConn (a + e) = true := by
  unfold isConn
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem initGrid_O_inr_nonInt (hB : BlockHyp i offs B t (flagOf flags))
    (hS : InitOK S offs flags) {q : ℕ × Fin 3} (hq : q ∈ outsideQ (3 + t.length)) :
    nonInt ((initGrid S hB hS).O (Sum.inr q)) = true := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL := hB.len_append
  have h3 : 3 ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B ++ t).length := by simp only [kc]; omega
  rw [initGrid_O]
  simp only [fColInv]
  rw [cornerOf_eq _ _ h₁, gRow_out S hB hS _ h3]
  split_ifs with hc
  · have hc0 := corner_ne_zero_of_in _ h3 hc
    obtain ⟨-, hrank⟩ := matching_inRank (B ++ t) _ hc0
    rw [← hrank]
    generalize positiveRectilinearWordMatching (B ++ t) (⟨(kc k).1, h₁⟩, (kc k).2) = q' at hc ⊢
    have hv := hB.val q'.1.val (by rw [hB.len]; exact hc)
    have hget : (B ++ t)[q'.1.val] = B[q'.1.val]'(by rw [hB.len]; exact hc) :=
      List.getElem_append_left _
    have hle := hB.offs_le q'.1.val hc
    simp only [nonInt]
    apply isConn_add (Or.inl rfl)
    unfold inRank
    rw [hget, hv]
    split_ifs <;> omega
  · rfl

theorem initGrid_X_inr_nonInt (hB : BlockHyp i offs B t (flagOf flags))
    (hS : InitOK S offs flags) {q : ℕ × Fin 3} (hq : q ∈ outsideQ (3 + t.length)) :
    nonInt ((initGrid S hB hS).X (Sum.inr q)) = true := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL := hB.len_append
  have h3 : 3 ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B ++ t).length := by simp only [kc]; omega
  rw [initGrid_X]
  simp only [fColInv]
  rw [cornerOf_eq _ _ h₁, gRow_symm_out S hB hS _ h3]
  split_ifs with hc
  · have hMp : positiveRectilinearWordMatching (B ++ t) ((positiveRectilinearWordMatching
        (B ++ t)).symm (⟨(kc k).1, h₁⟩, (kc k).2)) = (⟨(kc k).1, h₁⟩, (kc k).2) :=
      Equiv.apply_symm_apply _ _
    generalize (positiveRectilinearWordMatching (B ++ t)).symm (⟨(kc k).1, h₁⟩, (kc k).2) = p
      at hc hMp ⊢
    have hc0 : p.2 ≠ 0 := by
      intro h0
      have := positiveRectilinearWordMatching_middle (B ++ t) p.1
      rw [← h0] at this
      simp only [Prod.mk.eta] at this
      rw [this] at hMp
      have := congrArg (fun z => z.1.val) hMp
      simp only at this
      omega
    obtain ⟨-, hrank⟩ := matching_inRank (B ++ t) p hc0
    rw [hMp] at hrank
    rw [hrank]
    have hv := hB.val p.1.val (by rw [hB.len]; exact hc)
    have hget : (B ++ t)[p.1.val] = B[p.1.val]'(by rw [hB.len]; exact hc) :=
      List.getElem_append_left _
    have hle := hB.offs_le p.1.val hc
    simp only [nonInt]
    apply isConn_add (Or.inr rfl)
    unfold outRank
    rw [hget, hv]
    split_ifs <;> omega
  · rfl

end OutsideConn

/-! ### Internal rows commute with external rows -/

theorem rowsNonint_free {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q)
    (hout : ∀ q ∈ Q, nonInt (G.O (Sum.inr q)) = true ∧ nonInt (G.X (Sum.inr q)) = true)
    {x : ℕ} (hx : isConn x = false) (e : ℕ × Fin 3) :
    G.RowsNonint (Sum.inl x) (Sum.inr e) ∧ G.RowsNonint (Sum.inr e) (Sum.inl x) := by
  have hwin : ∀ c ∈ G.cols, (G.O c = Sum.inl x ∨ G.X c = Sum.inl x) → G.cpos c < W.length := by
    intro c hc hcx
    rcases hG.mem_cols hc with ⟨t, ht, rfl⟩ | hq
    · rw [hG.cpos_w ht]; exact ht
    · exfalso
      obtain ⟨q, hqQ, rfl⟩ := List.mem_map.mp hq
      rcases hcx with h | h
      · have := (hout q hqQ).1; rw [h] at this; simp [nonInt, hx] at this
      · have := (hout q hqQ).2; rw [h] at this; simp [nonInt, hx] at this
  have hext : ∀ c ∈ G.cols, (G.O c = Sum.inr e ∨ G.X c = Sum.inr e) → W.length ≤ G.cpos c :=
    fun c hc hce => hG.cpos_q (hG.col_of_inr hc hce)
  constructor
  · intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
    have h1 := hwin a ha (Or.inl hOa)
    have h2 := hwin a' ha' (Or.inr hXa)
    have h3 := hext b hb (Or.inl hOb)
    have h4 := hext b' hb' (Or.inr hXb)
    apply nonintN_of_lt; left
    simp only [max_lt_iff, lt_min_iff]; omega
  · intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
    have h1 := hext a ha (Or.inl hOa)
    have h2 := hext a' ha' (Or.inr hXa)
    have h3 := hwin b hb (Or.inl hOb)
    have h4 := hwin b' hb' (Or.inr hXb)
    apply nonintN_of_lt; right
    simp only [max_lt_iff, lt_min_iff]; omega

/-! ### The final comparison -/

section Final

variable {m : ℕ} {i : Fin (m - 1)} {offs₁ offs₂ : List ℕ} {B₁ B₂ t : PositiveAdjacentWord m}
  {flags : List Bool}

/-- The free rows: internal window rows. -/
def freeR : BRow → Bool
  | Sum.inl x => !isConn x
  | Sum.inr _ => false

theorem not_freeR (r : BRow) : (!freeR r) = nonInt r := by
  rcases r with x | e <;> simp [freeR, nonInt]

theorem outsideQ_len {fl : ℕ → Bool} {offs : List ℕ} {B : PositiveAdjacentWord m}
    (hB : BlockHyp i offs B t fl) : outsideQ (B ++ t).length = outsideQ (3 + t.length) := by
  rw [hB.len_append]

/-- **Two window sequences give grid moves.** -/
theorem wordGrid_movesTo_of_windows (hB₁ : BlockHyp i offs₁ B₁ t (flagOf flags))
    (hB₂ : BlockHyp i offs₂ B₂ t (flagOf flags)) (ha : AgreeHyp hB₁ hB₂) (S₁ S₂ : WState)
    (hS₁ : InitOK S₁ offs₁ flags) (hS₂ : InitOK S₂ offs₂ flags) (hP : PairOK S₁ offs₁ S₂ offs₂)
    {ms₁ ms₂ : List WMove} {F₁ F₂ : WState} (hr₁ : run S₁ ms₁ = some F₁)
    (hr₂ : run S₂ ms₂ = some F₂) {σ : List (ℕ × ℕ)} (hF : FinalOK F₁ F₂ σ) :
    (wordGrid (B₁ ++ t)).MovesTo (wordGrid (B₂ ++ t)) := by
  obtain ⟨hren, hinv, hσ⟩ := hF
  set Q := outsideQ (3 + t.length) with hQ
  have hR₁ := initGrid_real S₁ hB₁ hS₁
  rw [outsideQ_len hB₁] at hR₁
  have hR₂ := initGrid_real S₂ hB₂ hS₂
  rw [outsideQ_len hB₂] at hR₂
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
  have hout₁ : ∀ q ∈ Q, H₁.O (Sum.inr q) = (initGrid S₁ hB₁ hS₁).O (Sum.inr q) ∧
      H₁.X (Sum.inr q) = (initGrid S₁ hB₁ hS₁).X (Sum.inr q) := hso₁.1
  have hout₂ : ∀ q ∈ Q, H₂.O (Sum.inr q) = (initGrid S₂ hB₂ hS₂).O (Sum.inr q) ∧
      H₂.X (Sum.inr q) = (initGrid S₂ hB₂ hS₂).X (Sum.inr q) := hso₂.1
  have hnon₁ : ∀ q ∈ Q, nonInt (H₁.O (Sum.inr q)) = true ∧ nonInt (H₁.X (Sum.inr q)) = true :=
    fun q hq => by
      rw [(hout₁ q hq).1, (hout₁ q hq).2]
      exact ⟨initGrid_O_inr_nonInt S₁ hB₁ hS₁ hq, initGrid_X_inr_nonInt S₁ hB₁ hS₁ hq⟩
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
        rw [(hout₁ q hqQ).1, (hout₂ q hqQ).1, agree_O S₁ S₂ hS₁ hS₂ ha hqQ,
          gSig_nonInt hσ (initGrid_O_inr_nonInt S₂ hB₂ hS₂ hqQ)])
    (fun c hc => by
      change H₁.X c = gSig σ (H₂.X (colMap W₁ W₂ c))
      rcases hH₁.mem_cols hc with ⟨k, hk, rfl⟩ | hq
      · rw [colMap_getElem hW₁ hlenW.symm hk, hH₁.X_w k hk, hH₂.X_w k (by omega)]
        have hk' : k < F₂.cols.length := by rw [← hH₂.len]; omega
        simp only [gSig, WState.col, hFc, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some]
      · obtain ⟨q, hqQ, rfl⟩ := List.mem_map.mp hq
        change H₁.X (Sum.inr q) = gSig σ (H₂.X (Sum.inr q))
        rw [(hout₁ q hqQ).2, (hout₂ q hqQ).2, agree_X S₁ S₂ hS₁ hS₂ ha hqQ,
          gSig_nonInt hσ (initGrid_X_inr_nonInt S₂ hB₂ hS₂ hqQ)])
    (fun a b hfa hwb => by
      rcases a with x | e
      · rcases b with y | b
        · simp at hwb
        · exact rowsNonint_free hH₁ hnon₁ (by simpa [freeR] using hfa) b
      · simp [freeR] at hfa)
    (by
      rw [List.filter_congr (fun r _ => not_freeR r), List.filter_congr (fun r _ => not_freeR r),
        hso₁.2, agree_rows S₁ S₂ hS₁ hS₂ ha hP, ← hso₂.2]
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
  exact (((initGrid_movesTo S₁ hB₁ hS₁).symm.trans hmv₁).trans hmv).trans
    (hmv₂.symm.trans (initGrid_movesTo S₂ hB₂ hS₂))

end Final

end OnLeConjecture.KnotTheory.BraidWindow
