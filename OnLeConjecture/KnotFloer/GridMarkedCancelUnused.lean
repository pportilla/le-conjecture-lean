/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelUnknot
public import OnLeConjecture.KnotTheory.MarkedCancelFwd

/-!
# Marked cancellation of an inverse pair with an unused upper strand

Let `X = σ_r σ_r⁻¹` and let `t` be a signed word in which the strand `r` occurs and the strand
`r + 1` does not. For an outside corner `p` of `X ++ t`, the marked window grid of `X ++ t` with
the marked arc leaving `p` and the triply prepared protected grid `H` is related by grid moves to
a marked word grid of `t` with the marked arc leaving the corner of `t` under `p` and the
protected grid `blockInsert H k k` (`marked_cancel_unused`).

The window sequence (`Funk`, checked by `decide` in `mfwd_cancel_unused`) reduces the two letters
to one bivalent column and a split unknot on two columns. The two rows of the split unknot pass
all other rows, the bivalent column is contracted, and the resulting grid is the marked word grid
of `t` with a split unknot added (`addUnknot`), which is absorbed into the protected grid
(`unkGrid_movesTo_marked`). This is the step of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 8) in which the strand of a cancelled inverse pair that
is not used by the rest of the word becomes a four-mark block of the frame tower.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid
  OnLeConjecture.KnotFloer.GridFull

variable {m r k : ℕ} {sg : List Bool} {X t : SignedAdjacentWord m}

/-- The final window state of the cancellation of an inverse pair whose upper strand is unused:
the bivalent column `(30, 20)` and the split unknot `(1, 5), (5, 1)`. -/
def Funk : WState := ⟨[(30, 20), (1, 5), (5, 1)], [20, 1, 30, 5]⟩

/-- The finite checks on the heights and the order of the connecting labels of the rank `r`. -/
def UnusedOK (S : WState) (sg : List Bool) : Prop :=
  lvlRelS S [0, 0] sg 20 = 0 ∧ lvlRelS S [0, 0] sg 30 = 0 ∧ S.ri 20 < S.ri 30

instance (S : WState) (sg : List Bool) : Decidable (UnusedOK S sg) := by
  unfold UnusedOK; infer_instance

theorem lefts_filter_nonInt (l : List BRow) :
    lefts (l.filter nonInt) = (lefts l).filter isConn := by
  induction l with
  | nil => rfl
  | cons z l ih =>
    rcases z with n | e
    · by_cases h : isConn n = true
      · rw [List.filter_cons_of_pos (show nonInt (Sum.inl n) = true from h), lefts_cons_inl,
          lefts_cons_inl, List.filter_cons_of_pos h, ih]
      · rw [List.filter_cons_of_neg (show ¬ nonInt (Sum.inl n) = true from h), lefts_cons_inl,
          List.filter_cons_of_neg h, ih]
    · rw [List.filter_cons_of_pos (show nonInt (Sum.inr e) = true from rfl), lefts_cons_inr,
        lefts_cons_inr, ih]

theorem split_lefts_one {l₁ l₂ : List ℕ} (h : [20, 1, 30, 5] = l₁ ++ 1 :: l₂) :
    l₁ = [20] ∧ l₂ = [30, 5] := by
  rcases l₁ with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp at h
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨by rw [← h.1], h.2.2.symm⟩
  · simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨-, -, h'⟩ := h
    have : (1 : ℕ) ∈ [30, 5] := by rw [h']; simp
    simp at this

theorem split_lefts_five {l₁ l₂ : List ℕ} (h : [30, 5] = l₁ ++ 5 :: l₂) :
    l₁ = [30] ∧ l₂ = [] := by
  rcases l₁ with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp at h
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨by rw [← h.1], h.2.2.symm⟩
  · simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨-, -, h'⟩ := h
    have : (5 : ℕ) ∈ ([] : List ℕ) := by rw [h']; simp
    simp at this

/-- **Marked cancellation of an inverse pair with an unused upper strand**, from the finite data
of a window sequence, with the marked arc leaving an outside corner. -/
theorem marked_cancel_unused (hB : BlockS 2 1 r [0, 0] sg X t (flagOf [true, false]))
    (S : WState) (hS : InitOKS 2 S [0, 0] sg [true, false]) {ms : List WMove}
    (hr : run S ms = some Funk) (hC : UnusedOK S sg) (hOl : 30 ∈ Ol S)
    (hXc : ∀ x ∈ Xl S, x ∉ Ol S → isConn x = true)
    (p' : Fin t.length × Fin 3) (H : GridDiagram (k + 1)) (hH : TriplyPrepared H) :
    ∃ M : GridDiagram (t.length * 3 + (k + 2) + 1),
      IsMarkedGrid t (Fin.pos p'.1) p' (unkH H) (unkH_tp H hH).1 (unkH_tp H hH).2.1 M ∧
      (winGrid S hB hS (upCorner hB p') H hH.1 hH.2.1).toGrid.MovesTo M := by
  have hX : H.X 0 = 0 := hH.1
  have hO : H.O (Fin.last k) = 0 := hH.2.1
  obtain ⟨hl20, hl30, hri0⟩ := hC
  have hXl : X.length = 2 := hB.len
  have hL := hB.len_append
  have ht : 0 < t.length := Fin.pos p'.1
  set p := upCorner hB p' with hpdef
  have hp2 : 2 ≤ p.1.val := by simp [hpdef, upCorner]
  have hpv : p.1.val = p'.1.val + 2 := rfl
  set Gx := sInitGrid S hB hS with hGx
  set Gm := winGrid S hB hS p H hX hO with hGm
  set P := winBlock 2 S p H hX hO with hPdef
  set α := sgRow 2 S (X ++ t) p with hα
  set D := winData S hB hS p H hX hO with hD
  set Q := outsideQK 2 (2 + t.length) with hQ
  set qH := winQ (X ++ t).length k with hqH
  have hRx : Real S Gx (List.range (3 * 2)) Q := by
    have := sInitGrid_real S hB hS; rw [soutsideQ_len hB] at this; exact this
  have hR : Real S Gm (List.range (3 * 2)) (Q ++ qH) := by
    have := real_winGrid S hB hS p H hX hO hp2; rw [soutsideQ_len hB] at this; exact this
  -- the corners of `t` inside `X ++ t`
  have hQeq : Q = (sCols t).map (fun q => (q.1.val + 2, q.2)) := outsideQK_two_eq t
  have hshQ : ∀ a : Fin t.length × Fin 3, (a.1.val + 2, a.2) ∈ Q := fun a => by
    rw [hQeq]; exact List.mem_map.mpr ⟨a, mem_sCols t a, rfl⟩
  have hmemQ : ∀ q ∈ Q, (Sum.inr q : BCol) ∈ Gx.cols := fun q hq => by
    rw [hRx.cols]; exact List.mem_append_right _ (List.mem_map_of_mem hq)
  have hpQ : (p.1.val, p.2) ∈ Q := hshQ p'
  have hαGx : Gx.O (Sum.inr (p.1.val, p.2)) = α := by
    rw [← sfCol_out p hp2]; exact sInitGrid_O_corner S hB hS p
  -- the label of the marked arc
  have hαcases := sgRow_cases_out S hB hS p hp2
  have hαnon : nonInt α = true := by
    rcases hαcases with h | ⟨x, h, hx1, hx2⟩
    · rw [← hα] at h; rw [h]; rfl
    · rw [← hα] at h; rw [h]; exact hXc x hx1 hx2
  have hα30 : α ≠ Sum.inl 30 := by
    rcases hαcases with h | ⟨x, h, hx1, hx2⟩
    · rw [← hα] at h; rw [h]; simp
    · rw [← hα] at h; rw [h]; intro e; simp only [Sum.inl.injEq] at e; subst e; exact hx2 hOl
  -- the markings of the marked window grid
  have hGmO : ∀ q ∈ Q, Gm.O (Sum.inr q) =
      if q = (p.1.val, p.2) then P.hr 0 else Gx.O (Sum.inr q) := by
    intro q hq
    rw [hGm, winGrid, insertBlock_O, D.blockO_old (hmemQ q hq)]
    by_cases he : q = (p.1.val, p.2)
    · rw [if_pos (by rw [he, hαGx]), if_pos he]
    · rw [if_neg (fun e => he (by
          have := Gx.O_inj _ (hmemQ q hq) _ (hmemQ _ hpQ) (e.trans hαGx.symm)
          simpa using this)), if_neg he]
  have hGmX : ∀ q ∈ Q, Gm.X (Sum.inr q) = Gx.X (Sum.inr q) := by
    intro q hq
    rw [hGm, winGrid, insertBlock_X, D.blockX_old (hmemQ q hq)]
    split_ifs with he
    · rw [winBlock_hr_last]; exact he.symm
    · rfl
  have hGmOB : ∀ j, Gm.O (P.hc j) = P.oRow j := fun j => by
    rw [hGm, winGrid, insertBlock_O, blockO_hc]
  have hGmXB : ∀ j, Gm.X (P.hc j) = P.xRow j := fun j => by
    rw [hGm, winGrid, insertBlock_X, blockX_hc]
  have hP0 : P.hr 0 = Sum.inr ((X ++ t).length + 0, 1) :=
    winBlock_hr_of_ne S p H hX hO (by simp [Fin.ext_iff])
  have hPfresh : ∀ j, j ≠ Fin.last (k + 1) → ∀ c ∈ Gx.cols, P.hr j ≠ Gx.O c := by
    intro j hj c hc e
    rw [winBlock_hr_of_ne S p H hX hO hj] at e
    have hmem := Gx.O_mem c hc
    rw [← e] at hmem
    obtain ⟨q, hq⟩ := (mem_sInitGrid_rows S hB hS _).mp hmem
    exact sgRow_ne_new S q _ _ hq
  have hxRow_ne : ∀ j, P.xRow j ≠ P.hr (Fin.last (k + 1)) := P.xRow_ne_output
  have hqHcol : ∀ q ∈ qH, ∃ j, (Sum.inr q : BCol) = P.hc j := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨j, rfl⟩
  -- the window sequence
  obtain ⟨n, W, Hm, hH', hso, hmv⟩ := run_sound hR hr
  have hWl : W.length = 3 := by rw [hH'.len]; rfl
  obtain ⟨w₀, w₁, w₂, rfl⟩ : ∃ w₀ w₁ w₂, W = [w₀, w₁, w₂] := by
    match W, hWl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have hO₀ : Hm.O (Sum.inl w₀) = Sum.inl 30 := hH'.O_w 0 (by simp)
  have hX₀ : Hm.X (Sum.inl w₀) = Sum.inl 20 := hH'.X_w 0 (by simp)
  have hO₁ : Hm.O (Sum.inl w₁) = Sum.inl 1 := hH'.O_w 1 (by simp)
  have hX₁ : Hm.X (Sum.inl w₁) = Sum.inl 5 := hH'.X_w 1 (by simp)
  have hO₂ : Hm.O (Sum.inl w₂) = Sum.inl 5 := hH'.O_w 2 (by simp)
  have hX₂ : Hm.X (Sum.inl w₂) = Sum.inl 1 := hH'.X_w 2 (by simp)
  have hlefts : lefts Hm.rows = [20, 1, 30, 5] := hH'.rows
  have hmemL : ∀ y, Sum.inl y ∈ Hm.rows ↔ y = 20 ∨ y = 1 ∨ y = 30 ∨ y = 5 := by
    intro y; rw [← mem_lefts, hlefts]; simp
  have hcolsHm : Hm.cols = Sum.inl w₀ :: Sum.inl w₁ :: Sum.inl w₂ :: (Q ++ qH).map Sum.inr := by
    rw [hH'.cols]; simp
  have hcnd := Hm.cols_nodup
  rw [hcolsHm] at hcnd
  have hw01 : (Sum.inl w₀ : BCol) ≠ Sum.inl w₁ := fun e => by
    rw [e] at hcnd; simp at hcnd
  have hw02 : (Sum.inl w₀ : BCol) ≠ Sum.inl w₂ := fun e => by
    rw [e] at hcnd; simp at hcnd
  have hw12 : (Sum.inl w₁ : BCol) ≠ Sum.inl w₂ := fun e => by
    rw [e] at hcnd; simp at hcnd
  have hw12' : w₁ ≠ w₂ := fun e => hw12 (by rw [e])
  have hcp1 : Hm.cpos (Sum.inl w₁) = 1 :=
    cpos_of_cols_append Hm (l := [Sum.inl w₀]) (by rw [hcolsHm]; rfl) (by simpa using hw01.symm)
  have hcp2 : Hm.cpos (Sum.inl w₂) = 2 :=
    cpos_of_cols_append Hm (l := [Sum.inl w₀, Sum.inl w₁]) (by rw [hcolsHm]; rfl)
      (by simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
          exact ⟨hw02.symm, hw12.symm⟩)
  have hw1m : (Sum.inl w₁ : BCol) ∈ Hm.cols := by rw [hcolsHm]; simp
  have hw2m : (Sum.inl w₂ : BCol) ∈ Hm.cols := by rw [hcolsHm]; simp
  -- the row of label `1` moves to the bottom
  obtain ⟨A₁, B₁, hAB₁⟩ := List.append_of_mem ((hmemL 1).mpr (by simp))
  have hl₁ := hlefts
  rw [hAB₁, lefts_append, lefts_cons_inl] at hl₁
  obtain ⟨hlA₁, hlB₁⟩ := split_lefts_one hl₁.symm
  have hA₁1 : Sum.inl 1 ∉ A₁ := fun h => by
    have := mem_lefts.mpr h; rw [hlA₁] at this; simp at this
  have hA₁5 : Sum.inl 5 ∉ A₁ := fun h => by
    have := mem_lefts.mpr h; rw [hlA₁] at this; simp at this
  obtain ⟨Hm₁, hc₁', hr₁', hO₁', hX₁', hm₁'⟩ := Hm.exists_moveRowDown (m₁ := []) (mid := A₁)
    (x := Sum.inl 1) (m₂ := B₁) (by rw [hAB₁]; simp) (fun z hz => (Hm.rowsNonint_comm).mpr
      (Hm.rowsNonint_of_short hw1m hw2m hO₁ hX₂ (Or.inl (by rw [hcp1, hcp2]))
        (fun e => hA₁1 (e ▸ hz)) (by rw [hO₂]; exact fun e => hA₁5 (e ▸ hz))
        (by rw [hX₁]; exact fun e => hA₁5 (e ▸ hz))))
  -- the row of label `5` moves next to it
  obtain ⟨A₂, B₂, hAB₂⟩ := List.append_of_mem (show Sum.inl 5 ∈ B₁ from
    mem_lefts.mp (by rw [hlB₁]; simp))
  have hl₂ := hlB₁
  rw [hAB₂, lefts_append, lefts_cons_inl] at hl₂
  obtain ⟨hlA₂, hlB₂⟩ := split_lefts_five hl₂.symm
  have hA₂1 : Sum.inl 1 ∉ A₂ := fun h => by
    have := mem_lefts.mpr h; rw [hlA₂] at this; simp at this
  have hA₂5 : Sum.inl 5 ∉ A₂ := fun h => by
    have := mem_lefts.mpr h; rw [hlA₂] at this; simp at this
  have hB₂1 : ∀ y, Sum.inl y ∉ B₂ := fun y h => by
    have := mem_lefts.mpr h; rw [hlB₂] at this; simp at this
  have hcpos₁ : ∀ c, Hm₁.cpos c = Hm.cpos c := fun c => by simp only [LabeledGrid.cpos, hc₁']
  obtain ⟨Hm₂, hc₂', hr₂', hO₂', hX₂', hm₂'⟩ := Hm₁.exists_moveRowDown (m₁ := [Sum.inl 1])
    (mid := A₁ ++ A₂) (x := Sum.inl 5) (m₂ := B₂) (by rw [hr₁', hAB₂]; simp) (fun z hz => by
      have hz1 : z ≠ Sum.inl 1 := fun e => by
        rw [e, List.mem_append] at hz; rcases hz with h | h; exacts [hA₁1 h, hA₂1 h]
      have hz5 : z ≠ Sum.inl 5 := fun e => by
        rw [e, List.mem_append] at hz; rcases hz with h | h; exacts [hA₁5 h, hA₂5 h]
      refine (Hm₁.rowsNonint_comm).mpr (Hm₁.rowsNonint_of_short (by rw [hc₁']; exact hw2m)
        (by rw [hc₁']; exact hw1m) (by rw [hO₁']; exact hO₂) (by rw [hX₁']; exact hX₁)
        (Or.inr (by rw [hcpos₁, hcpos₁, hcp1, hcp2])) hz5 ?_ ?_)
      · rw [hO₁', hO₁]; exact hz1
      · rw [hX₁', hX₂]; exact hz1)
  have hOeq : Hm₂.O = Hm.O := hO₂'.trans hO₁'
  have hXeq : Hm₂.X = Hm.X := hX₂'.trans hX₁'
  have hceq : Hm₂.cols = Hm.cols := hc₂'.trans hc₁'
  -- the other rows are the connecting and outside rows
  have hnonOf : ∀ z ∈ Hm.rows, z ≠ Sum.inl 1 → z ≠ Sum.inl 5 → nonInt z = true := by
    intro z hz h1 h5
    rcases z with y | a
    · rcases (hmemL y).mp hz with rfl | rfl | rfl | rfl
      · rfl
      · exact absurd rfl h1
      · rfl
      · exact absurd rfl h5
    · rfl
  set R' := A₁ ++ A₂ ++ B₂ with hR'def
  have hR'filter : R' = Hm.rows.filter nonInt := by
    have hA₁n : ∀ z ∈ A₁, nonInt z = true := fun z hz =>
      hnonOf z (by rw [hAB₁]; simp [hz]) (fun e => hA₁1 (e ▸ hz)) (fun e => hA₁5 (e ▸ hz))
    have hA₂n : ∀ z ∈ A₂, nonInt z = true := fun z hz =>
      hnonOf z (by rw [hAB₁, hAB₂]; simp [hz]) (fun e => hA₂1 (e ▸ hz)) (fun e => hA₂5 (e ▸ hz))
    have hB₂n : ∀ z ∈ B₂, nonInt z = true := fun z hz =>
      hnonOf z (by rw [hAB₁, hAB₂]; simp [hz]) (fun e => hB₂1 1 (e ▸ hz))
        (fun e => hB₂1 5 (e ▸ hz))
    rw [hAB₁, hAB₂, List.filter_append, List.filter_cons_of_neg (by decide),
      List.filter_append, List.filter_cons_of_neg (by decide), List.filter_eq_self.mpr hA₁n,
      List.filter_eq_self.mpr hA₂n, List.filter_eq_self.mpr hB₂n, hR'def, List.append_assoc]
  have hR'rows : Hm₂.rows = Sum.inl 1 :: Sum.inl 5 :: R' := by
    rw [hr₂', hR'def]; simp
  have hlR' : lefts R' = [20, 30] := by
    rw [hR'def, lefts_append, lefts_append, hlA₁, hlA₂, hlB₂]; rfl
  have hHrows : R' = Gm.rows.filter nonInt := hR'filter.trans hso.2
  have hPnon : ∀ z ∈ P.rows, nonInt z = true := by
    intro z hz
    obtain ⟨j, rfl⟩ := P.mem_rows.mp hz
    by_cases hj : j = Fin.last (k + 1)
    · rw [hj, winBlock_hr_last]; exact hαnon
    · rw [winBlock_hr_of_ne S p H hX hO hj]; rfl
  have hProws : P.rows = List.ofFn (fun j : Fin (k + 1) => P.hr j.castSucc) ++ [α] := by
    change List.ofFn P.hr = _; rw [ofFn_succ_last, winBlock_hr_last]
  -- the rows, with the block rows replacing the marked arc
  have hGxrows : Gx.rows = D.m₁ ++ α :: D.m₂ := D.rows_eq
  have hGmrows : Gm.rows = D.m₁ ++ P.rows ++ D.m₂ := rfl
  have hHmrows : R' = D.m₁.filter nonInt ++ P.rows ++ D.m₂.filter nonInt := by
    rw [hHrows, hGmrows, filter_replace nonInt hPnon]
  set U₀ := Gx.rows.filter nonInt with hU₀
  have hU₀eq : U₀ = D.m₁.filter nonInt ++ α :: D.m₂.filter nonInt := by
    rw [hU₀, hGxrows, List.filter_append, List.filter_cons_of_pos hαnon]
  have hU₀nd : U₀.Nodup := Gx.rows_nodup.filter _
  have hlP : lefts P.rows = lefts [α] := lefts_winBlock_rows S p H hX hO
  have hlefts₀ : lefts U₀ = [20, 30] := by
    rw [← hlR', hHmrows, hU₀eq, show D.m₁.filter nonInt ++ α :: D.m₂.filter nonInt =
        D.m₁.filter nonInt ++ [α] ++ D.m₂.filter nonInt by simp]
    simp only [lefts_append, hlP]
  have hmemL₀ : ∀ y, Sum.inl y ∈ U₀ ↔ y = 20 ∨ y = 30 := by
    intro y; rw [← mem_lefts, hlefts₀]; simp
  set N := BIG (2 + t.length) with hN
  have hN16 : 16 ≤ N := by simp only [hN, BIG]; omega
  have hri : ∀ x, S.ri x < 16 := fun x => by
    have := List.idxOf_le_length (a := x) (l := S.rows); have := hS.2.2.2.2.1
    simp only [WState.ri]; omega
  set sK := sKf S [0, 0] sg r 2 t N with hsK
  have hsortGx : Gx.rows.Pairwise (fun a b => sK a < sK b) := srows_pairwise_Kf S hB hS
  have hsort₀ : U₀.Pairwise (fun a b => sK a < sK b) := hsortGx.filter _
  have hinr : ∀ a, Sum.inr a ∈ U₀ → 16 + cidx a.1 a.2 < N := by
    intro a ha
    rw [hU₀, List.mem_filter] at ha
    obtain ⟨h, -, -⟩ := (smem_rows_inr S hB hS a).mp ha.1
    have := a.2.isLt
    simp only [hN, BIG, cidx]
    omega
  -- no row has a key strictly between the two connecting labels
  have hnone : ∀ x ∈ U₀, ¬ (sK (Sum.inl 20) < sK x ∧ sK x < sK (Sum.inl 30)) := by
    intro x hxH
    rcases x with y' | a
    · simp only [hsK, sKf]
      have hy' := (hmemL₀ y').mp hxH
      rw [key_lt_iff (hri _ |>.trans_le hN16) (hri _ |>.trans_le hN16),
        key_lt_iff (hri _ |>.trans_le hN16) (hri _ |>.trans_le hN16)]
      rcases hy' with rfl | rfl <;> simp only [hl20, hl30] <;> omega
    · simp only [hsK, sKf]
      have hb := hinr a hxH
      rw [key_lt_iff (hri _ |>.trans_le hN16) hb, key_lt_iff hb (hri _ |>.trans_le hN16)]
      have h1 := hri 20
      have h2 := hri 30
      simp only [hl20, hl30]; omega
  have hk20 : sK (Sum.inl 20) < sK (Sum.inl 30) := by simp only [hsK, sKf, hl20, hl30]; omega
  -- the outside columns carrying the connecting labels
  have hout : ∀ c ∈ Hm.cols, c ≠ Sum.inl w₀ → c ≠ Sum.inl w₁ → c ≠ Sum.inl w₂ →
      ∃ q ∈ Q ++ qH, c = Sum.inr q := by
    intro c hc h0 h1 h2
    rw [hcolsHm] at hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | hc
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hc; exact ⟨q, hq', rfl⟩
  have hHmX : ∀ q ∈ Q, Hm.X (Sum.inr q) = Gx.X (Sum.inr q) := fun q hq => by
    rw [(hso.1 q (List.mem_append_left _ hq)).2, hGmX q hq]
  have hHmO : ∀ q ∈ Q, Hm.O (Sum.inr q) =
      if q = (p.1.val, p.2) then P.hr 0 else Gx.O (Sum.inr q) := fun q hq => by
    rw [(hso.1 q (List.mem_append_left _ hq)).1, hGmO q hq]
  have hHmB : ∀ j, Hm.O (P.hc j) = P.oRow j ∧ Hm.X (P.hc j) = P.xRow j := by
    intro j
    have hj : ((X ++ t).length + j.val, (0 : Fin 3)) ∈ Q ++ qH :=
      List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact ⟨(hso.1 _ hj).1.trans (hGmOB j), (hso.1 _ hj).2.trans (hGmXB j)⟩
  have hHmO_inl : ∀ q ∈ Q, ∀ y : ℕ, Hm.O (Sum.inr q) = Sum.inl y →
      Gx.O (Sum.inr q) = Sum.inl y := by
    intro q hq y h
    rw [hHmO q hq] at h
    split_ifs at h with he
    · rw [hP0] at h; simp at h
    · exact h
  obtain ⟨qN, hqN, hXN⟩ : ∃ q ∈ Q, Hm.X (Sum.inr q) = Sum.inl 30 := by
    have hm : Sum.inl 30 ∈ Hm.rows := (hmemL _).mpr (by omega)
    obtain ⟨c, hc, hXc⟩ := Hm.exists_X_eq hm
    obtain ⟨q, hq, rfl⟩ := hout c hc (fun e => by rw [e, hX₀] at hXc; simp at hXc)
      (fun e => by rw [e, hX₁] at hXc; simp at hXc) (fun e => by rw [e, hX₂] at hXc; simp at hXc)
    rcases List.mem_append.mp hq with hq | hq
    · exact ⟨q, hq, hXc⟩
    · exfalso
      obtain ⟨j, hj⟩ := hqHcol q hq
      rw [hj, (hHmB j).2] at hXc
      unfold ProtBlock.xRow at hXc
      rw [winBlock_hr_of_ne S p H hX hO (Fin.castSucc_ne_last _)] at hXc
      simp at hXc
  have hcolQ : ∀ q ∈ Q ++ qH, Sum.inr q ∈ Hm.cols := fun q hq => by
    rw [hH'.cols]; exact List.mem_append_right _ (List.mem_map_of_mem hq)
  -- the order of the ends of the connecting arcs
  have horder : ∀ {qn qp : ℕ × Fin 3} {e' : ℕ}, qn ∈ Q → qp ∈ Q →
      Hm.X (Sum.inr qn) = Sum.inl (30 + e') → Hm.O (Sum.inr qp) = Sum.inl (20 + e') →
      cidx qn.1 qn.2 < cidx qp.1 qp.2 := by
    intro qn qp e' hqn hqp hx ho
    rw [hHmX qn hqn] at hx
    have ho' := hHmO_inl qp hqp _ ho
    obtain ⟨h1, hb1, hx1⟩ := X_label_inv S hB hS hqn hx
    obtain ⟨h2, hK2, hb2, ho2⟩ := O_label_inv S hB hS hqp ho'
    obtain ⟨hK1, -, -⟩ := mem_outsideQK hqn
    have := order_NP hB (qN := (⟨qn.1, h1⟩, qn.2)) (qP := (⟨qp.1, h2⟩, qp.2)) hK1 hK2 hb1 hb2
      (by rw [hx1, ho2])
    simp only [finProdFinEquiv_val3] at this
    simp only [cidx]; omega
  -- injectivity on the columns
  have hOinj : ∀ q q' : ℕ × Fin 3, q ∈ Q ++ qH → q' ∈ Q ++ qH →
      Hm.O (Sum.inr q) = Hm.O (Sum.inr q') → q = q' := fun q q' hq hq' h => by
    have := Hm.O_inj _ (hcolQ q hq) _ (hcolQ q' hq') h; simpa using this
  have hXinj : ∀ q q' : ℕ × Fin 3, q ∈ Q ++ qH → q' ∈ Q ++ qH →
      Hm.X (Sum.inr q) = Hm.X (Sum.inr q') → q = q' := fun q q' hq hq' h => by
    have := Hm.X_inj _ (hcolQ q hq) _ (hcolQ q' hq') h; simpa using this
  have hQ_mem : ∀ q ∈ Q, q ∈ Q ++ qH := fun q hq => List.mem_append_left _ hq
  -- the columns of `Q` carrying an incoming connecting label lie after `qN`
  have hOgt : ∀ {q : ℕ × Fin 3} {qn : ℕ × Fin 3} {e' : ℕ}, q ∈ Q → qn ∈ Q →
      Hm.X (Sum.inr qn) = Sum.inl (30 + e') → Hm.O (Sum.inr q) = Sum.inl (20 + e') →
      cidx qn.1 qn.2 < cidx q.1 q.2 := fun hq hqn hx ho => horder hqn hq hx ho
  -- the consecutive rows `20, 30`
  obtain ⟨n₁r, n₂r, hU₀split⟩ := consecutive_of_key hsort₀ ((hmemL₀ 20).mpr (by simp))
    ((hmemL₀ 30).mpr (by simp)) hk20 hnone
  obtain ⟨n₁', n₂', hrows1⟩ : ∃ n₁' n₂', R' = n₁' ++ Sum.inl 20 :: Sum.inl 30 :: n₂' := by
    rw [hHmrows]
    exact consec_replace (hU₀eq ▸ hU₀nd) (hU₀eq ▸ hU₀split) hα30 hProws
  have hrowsHm₂ :
      Hm₂.rows = (Sum.inl 1 :: Sum.inl 5 :: n₁') ++ Sum.inl 20 :: Sum.inl 30 :: n₂' := by
    rw [hR'rows, hrows1]; simp
  -- the contraction
  obtain ⟨Q₁, Q₂, hQs, hQ₁, hQ₂⟩ := outsideQK_split 2 (2 + t.length) hqN
  have hQs' : Q = Q₁ ++ qN :: Q₂ := hQs
  obtain ⟨n₁, rfl⟩ : ∃ n₁, n = n₁ + 1 := ⟨n - 1, by
    have := Hm.cols_length; rw [hH'.cols] at this; simp at this; omega⟩
  have hcols1 : Hm₂.cols = Sum.inl w₀ ::
      ((Sum.inl w₁ :: Sum.inl w₂ :: Q₁.map Sum.inr) ++ Sum.inr qN :: (Q₂ ++ qH).map Sum.inr) := by
    rw [hceq, hH'.cols, hQs']; simp
  obtain ⟨H₁, hc₁, hr₁, hOH₁, hXH₁, hm₁⟩ := Hm₂.exists_contract hcols1 (by rw [hOeq]; exact hO₀)
    (by rw [hXeq]; exact hX₀) (by rw [hXeq]; exact hXN)
    (fun h => by
      rw [hOeq] at h
      have := hOgt hqN hqN (e' := 0) (by simpa using hXN) (by simpa using h)
      omega)
    (Or.inr hrowsHm₂) (by
      intro d' hd'
      rw [hOeq, hXeq]
      simp only [List.mem_cons] at hd'
      rcases hd' with rfl | rfl | hd'
      · rw [hO₁, hX₁]; simp
      · rw [hO₂, hX₂]; simp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd'
        have hqQ : q ∈ Q := by rw [hQs']; simp [hq]
        have hc := hQ₁ q hq
        constructor
        · intro h
          have := hOgt hqQ hqN (e' := 0) (by simpa using hXN) (by simpa using h)
          omega
        · intro h
          have := hXinj q qN (hQ_mem q hqQ) (hQ_mem qN hqN) (h.trans hXN.symm)
          subst this; omega)
  have hr₁'' : H₁.rows = Hm₂.rows.filter (fun z => z ≠ Sum.inl 30) := by
    rw [hr₁]; exact filter_ne_of_consec Hm₂.rows_nodup hrowsHm₂
  -- the final grid
  have hP30 : ∀ z ∈ P.rows, (fun z : BRow => decide (z ≠ Sum.inl 30)) z = true := by
    intro z hz
    obtain ⟨j, rfl⟩ := P.mem_rows.mp hz
    by_cases hj : j = Fin.last (k + 1)
    · rw [hj, winBlock_hr_last]; simpa using hα30
    · rw [winBlock_hr_of_ne S p H hX hO hj]; simp
  set A₁' := (D.m₁.filter nonInt).filter (fun z => z ≠ Sum.inl 30) with hA₁'
  set B₁' := (D.m₂.filter nonInt).filter (fun z => z ≠ Sum.inl 30) with hB₁'
  have hH₁rows : H₁.rows = Sum.inl 1 :: Sum.inl 5 :: (A₁' ++ P.rows ++ B₁') := by
    rw [hr₁'', hR'rows, List.filter_cons_of_pos (by decide), List.filter_cons_of_pos (by decide),
      hHmrows, filter_replace _ hP30]
  have hcolsF : H₁.cols = Sum.inl w₁ :: Sum.inl w₂ :: (Q ++ qH).map Sum.inr := by
    rw [hc₁, hQs']; simp
  have hn : n₁ = t.length * 3 + k + 1 + 2 := by
    have := H₁.cols_length
    rw [hcolsF, List.length_cons, List.length_cons, List.length_map, List.length_append, hQ,
      outsideQK_length] at this
    simp only [hqH, winQ, List.length_ofFn] at this
    omega
  subst hn
  set U₁ := U₀.filter (fun z => z ≠ Sum.inl 30) with hU₁
  have hU₁eq : U₁ = A₁' ++ α :: B₁' := by
    rw [hU₁, hU₀eq, List.filter_append, List.filter_cons_of_pos (by simpa using hα30)]
  have hU₁nd : U₁.Nodup := hU₀nd.filter _
  have hsort₁ : U₁.Pairwise (fun a b => sK a < sK b) := hsort₀.filter _
  have hOF : ∀ c, H₁.O c = Hm.O c := fun c => by rw [hOH₁, hOeq]
  have hXF : ∀ c, H₁.X c = Function.update Hm.X (Sum.inr qN) (Sum.inl 20) c := fun c => by
    rw [hXH₁, hXeq]
  have hXFB : ∀ j, H₁.X (P.hc j) = P.xRow j := by
    intro j
    rw [hXF, Function.update_of_ne, (hHmB j).2]
    intro e
    have : (P.hc j) ∈ qH.map Sum.inr := by
      rw [← winBlock_cols S p H hX hO]; exact P.hc_mem j
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp this
    rw [e] at hqe
    simp only [Sum.inr.injEq] at hqe
    subst hqe
    obtain ⟨j', hj'⟩ := List.mem_ofFn.mp hq
    have := mem_outsideQK hqN
    rw [← hj'] at this
    simp only at this
    rw [hL] at this; omega
  -- the corners of `t` inside `X ++ t`
  have hcorner : ∀ a : Fin t.length × Fin 3, ∃ ha : a.1.val + 2 < (X ++ t).length,
      Gx.O (Sum.inr (a.1.val + 2, a.2)) = sgRow 2 S (X ++ t) (⟨a.1.val + 2, ha⟩, a.2) ∧
      Gx.X (Sum.inr (a.1.val + 2, a.2)) =
        sgRow 2 S (X ++ t) ((sM (X ++ t)).symm (⟨a.1.val + 2, ha⟩, a.2)) := by
    intro a
    obtain ⟨ha, -, hO', hX'⟩ := sInitGrid_inr S hB hS (hshQ a)
    exact ⟨ha, hO', hX'⟩
  have hoH : ∀ (a : Fin t.length × Fin 3) (ha : a.1.val + 2 < (X ++ t).length),
      (X ++ t).oHeight2 (⟨a.1.val + 2, ha⟩, a.2) = t.oHeight2 a := by
    intro a ha
    simp only [SignedAdjacentWord.oHeight2, getElem_shift X t hXl a.1.isLt]
  have hxH : ∀ (a : Fin t.length × Fin 3) (ha : a.1.val + 2 < (X ++ t).length),
      (X ++ t).xHeight2 (⟨a.1.val + 2, ha⟩, a.2) = t.xHeight2 a := by
    intro a ha
    simp only [SignedAdjacentWord.xHeight2, getElem_shift X t hXl a.1.isLt]
  have hBIG : BIG (X ++ t).length = N := by rw [hN, hL]
  -- the `X` markings of the final grid
  have hXfin : ∀ q : Fin t.length × Fin 3, H₁.X (Sum.inr (q.1.val + 2, q.2)) =
      Gx.O (Sum.inr (((sM t).symm q).1.val + 2, ((sM t).symm q).2)) := by
    intro q
    set p := (sM t).symm q with hpdef
    have hMp : sM t p = q := by rw [hpdef]; exact Equiv.apply_symm_apply _ _
    rw [hXF]
    obtain ⟨hp, hOp, -⟩ := hcorner p
    obtain ⟨hq, -, hXq⟩ := hcorner q
    have hcq : (⟨q.1.val + 2, hq⟩, q.2) = ((⟨(sM t (⟨p.1.val, p.1.isLt⟩, p.2)).1.val + 2, by
        have := (sM t (⟨p.1.val, p.1.isLt⟩, p.2)).1.isLt; omega⟩,
        (sM t (⟨p.1.val, p.1.isLt⟩, p.2)).2) : Fin (X ++ t).length × Fin 3) := by
      simp only [Fin.eta, Prod.mk.eta, hMp]
    rcases sM_shift X t hXl p.1.isLt p.2 with ⟨hK, he1, he2⟩ | ⟨hb1, hb2⟩
    · -- the arc stays outside the block
      have hsMx : sM (X ++ t) (⟨p.1.val + 2, hp⟩, p.2) = (⟨q.1.val + 2, hq⟩, q.2) := by
        simp only [Fin.eta, Prod.mk.eta, hMp] at he1 he2
        exact Prod.ext (Fin.ext he1) he2
      have hO' : sgRow 2 S (X ++ t) (⟨p.1.val + 2, hp⟩, p.2) = Sum.inr (p.1.val + 2, p.2) := by
        rw [sgRow_out S hB hS _ (by simp), if_neg (by rw [hsMx]; simp)]
      have hX' : Hm.X (Sum.inr (q.1.val + 2, q.2)) = Sum.inr (p.1.val + 2, p.2) := by
        rw [hHmX _ (hshQ q), hXq, ← hsMx, Equiv.symm_apply_apply, hO']
      have hne1 : (Sum.inr (q.1.val + 2, q.2) : BCol) ≠ Sum.inr qN := by
        intro h; rw [h, hXN] at hX'; simp at hX'
      rw [Function.update_of_ne hne1, hX', hOp, hO']
    · -- the arc wraps around the block
      have hb1' : (sM (X ++ t) (⟨p.1.val + 2, hp⟩, p.2)).1.val < 2 := hb1
      have hb2' : ((sM (X ++ t)).symm (⟨q.1.val + 2, hq⟩, q.2)).1.val < 2 := by
        rw [hcq]; exact hb2
      have hO' := sgRow_out S hB hS (⟨p.1.val + 2, hp⟩, p.2) (by simp)
      rw [if_pos hb1'] at hO'
      have hX'' := sgRow_symm_out S hB hS (⟨q.1.val + 2, hq⟩, q.2) (by simp)
      rw [if_pos hb2'] at hX''
      have hheq : (X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) =
          (X ++ t).xHeight2 (⟨q.1.val + 2, hq⟩, q.2) := by
        rw [hoH, hxH, ← hMp, sM_height]
      have hX' : Hm.X (Sum.inr (q.1.val + 2, q.2)) =
          Sum.inl (30 + ((X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r)) := by
        rw [hHmX _ (hshQ q), hXq, hX'', hheq]
      have hmem : Sum.inl (30 + ((X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r)) ∈
          Hm.rows := by
        rw [← hX']; exact Hm.X_mem _ (hcolQ _ (hQ_mem _ (hshQ q)))
      rcases (hmemL _).mp hmem with h | h | h | h
      · omega
      · omega
      · have he : (X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r = 0 := by omega
        rw [he] at hX'
        have hqq : (q.1.val + 2, q.2) = qN :=
          hXinj _ _ (hQ_mem _ (hshQ q)) (hQ_mem _ hqN) (hX'.trans hXN.symm)
        rw [hqq, Function.update_self, hOp, hO', he]
      · omega
  -- recognition as a marked word grid of `t`
  set g' : ℕ × Fin 3 → BRow := fun q => Gx.O (Sum.inr (q.1 + 2, q.2)) with hg'
  set g : Fin t.length × Fin 3 → BRow := fun q => g' (q.1.val, q.2) with hg
  have hgp : g p' = α := hαGx
  have hg_up : ∀ q, g q = sgRow 2 S (X ++ t) (upCorner hB q) := fun q => by
    change Gx.O (Sum.inr ((upCorner hB q).1.val, (upCorner hB q).2)) = _
    rw [← sfCol_out (K := 2) (upCorner hB q) (by simp [upCorner])]
    exact sInitGrid_O_corner S hB hS _
  have hg_inj : ∀ q q', g q = g q' → q = q' := by
    intro q q' h
    have := Gx.O_inj _ (hmemQ _ (hshQ q)) _ (hmemQ _ (hshQ q')) h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at this
    exact Prod.ext (Fin.ext (by omega)) this.2
  set κ' : Fin t.length × Fin 3 → ℕ := fun q => sK (g q) with hκ'
  have hκ'_eq : ∀ q, κ' q = skappa 2 S (X ++ t) (upCorner hB q) := by
    intro q
    simp only [hκ']
    rw [hg_up, hsK, hN, sKf_sgRow S hB hS]
    unfold skappa
    rw [hL]
  have hup_inj : ∀ q q' : Fin t.length × Fin 3, upCorner hB q = upCorner hB q' → q = q' := by
    intro q q' h
    simp only [upCorner, Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext (Fin.ext (by omega)) h.2
  have hκ'_inj : ∀ q q', κ' q = κ' q' → q = q' := fun q q' h => by
    rw [hκ'_eq, hκ'_eq] at h
    exact hup_inj _ _ (skappa_inj S hB hS h)
  have hadm : ∀ a b, t.oHeight2 a < t.oHeight2 b → κ' a < κ' b := by
    intro a b h
    rw [hκ'_eq, hκ'_eq]
    apply skappa_mono S _ hS.2.2.2.2.1
    simp only [upCorner]
    rw [hoH, hoH]; exact h
  have hsortR : ((sRows t κ').map g).Pairwise (fun a b => sK a < sK b) := by
    rw [List.pairwise_map]
    have h := (sRows_sorted t κ').and (List.nodup_iff_pairwise_ne.mp (sRows_nodup t κ'))
    exact h.imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 (fun e => h2 (hκ'_inj _ _ e))
  have hgnon : ∀ q, nonInt (g q) = true := by
    intro q
    rw [hg_up]
    rcases sgRow_cases_out S hB hS (upCorner hB q) (by simp [upCorner]) with h | ⟨x, h, hx1, hx2⟩
    · rw [h]; rfl
    · rw [h]; exact hXc x hx1 hx2
  have hH₁nd := H₁.rows_nodup
  rw [hH₁rows] at hH₁nd
  have hH₁nd' := (List.nodup_cons.mp (List.nodup_cons.mp hH₁nd).2).2
  have hnotP : ∀ x, x ∈ A₁' ∨ x ∈ B₁' → x ∉ P.rows := by
    intro x hx hxP
    rcases hx with hx | hx
    · exact (List.nodup_append.mp (List.nodup_append.mp hH₁nd').1).2.2 x hx x hxP rfl
    · exact (List.nodup_append.mp hH₁nd').2.2 x (List.mem_append_right _ hxP) x hx rfl
  have hA₁'non : ∀ x ∈ A₁', nonInt x = true := fun x hx => by
    rw [hA₁', List.mem_filter, List.mem_filter] at hx; exact hx.1.2
  have hB₁'non : ∀ x ∈ B₁', nonInt x = true := fun x hx => by
    rw [hB₁', List.mem_filter, List.mem_filter] at hx; exact hx.1.2
  have hgP : ∀ q, q ≠ p' → g q ∉ P.rows := by
    intro q hq hmem
    obtain ⟨j, hj⟩ := P.mem_rows.mp hmem
    by_cases hjl : j = Fin.last (k + 1)
    · rw [hjl, winBlock_hr_last, ← hα, ← hgp] at hj
      exact hq (hg_inj _ _ hj.symm)
    · exact hPfresh j hjl _ (hmemQ _ (hshQ q)) hj
  have hshp : ∀ q : Fin t.length × Fin 3, (q.1.val + 2, q.2) = (p.1.val, p.2) → q = p' := by
    intro q h
    simp only [Prod.mk.injEq, hpv] at h
    exact Prod.ext (Fin.ext (by omega)) h.2
  have hH₁Ow : ∀ q : Fin t.length × Fin 3, q ≠ p' → H₁.O (Sum.inr (q.1.val + 2, q.2)) = g q := by
    intro q hq
    rw [hOF, hHmO _ (hshQ q), if_neg (fun e => hq (hshp q e))]
  have hU₁mem : ∀ x, x ∈ U₁ ↔ ∃ q, g q = x := by
    intro x
    rw [hU₁eq]
    simp only [List.mem_append, List.mem_cons]
    have hside : ∀ x, x ∈ A₁' ∨ x ∈ B₁' → ∃ q, g q = x := by
      intro x hx
      have hxH : x ∈ H₁.rows := by
        rw [hH₁rows]; rcases hx with hx | hx <;> simp [hx]
      have hxP := hnotP x hx
      have hxn : nonInt x = true := by rcases hx with hx | hx; exacts [hA₁'non x hx, hB₁'non x hx]
      obtain ⟨c, hc, hOc⟩ := H₁.exists_O_eq hxH
      rw [hcolsF] at hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · rw [hOF, hO₁] at hOc; rw [← hOc] at hxn; exact absurd hxn (by decide)
      · rw [hOF, hO₂] at hOc; rw [← hOc] at hxn; exact absurd hxn (by decide)
      obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hc
      rcases List.mem_append.mp hq₀ with hq₀ | hq₀
      · rw [hOF, hHmO _ hq₀] at hOc
        split_ifs at hOc
        · exact absurd (hOc ▸ P.hr_mem 0) hxP
        · rw [hQeq] at hq₀
          obtain ⟨q, -, rfl⟩ := List.mem_map.mp hq₀
          exact ⟨q, hOc⟩
      · obtain ⟨j, hj⟩ := hqHcol q₀ hq₀
        rw [hj, hOF, (hHmB j).1] at hOc
        exact absurd (hOc ▸ (by unfold ProtBlock.oRow; split_ifs <;> exact P.hr_mem _)) hxP
    constructor
    · rintro (hx | rfl | hx)
      · exact hside x (Or.inl hx)
      · exact ⟨p', hgp⟩
      · exact hside x (Or.inr hx)
    · rintro ⟨q, rfl⟩
      by_cases hq : q = p'
      · right; left; rw [hq, hgp]
      · have hxH : g q ∈ H₁.rows := by
          rw [← hH₁Ow q hq]
          exact H₁.O_mem _ (by
            rw [hcolsF]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_map_of_mem (hQ_mem _ (hshQ q)))))
        rw [hH₁rows] at hxH
        simp only [List.mem_cons, List.mem_append] at hxH
        rcases hxH with h | h | (h | h) | h
        · have := hgnon q; rw [h] at this; exact absurd this (by decide)
        · have := hgnon q; rw [h] at this; exact absurd this (by decide)
        · exact Or.inl h
        · exact absurd h (hgP q hq)
        · exact Or.inr (Or.inr h)
  have hUR : U₁ = (sRows t κ').map g :=
    eq_of_pairwise_key hsort₁ hsortR (fun x => by
      rw [hU₁mem x, List.mem_map]
      exact ⟨fun ⟨q, hq⟩ => ⟨q, mem_sRows t κ' q, hq⟩, fun ⟨q, _, hq⟩ => ⟨q, hq⟩⟩)
  -- the image of the marked word grid of `t` with a split unknot
  set L := insertBlock (plainGrid t κ' ht) (markRow t p') (markBlock t H hX hO)
    (endData t κ' ht p' H hX hO) with hLdef
  set fR := upRow t.length k g' α with hfR
  have hfRw : ∀ q : Fin t.length × Fin 3, fR (Sum.inr (q.1.val, q.2)) = g q := by
    intro q; simp only [hfR, upRow]; rw [if_pos q.1.isLt]
  have hfRb : ∀ i, fR ((markBlock t H hX hO).hr i) = P.hr i := by
    intro i
    rw [stdBlock_hr]
    simp only [hfR, upRow]
    rw [if_neg (by omega)]
    by_cases hi : i = Fin.last (k + 1)
    · subst hi
      rw [if_pos (by simp), winBlock_hr_last]
    · rw [if_neg (fun e => hi (Fin.ext (by simp only [Fin.val_last]; omega))),
        winBlock_hr_of_ne S p H hX hO hi, hL]
      congr 2; omega
  have hfCb : ∀ j, upCol ((markBlock t H hX hO).hc j) = P.hc j := by
    intro j
    rw [stdBlock_hc, winBlock_hc]
    simp only [upCol]
    rw [hL]; congr 2; omega
  have hLcols : L.cols = (sCols t).map (sfCol 0 t) ++ (markBlock t H hX hO).cols := by
    rw [hLdef, insertBlock_cols]; simp [endData, plainGrid_cols]
  have hcolL : ∀ c ∈ L.cols, (∃ q : Fin t.length × Fin 3, c = Sum.inr (q.1.val, q.2)) ∨
      ∃ j, c = (markBlock t H hX hO).hc j := by
    intro c hc
    rw [hLcols, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hc
      exact Or.inl ⟨q, sfCol_zero t q⟩
    · obtain ⟨j, rfl⟩ := (markBlock t H hX hO).mem_cols.mp hc
      exact Or.inr ⟨j, rfl⟩
  have hrowL : ∀ x ∈ L.rows, (∃ q : Fin t.length × Fin 3, q ≠ p' ∧ x = Sum.inr (q.1.val, q.2)) ∨
      ∃ j, x = (markBlock t H hX hO).hr j := by
    intro x hx
    rw [hLdef, insertBlock_rows] at hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · have hmem : x ∈ (plainGrid t κ' ht).rows := by
        rw [(endData t κ' ht p' H hX hO).rows_eq]; simp [hx]
      obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hmem
      refine Or.inl ⟨q, fun e => (endData t κ' ht p' H hX hO).not_mem_m₁ ?_, rfl⟩
      subst e; exact hx
    · obtain ⟨j, rfl⟩ := (markBlock t H hX hO).mem_rows.mp hx
      exact Or.inr ⟨j, rfl⟩
    · have hmem : x ∈ (plainGrid t κ' ht).rows := by
        rw [(endData t κ' ht p' H hX hO).rows_eq]; simp [hx]
      obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hmem
      refine Or.inl ⟨q, fun e => (endData t κ' ht p' H hX hO).not_mem_m₂ ?_, rfl⟩
      subst e; exact hx
  have hfRnon : ∀ x ∈ L.rows, nonInt (fR x) = true := by
    intro x hx
    rcases hrowL x hx with ⟨q, -, rfl⟩ | ⟨j, rfl⟩
    · rw [hfRw]; exact hgnon q
    · rw [hfRb]; exact hPnon _ (P.hr_mem j)
  have hplain_map : (plainGrid t κ' ht).rows.map fR = U₁ := by
    rw [hUR, plainGrid_rows, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp, sfCol_zero]
    exact hfRw q
  have hsplitU : (endData t κ' ht p' H hX hO).m₁.map fR = A₁' ∧
      (endData t κ' ht p' H hX hO).m₂.map fR = B₁' := by
    have h1 : U₁ = (endData t κ' ht p' H hX hO).m₁.map fR ++
        α :: (endData t κ' ht p' H hX hO).m₂.map fR := by
      rw [← hplain_map, (endData t κ' ht p' H hX hO).rows_eq, List.map_append, List.map_cons]
      congr 2
      rw [← hgp]; exact hfRw p'
    exact eq_of_append_cons_eq (h1 ▸ hU₁nd) (h1.symm.trans hU₁eq)
  have hab' : (Sum.inl w₁ : BCol) ≠ Sum.inl w₂ := hw12
  have hLna : (Sum.inl w₁ : BCol) ∉ L.cols := inl_not_mem_endGrid_cols t κ' ht p' H hX hO w₁
  have hLnb : (Sum.inl w₂ : BCol) ∉ L.cols := inl_not_mem_endGrid_cols t κ' ht p' H hX hO w₂
  have hrec : H₁.toGrid = (unkGrid t κ' ht p' H hH w₁ w₂ 1 5 hw12' (by decide)).toGrid := by
    apply toGrid_eq_of_image (unkGrid t κ' ht p' H hH w₁ w₂ 1 5 hw12' (by decide)) H₁ upCol fR
    · exact fun c _ c' _ h => upCol_injective h
    · rintro x hx x' hx' h
      change x ∈ Sum.inl 1 :: Sum.inl 5 :: L.rows at hx
      change x' ∈ Sum.inl 1 :: Sum.inl 5 :: L.rows at hx'
      have key : ∀ z ∈ L.rows, ∀ y, y = 1 ∨ y = 5 → fR z ≠ Sum.inl y := by
        intro z hz y hy e
        have := hfRnon z hz
        rw [e] at this
        rcases hy with rfl | rfl <;> exact absurd this (by decide)
      simp only [List.mem_cons] at hx hx'
      rcases hx with rfl | rfl | hx <;> rcases hx' with rfl | rfl | hx'
      · rfl
      · simp [hfR, upRow] at h
      · exact absurd h.symm (key _ hx' 1 (Or.inl rfl))
      · simp [hfR, upRow] at h
      · rfl
      · exact absurd h.symm (key _ hx' 5 (Or.inr rfl))
      · exact absurd h (key _ hx 1 (Or.inl rfl))
      · exact absurd h (key _ hx 5 (Or.inr rfl))
      · rcases hrowL x hx with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ <;>
          rcases hrowL x' hx' with ⟨q', hq', rfl⟩ | ⟨j', rfl⟩
        · rw [hfRw, hfRw] at h; rw [hg_inj q q' h]
        · rw [hfRw, hfRb] at h; exact absurd (h ▸ P.hr_mem j') (hgP q hq)
        · rw [hfRw, hfRb] at h; exact absurd (h ▸ P.hr_mem j) (hgP q' hq')
        · rw [hfRb, hfRb] at h; rw [P.hr_inj h]
    · have e1 : Q.map Sum.inr = ((sCols t).map (sfCol 0 t)).map upCol := by
        rw [hQeq, List.map_map, List.map_map]
        apply List.map_congr_left
        intro q _
        simp only [Function.comp, sfCol_zero, upCol]
      have e2 : qH.map Sum.inr = (markBlock t H hX hO).cols.map upCol := by
        rw [← winBlock_cols (K := 2) S p H hX hO]
        change List.ofFn _ = (List.ofFn _).map upCol
        rw [List.map_ofFn]
        congr 1
        funext j
        exact (hfCb j).symm
      change H₁.cols = (Sum.inl w₁ :: Sum.inl w₂ :: L.cols).map upCol
      rw [hcolsF, List.map_cons, List.map_cons, hLcols, List.map_append, List.map_append, e1, e2]
      rfl
    · change H₁.rows = (Sum.inl 1 :: Sum.inl 5 :: L.rows).map fR
      have e : (markBlock t H hX hO).rows.map fR = P.rows := by
        change (List.ofFn _).map fR = List.ofFn _
        rw [List.map_ofFn]; congr 1; funext i; exact hfRb i
      rw [hH₁rows, List.map_cons, List.map_cons, hLdef, insertBlock_rows, List.map_append,
        List.map_append, hsplitU.1, hsplitU.2, e]
      rfl
    · intro c hc
      change c ∈ Sum.inl w₁ :: Sum.inl w₂ :: L.cols at hc
      change H₁.O (upCol c) = fR (unkO L (Sum.inl w₁) (Sum.inl w₂) (Sum.inl 1) (Sum.inl 5) c)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · rw [unkO_a]; simp only [upCol]; rw [hOF, hO₁]; rfl
      · rw [unkO_b L _ _ hab']; simp only [upCol]; rw [hOF, hO₂]; rfl
      rw [unkO_old L _ _ hLna hLnb hc]
      rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · change H₁.O (Sum.inr (q.1.val + 2, q.2)) = fR (blockO _ _ _ (Sum.inr (q.1.val, q.2)))
        rw [(endData t κ' ht p' H hX hO).blockO_old (by
          rw [plainGrid_cols]; exact List.mem_map.mpr ⟨q, mem_sCols t q, sfCol_zero t q⟩),
          plainGrid_O]
        by_cases hq : q = p'
        · have e1 : (Sum.inr (q.1.val, q.2) : BRow) = markRow t p' := by rw [hq]
          have e2 : ((q.1.val + 2, q.2) : ℕ × Fin 3) = (p.1.val, p.2) := by
            rw [hq]; exact Prod.ext hpv.symm rfl
          rw [if_pos e1, hfRb, hOF, hHmO _ (hshQ _), if_pos e2]
        · rw [if_neg (fun e => hq (by
              simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
              exact Prod.ext (Fin.ext e.1) e.2)), hfRw, hH₁Ow q hq]
      · rw [hfCb]
        change H₁.O (P.hc j) = fR (blockO _ _ _ ((markBlock t H hX hO).hc j))
        rw [blockO_hc, hOF, (hHmB j).1]
        unfold ProtBlock.oRow
        change (if H.O j = 0 then _ else _) = fR (if H.O j = 0 then _ else _)
        split_ifs <;> rw [hfRb]; rfl
    · intro c hc
      change c ∈ Sum.inl w₁ :: Sum.inl w₂ :: L.cols at hc
      change H₁.X (upCol c) = fR (unkX L (Sum.inl w₁) (Sum.inl w₂) (Sum.inl 1) (Sum.inl 5) c)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · rw [unkX_a]; simp only [upCol]
        rw [hXF, Function.update_of_ne (by simp), hX₁]; rfl
      · rw [unkX_b L _ _ hab']; simp only [upCol]
        rw [hXF, Function.update_of_ne (by simp), hX₂]; rfl
      rw [unkX_old L _ _ hLna hLnb hc]
      rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · change H₁.X (Sum.inr (q.1.val + 2, q.2)) = fR (blockX _ _ _ (Sum.inr (q.1.val, q.2)))
        rw [(endData t κ' ht p' H hX hO).blockX_old (by
          rw [plainGrid_cols]; exact List.mem_map.mpr ⟨q, mem_sCols t q, sfCol_zero t q⟩),
          plainGrid_X, hXfin q]
        by_cases hq : (sM t).symm q = p'
        · rw [hq, if_pos rfl, hfRb, winBlock_hr_last, ← hα, ← hgp]
        · rw [if_neg (fun e => hq (by
              simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
              exact Prod.ext (Fin.ext e.1) e.2)), hfRw]
      · rw [hfCb]
        change H₁.X (P.hc j) = fR (blockX _ _ _ ((markBlock t H hX hO).hc j))
        rw [blockX_hc, hXFB]
        exact (hfRb _).symm
  refine ⟨(markedGrid t κ' ht p' (unkH H) (unkH_tp H hH).1 (unkH_tp H hH).2.1).toGrid,
    ⟨κ', hadm, rfl⟩, ?_⟩
  have hfin := unkGrid_movesTo_marked t κ' ht p' H hH w₁ w₂ 1 5 hw12' (by decide)
  rw [← hrec] at hfin
  exact hmv.trans (hm₁'.trans (hm₂'.trans (hm₁.trans hfin)))

end OnLeConjecture.KnotTheory.MarkedCancel
