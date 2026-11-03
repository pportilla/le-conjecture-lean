/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelStep

/-!
# Marked cancellation of an inverse pair at the front of a word

Let `X` be a block of two inverse letters and `t` a signed word in which both ranks of `X`
occur. For an outside corner `p` of `X ++ t`, the marked window grid `winGrid` of `X ++ t` with
the marked arc leaving `p` is related by grid moves to a marked word grid of `t` with the marked
arc leaving the corner of `t` under `p` (`marked_cancel_front`).

The proof follows `SignedGrid.cancel_front_of_data`. The window sequence reduces the two letters to
two bivalent columns, which are contracted. The protected block stays among the outside columns,
after all of them, so it never lies between a contracted column and its partner. The rows of the
final grid are the rows of the unmarked final grid with the marked arc replaced by the block rows,
and the final grid is recognized through `toGrid_eq_of_image`. This is the case of the marked
inverse cancellation of the written proof of Statement E (`statement_E_complete_proof.tex`,
Section 8) in which the marked arc leaves a corner outside the cancelled letters.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid

variable {m r k : ℕ} {sg : List Bool} {X t : SignedAdjacentWord m}

/-- The corner of `X ++ t` over a corner of `t`, for a block `X` of two letters. -/
def upCorner {fl : ℕ → Bool} (hB : BlockS 2 1 r [0, 0] sg X t fl) (q : Fin t.length × Fin 3) :
    Fin (X ++ t).length × Fin 3 :=
  (⟨q.1.val + 2, by rw [hB.len_append]; omega⟩, q.2)

/-- The column labels of `t` lifted to the column labels of `X ++ t`. -/
def upCol : BCol → BCol
  | Sum.inl x => Sum.inl x
  | Sum.inr q => Sum.inr (q.1 + 2, q.2)

/-- The row labels of a marked word grid of `t` lifted to the row labels of the marked window
grid of `X ++ t`: corners by `g`, the output row by `α`, and the other block rows by a shift. -/
def upRow (len k : ℕ) (g : ℕ × Fin 3 → BRow) (α : BRow) : BRow → BRow
  | Sum.inl x => Sum.inl x
  | Sum.inr q => if q.1 < len then g q else if q.1 = len + (k + 1) then α
      else Sum.inr (q.1 + 2, q.2)

theorem upCol_injective : Function.Injective upCol := by
  intro c c' h
  rcases c with x | q <;> rcases c' with x' | q' <;> simp only [upCol] at h
  · simpa using h
  · simp at h
  · simp at h
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    congr 1; exact Prod.ext (by omega) h.2

/-- The label of the arc leaving an outside corner is an outside label or a window label that
is an `X` label and no `O` label. -/
theorem sgRow_cases_out {K E i : ℕ} {offs : List ℕ} {flags : List Bool} {B : SignedAdjacentWord m}
    (S : WState) (hB : BlockS K E i offs sg B t (flagOf flags)) (hS : InitOKS K S offs sg flags)
    (p : Fin (B ++ t).length × Fin 3) (hp : K ≤ p.1.val) :
    sgRow K S (B ++ t) p = Sum.inr (p.1.val, p.2) ∨
      ∃ x, sgRow K S (B ++ t) p = Sum.inl x ∧ x ∈ Xl S ∧ x ∉ Ol S := by
  have hlen := hS.1
  unfold sgRow
  rw [if_neg (by omega)]
  split_ifs with h2
  · right
    refine ⟨_, rfl, ?_, sxlabel_not_mem_ol S hB hS p hp h2⟩
    have hk : cidx (sM (B ++ t) p).1.val (sM (B ++ t) p).2 < S.cols.length := by
      rw [hlen]; exact cidx_ltK h2 _
    simp only [Xl, List.mem_map]
    exact ⟨_, List.getElem_mem hk, by rw [← col_eq_getElem S hk]⟩
  · left; rfl

/-- **Marked cancellation at the front of a word**, from the finite data of a window sequence,
with the marked arc leaving an outside corner. -/
theorem marked_cancel_front (hB : BlockS 2 1 r [0, 0] sg X t (flagOf [true, true]))
    (S : WState) (hS : InitOKS 2 S [0, 0] sg [true, true]) {ms : List WMove}
    (hr : run S ms = some Fbiv) (hC : CancelOK S sg) (hOl : 30 ∈ Ol S ∧ 31 ∈ Ol S)
    (hXc : ∀ x ∈ Xl S, x ∉ Ol S → isConn x = true)
    (p' : Fin t.length × Fin 3) (H : GridDiagram (k + 1)) (hX : H.X 0 = 0)
    (hO : H.O (Fin.last k) = 0) :
    ∃ M : GridDiagram (t.length * 3 + k + 1), IsMarkedGrid t (Fin.pos p'.1) p' H hX hO M ∧
      (winGrid S hB hS (upCorner hB p') H hX hO).toGrid.MovesTo M := by
  obtain ⟨hl20, hl30, hl21, hl31, hri0, hri1⟩ := hC
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
    · rw [← hα] at h; rw [h]; intro e; simp only [Sum.inl.injEq] at e; subst e; exact hx2 hOl.1
  have hα31 : α ≠ Sum.inl 31 := by
    rcases hαcases with h | ⟨x, h, hx1, hx2⟩
    · rw [← hα] at h; rw [h]; simp
    · rw [← hα] at h; rw [h]; intro e; simp only [Sum.inl.injEq] at e; subst e; exact hx2 hOl.2
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
  obtain ⟨n, W, Hm, hH, hso, hmv⟩ := run_sound hR hr
  have hWl : W.length = 2 := by rw [hH.len]; rfl
  obtain ⟨w₀, w₁, rfl⟩ : ∃ w₀ w₁, W = [w₀, w₁] := by
    match W, hWl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hO₀ : Hm.O (Sum.inl w₀) = Sum.inl 30 := hH.O_w 0 (by simp)
  have hX₀ : Hm.X (Sum.inl w₀) = Sum.inl 20 := hH.X_w 0 (by simp)
  have hO₁ : Hm.O (Sum.inl w₁) = Sum.inl 31 := hH.O_w 1 (by simp)
  have hX₁ : Hm.X (Sum.inl w₁) = Sum.inl 21 := hH.X_w 1 (by simp)
  have hlefts : lefts Hm.rows = [20, 30, 21, 31] := hH.rows
  have hmemL : ∀ y, Sum.inl y ∈ Hm.rows ↔ y = 20 ∨ y = 30 ∨ y = 21 ∨ y = 31 := by
    intro y; rw [← mem_lefts, hlefts]; simp
  have hnon : ∀ x ∈ Hm.rows, nonInt x = true := by
    intro x hx
    rcases x with y | a
    · rcases (hmemL y).mp hx with rfl | rfl | rfl | rfl <;> decide
    · rfl
  have hHrows : Hm.rows = Gm.rows.filter nonInt := by
    rw [← hso.2]; exact (List.filter_eq_self.mpr hnon).symm
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
  have hHmrows : Hm.rows = D.m₁.filter nonInt ++ P.rows ++ D.m₂.filter nonInt := by
    rw [hHrows, hGmrows, filter_replace nonInt hPnon]
  set U₀ := Gx.rows.filter nonInt with hU₀
  have hU₀eq : U₀ = D.m₁.filter nonInt ++ α :: D.m₂.filter nonInt := by
    rw [hU₀, hGxrows, List.filter_append, List.filter_cons_of_pos hαnon]
  have hU₀nd : U₀.Nodup := Gx.rows_nodup.filter _
  have hlP : lefts P.rows = lefts [α] := lefts_winBlock_rows S p H hX hO
  have hlefts₀ : lefts U₀ = [20, 30, 21, 31] := by
    rw [← hlefts, hHmrows, hU₀eq, show D.m₁.filter nonInt ++ α :: D.m₂.filter nonInt =
        D.m₁.filter nonInt ++ [α] ++ D.m₂.filter nonInt by simp]
    simp only [lefts_append, hlP]
  have hmemL₀ : ∀ y, Sum.inl y ∈ U₀ ↔ y = 20 ∨ y = 30 ∨ y = 21 ∨ y = 31 := by
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
  -- no row has a key strictly between two connecting labels of the same rank
  have hnone : ∀ (l : List BRow), l ⊆ U₀ → ∀ (y z : ℕ), (y = 20 ∧ z = 30 ∨ y = 21 ∧ z = 31) →
      ∀ x ∈ l, ¬ (sK (Sum.inl y) < sK x ∧ sK x < sK (Sum.inl z)) := by
    intro l hl y z hyz x hx
    have hxH := hl hx
    rcases x with y' | a
    · simp only [hsK, sKf]
      have hy' := (hmemL₀ y').mp hxH
      rw [key_lt_iff (hri _ |>.trans_le hN16) (hri _ |>.trans_le hN16),
        key_lt_iff (hri _ |>.trans_le hN16) (hri _ |>.trans_le hN16)]
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hy' with rfl | rfl | rfl | rfl <;> simp only [hl20, hl30, hl21, hl31] <;> omega
    · simp only [hsK, sKf]
      have hb := hinr a hxH
      rw [key_lt_iff (hri _ |>.trans_le hN16) hb, key_lt_iff hb (hri _ |>.trans_le hN16)]
      have h1 := hri y
      have h2 := hri z
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [hl20, hl30, hl21, hl31] <;> omega
  have hk20 : sK (Sum.inl 20) < sK (Sum.inl 30) := by simp only [hsK, sKf, hl20, hl30]; omega
  have hk21 : sK (Sum.inl 21) < sK (Sum.inl 31) := by simp only [hsK, sKf, hl21, hl31]; omega
  -- the outside columns carrying the connecting labels
  have hout : ∀ c ∈ Hm.cols, (∀ k (hk : k < 2), c ≠ Sum.inl ([w₀, w₁][k]'(by simpa using hk))) →
      ∃ q ∈ Q ++ qH, c = Sum.inr q := by
    intro c hc hne
    rcases hH.mem_cols hc with ⟨k, hk, rfl⟩ | hq
    · exact absurd rfl (hne k (by simpa using hk))
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hq; exact ⟨q, hq', rfl⟩
  have hwin : ∀ k (hk : k < 2), [w₀, w₁][k]'(by simpa using hk) = w₀ ∨
      [w₀, w₁][k]'(by simpa using hk) = w₁ := by
    intro k hk; interval_cases k <;> simp
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
  have findX : ∀ e', e' ≤ 1 → ∃ q ∈ Q, Hm.X (Sum.inr q) = Sum.inl (30 + e') := by
    intro e' he'
    have hm : Sum.inl (30 + e') ∈ Hm.rows := (hmemL _).mpr (by omega)
    obtain ⟨c, hc, hXc⟩ := Hm.exists_X_eq hm
    obtain ⟨q, hq, rfl⟩ := hout c hc (fun k hk he => by
      rcases hwin k hk with h | h <;> rw [he, h] at hXc
      · rw [hX₀] at hXc; simp at hXc; omega
      · rw [hX₁] at hXc; simp at hXc; omega)
    rcases List.mem_append.mp hq with hq | hq
    · exact ⟨q, hq, hXc⟩
    · exfalso
      obtain ⟨j, hj⟩ := hqHcol q hq
      rw [hj, (hHmB j).2] at hXc
      unfold ProtBlock.xRow at hXc
      rw [winBlock_hr_of_ne S p H hX hO (Fin.castSucc_ne_last _)] at hXc
      simp at hXc
  obtain ⟨qN, hqN, hXN⟩ := findX 0 (by norm_num)
  obtain ⟨qN', hqN', hXN'⟩ := findX 1 le_rfl
  simp only [Nat.add_zero] at hXN
  have hcolQ : ∀ q ∈ Q ++ qH, Sum.inr q ∈ Hm.cols := fun q hq => by
    rw [hH.cols]; exact List.mem_append_right _ (List.mem_map_of_mem hq)
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
  have hqNN' : qN ≠ qN' := by
    intro h; rw [h, hXN'] at hXN; simp at hXN
  -- the columns of `Q` carrying an incoming connecting label lie after `qN`
  have hOgt : ∀ {q : ℕ × Fin 3} {qn : ℕ × Fin 3} {e' : ℕ}, q ∈ Q → qn ∈ Q →
      Hm.X (Sum.inr qn) = Sum.inl (30 + e') → Hm.O (Sum.inr q) = Sum.inl (20 + e') →
      cidx qn.1 qn.2 < cidx q.1 q.2 := fun hq hqn hx ho => horder hqn hq hx ho
  -- the consecutive rows `20, 30`
  obtain ⟨n₁r, n₂r, hU₀split⟩ := consecutive_of_key hsort₀ ((hmemL₀ 20).mpr (by simp))
    ((hmemL₀ 30).mpr (by simp)) hk20 (hnone U₀ (fun _ h => h) 20 30 (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨n₁', n₂', hrows1⟩ : ∃ n₁' n₂', Hm.rows = n₁' ++ Sum.inl 20 :: Sum.inl 30 :: n₂' := by
    rw [hHmrows]
    exact consec_replace (hU₀eq ▸ hU₀nd) (hU₀eq ▸ hU₀split) hα30 hProws
  -- first contraction
  obtain ⟨Q₁, Q₂, hQs, hQ₁, hQ₂⟩ := outsideQK_split 2 (2 + t.length) hqN
  have hQs' : Q = Q₁ ++ qN :: Q₂ := hQs
  obtain ⟨n₁, rfl⟩ : ∃ n₁, n = n₁ + 1 := ⟨n - 1, by
    have := Hm.cols_length; rw [hH.cols] at this; simp at this; omega⟩
  have hcols1 : Hm.cols = Sum.inl w₀ ::
      ((Sum.inl w₁ :: Q₁.map Sum.inr) ++ Sum.inr qN :: (Q₂ ++ qH).map Sum.inr) := by
    rw [hH.cols, hQs']; simp
  obtain ⟨H₁, hc₁, hr₁, hOH₁, hXH₁, hm₁⟩ := Hm.exists_contract hcols1 hO₀ hX₀ hXN
    (fun h => by
      have := hOgt hqN hqN (e' := 0) (by simpa using hXN) (by simpa using h)
      omega)
    (Or.inr hrows1) (by
      intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · rw [hO₁, hX₁]; simp
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
  have hr₁' : H₁.rows = Hm.rows.filter (fun z => z ≠ Sum.inl 30) := by
    rw [hr₁]; exact filter_ne_of_consec Hm.rows_nodup hrows1
  -- the consecutive rows `21, 31`
  have hP30 : ∀ z ∈ P.rows, (fun z : BRow => decide (z ≠ Sum.inl 30)) z = true := by
    intro z hz
    obtain ⟨j, rfl⟩ := P.mem_rows.mp hz
    by_cases hj : j = Fin.last (k + 1)
    · rw [hj, winBlock_hr_last]; simpa using hα30
    · rw [winBlock_hr_of_ne S p H hX hO hj]; simp
  have hP31 : ∀ z ∈ P.rows, (fun z : BRow => decide (z ≠ Sum.inl 31)) z = true := by
    intro z hz
    obtain ⟨j, rfl⟩ := P.mem_rows.mp hz
    by_cases hj : j = Fin.last (k + 1)
    · rw [hj, winBlock_hr_last]; simpa using hα31
    · rw [winBlock_hr_of_ne S p H hX hO hj]; simp
  set A₁ := (D.m₁.filter nonInt).filter (fun z => z ≠ Sum.inl 30) with hA₁
  set B₁ := (D.m₂.filter nonInt).filter (fun z => z ≠ Sum.inl 30) with hB₁
  have hH₁rows : H₁.rows = A₁ ++ P.rows ++ B₁ := by
    rw [hr₁', hHmrows, filter_replace _ hP30]
  set U₁ := U₀.filter (fun z => z ≠ Sum.inl 30) with hU₁
  have hU₁eq : U₁ = A₁ ++ α :: B₁ := by
    rw [hU₁, hU₀eq, List.filter_append, List.filter_cons_of_pos (by simpa using hα30)]
  have hU₁nd : U₁.Nodup := hU₀nd.filter _
  have hsub1 : U₁ ⊆ U₀ := List.filter_subset_self _
  have hm21 : Sum.inl 21 ∈ U₁ := by
    rw [hU₁, List.mem_filter]; exact ⟨(hmemL₀ 21).mpr (by simp), by simp⟩
  have hm31 : Sum.inl 31 ∈ U₁ := by
    rw [hU₁, List.mem_filter]; exact ⟨(hmemL₀ 31).mpr (by simp), by simp⟩
  obtain ⟨n₃r, n₄r, hU₁split⟩ := consecutive_of_key (hsort₀.filter _) hm21 hm31 hk21
    (hnone U₁ hsub1 21 31 (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨n₃', n₄', hrows2⟩ : ∃ n₃' n₄', H₁.rows = n₃' ++ Sum.inl 21 :: Sum.inl 31 :: n₄' := by
    rw [hH₁rows]
    have hU₁split' : A₁ ++ α :: B₁ = n₃r ++ Sum.inl 21 :: Sum.inl 31 :: n₄r := by
      rw [← hU₁eq]; exact hU₁split
    exact consec_replace (hU₁eq ▸ hU₁nd) hU₁split' hα31 hProws
  -- second contraction
  obtain ⟨Q₁', Q₂', hQs2, hQ₁', hQ₂'⟩ := outsideQK_split 2 (2 + t.length) hqN'
  have hQs2' : Q = Q₁' ++ qN' :: Q₂' := hQs2
  obtain ⟨n₂, rfl⟩ : ∃ n₂, n₁ = n₂ + 1 := ⟨n₁ - 1, by
    have := H₁.cols_length; rw [hc₁] at this; simp at this; omega⟩
  have hcols2 : H₁.cols = Sum.inl w₁ ::
      (Q₁'.map Sum.inr ++ Sum.inr qN' :: (Q₂' ++ qH).map Sum.inr) := by
    rw [hc₁]
    have e1 : (Sum.inl w₁ :: Q₁.map Sum.inr) ++ Sum.inr qN :: (Q₂ ++ qH).map Sum.inr =
        Sum.inl w₁ :: (Q ++ qH).map (Sum.inr : ℕ × Fin 3 → BCol) := by rw [hQs']; simp
    rw [e1, hQs2']; simp
  have hO1w : H₁.O (Sum.inl w₁) = Sum.inl 31 := by rw [hOH₁, hO₁]
  have hX1w : H₁.X (Sum.inl w₁) = Sum.inl 21 := by
    rw [hXH₁, Function.update_of_ne (by simp), hX₁]
  have hX1N' : H₁.X (Sum.inr qN') = Sum.inl 31 := by
    rw [hXH₁, Function.update_of_ne (by simpa using hqNN'.symm), hXN']
  obtain ⟨H₂, hc₂, hr₂, hOH₂, hXH₂, hm₂⟩ := H₁.exists_contract hcols2 hO1w hX1w hX1N'
    (fun h => by
      rw [hOH₁] at h
      have := hOgt hqN' hqN' (e' := 1) hXN' h
      omega)
    (Or.inr hrows2) (by
      intro d' hd'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd'
      have hqQ : q ∈ Q := by rw [hQs2']; simp [hq]
      have hc := hQ₁' q hq
      constructor
      · rw [hOH₁]; intro h
        have := hOgt hqQ hqN' (e' := 1) hXN' h
        omega
      · rw [hXH₁]; intro h
        by_cases hq0 : (Sum.inr q : BCol) = Sum.inr qN
        · rw [hq0, Function.update_self] at h; simp at h
        · rw [Function.update_of_ne hq0] at h
          have := hXinj q qN' (hQ_mem q hqQ) (hQ_mem qN' hqN') (h.trans hXN'.symm)
          subst this; omega)
  have hr₂' : H₂.rows = H₁.rows.filter (fun z => z ≠ Sum.inl 31) := by
    rw [hr₂]; exact filter_ne_of_consec H₁.rows_nodup hrows2
  -- the final grid
  have hcolsF : H₂.cols = (Q ++ qH).map Sum.inr := by
    rw [hc₂, hQs2']; simp
  have hn : n₂ = t.length * 3 + k + 1 := by
    have := H₂.cols_length
    rw [hcolsF, List.length_map, List.length_append, hQ, outsideQK_length] at this
    simp only [hqH, winQ, List.length_ofFn] at this
    omega
  subst hn
  set A₂ := A₁.filter (fun z => z ≠ Sum.inl 31) with hA₂
  set B₂ := B₁.filter (fun z => z ≠ Sum.inl 31) with hB₂
  have hH₂rows : H₂.rows = A₂ ++ P.rows ++ B₂ := by
    rw [hr₂', hH₁rows, filter_replace _ hP31]
  set U₂ := U₁.filter (fun z => z ≠ Sum.inl 31) with hU₂
  have hU₂eq : U₂ = A₂ ++ α :: B₂ := by
    rw [hU₂, hU₁eq, List.filter_append, List.filter_cons_of_pos (by simpa using hα31)]
  have hU₂nd : U₂.Nodup := hU₁nd.filter _
  have hsort₂ : U₂.Pairwise (fun a b => sK a < sK b) := (hsort₀.filter _).filter _
  have hOF : ∀ c, H₂.O c = Hm.O c := fun c => by rw [hOH₂, hOH₁]
  have hXF : ∀ q ∈ Q, H₂.X (Sum.inr q) = Function.update (Function.update Hm.X (Sum.inr qN)
      (Sum.inl 20)) (Sum.inr qN') (Sum.inl 21) (Sum.inr q) := fun q _ => by
    rw [hXH₂, hXH₁]
  have hXFB : ∀ j, H₂.X (P.hc j) = P.xRow j := by
    intro j
    rw [hXH₂, hXH₁, Function.update_of_ne, Function.update_of_ne, (hHmB j).2]
    · intro e
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
    · intro e
      have : (P.hc j) ∈ qH.map Sum.inr := by
        rw [← winBlock_cols S p H hX hO]; exact P.hc_mem j
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp this
      rw [e] at hqe
      simp only [Sum.inr.injEq] at hqe
      subst hqe
      obtain ⟨j', hj'⟩ := List.mem_ofFn.mp hq
      have := mem_outsideQK hqN'
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
  have hXfin : ∀ q : Fin t.length × Fin 3, H₂.X (Sum.inr (q.1.val + 2, q.2)) =
      Gx.O (Sum.inr (((sM t).symm q).1.val + 2, ((sM t).symm q).2)) := by
    intro q
    set p := (sM t).symm q with hpdef
    have hMp : sM t p = q := by rw [hpdef]; exact Equiv.apply_symm_apply _ _
    rw [hXF _ (hshQ q)]
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
      have hne2 : (Sum.inr (q.1.val + 2, q.2) : BCol) ≠ Sum.inr qN' := by
        intro h; rw [h, hXN'] at hX'; simp at hX'
      rw [Function.update_of_ne hne2, Function.update_of_ne hne1, hX', hOp, hO']
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
      · -- rank `r`
        have he : (X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r = 0 := by omega
        rw [he] at hX'
        have hqq : (q.1.val + 2, q.2) = qN :=
          hXinj _ _ (hQ_mem _ (hshQ q)) (hQ_mem _ hqN) (hX'.trans hXN.symm)
        have hne2 : (Sum.inr (q.1.val + 2, q.2) : BCol) ≠ Sum.inr qN' := by
          rw [hqq]; simpa using hqNN'
        rw [Function.update_of_ne hne2, hqq, Function.update_self, hOp, hO', he]
      · omega
      · -- rank `r + 1`
        have he : (X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r = 1 := by omega
        rw [he] at hX'
        have hqq : (q.1.val + 2, q.2) = qN' :=
          hXinj _ _ (hQ_mem _ (hshQ q)) (hQ_mem _ hqN') (hX'.trans hXN'.symm)
        rw [hqq, Function.update_self, hOp, hO', he]
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
  have hH₂nd := H₂.rows_nodup
  rw [hH₂rows] at hH₂nd
  have hnotP : ∀ x, x ∈ A₂ ∨ x ∈ B₂ → x ∉ P.rows := by
    intro x hx hxP
    rcases hx with hx | hx
    · exact (List.nodup_append.mp (List.nodup_append.mp hH₂nd).1).2.2 x hx x hxP rfl
    · exact (List.nodup_append.mp hH₂nd).2.2 x (List.mem_append_right _ hxP) x hx rfl
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
  have hH₂Ow : ∀ q : Fin t.length × Fin 3, q ≠ p' → H₂.O (Sum.inr (q.1.val + 2, q.2)) = g q := by
    intro q hq
    rw [hOF, hHmO _ (hshQ q), if_neg (fun e => hq (hshp q e))]
  have hU₂mem : ∀ x, x ∈ U₂ ↔ ∃ q, g q = x := by
    intro x
    rw [hU₂eq]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (hx | rfl | hx)
      · have hxH : x ∈ H₂.rows := by rw [hH₂rows]; simp [hx]
        have hxP := hnotP x (Or.inl hx)
        obtain ⟨c, hc, hOc⟩ := H₂.exists_O_eq hxH
        rw [hcolsF] at hc
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
      · exact ⟨p', hgp⟩
      · have hxH : x ∈ H₂.rows := by rw [hH₂rows]; simp [hx]
        have hxP := hnotP x (Or.inr hx)
        obtain ⟨c, hc, hOc⟩ := H₂.exists_O_eq hxH
        rw [hcolsF] at hc
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
    · rintro ⟨q, rfl⟩
      by_cases hq : q = p'
      · right; left; rw [hq, hgp]
      · have hxH : g q ∈ H₂.rows := by
          rw [← hH₂Ow q hq]
          exact H₂.O_mem _ (by rw [hcolsF]; exact List.mem_map_of_mem (hQ_mem _ (hshQ q)))
        rw [hH₂rows] at hxH
        simp only [List.mem_append] at hxH
        rcases hxH with (h | h) | h
        · exact Or.inl h
        · exact absurd h (hgP q hq)
        · exact Or.inr (Or.inr h)
  have hUR : U₂ = (sRows t κ').map g :=
    eq_of_pairwise_key hsort₂ hsortR (fun x => by
      rw [hU₂mem x, List.mem_map]
      exact ⟨fun ⟨q, hq⟩ => ⟨q, mem_sRows t κ' q, hq⟩, fun ⟨q, _, hq⟩ => ⟨q, hq⟩⟩)
  -- the image of the marked word grid of `t`
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
  have hplain_map : (plainGrid t κ' ht).rows.map fR = U₂ := by
    rw [hUR, plainGrid_rows, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp, sfCol_zero]
    exact hfRw q
  have hsplitU : (endData t κ' ht p' H hX hO).m₁.map fR = A₂ ∧
      (endData t κ' ht p' H hX hO).m₂.map fR = B₂ := by
    have h1 : U₂ = (endData t κ' ht p' H hX hO).m₁.map fR ++
        α :: (endData t κ' ht p' H hX hO).m₂.map fR := by
      rw [← hplain_map, (endData t κ' ht p' H hX hO).rows_eq, List.map_append, List.map_cons]
      congr 2
      rw [← hgp]; exact hfRw p'
    have h2 := eq_of_append_cons_eq (h1 ▸ hU₂nd) (h1.symm.trans hU₂eq)
    exact h2
  have hrec : H₂.toGrid = L.toGrid := by
    apply toGrid_eq_of_image L H₂ upCol fR
    · exact fun c _ c' _ h => upCol_injective h
    · rintro x hx x' hx' h
      rcases hrowL x hx with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ <;>
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
      rw [hcolsF, hLcols, List.map_append, List.map_append, e1, e2]
    · rw [hH₂rows, hLdef, insertBlock_rows, List.map_append, List.map_append, hsplitU.1,
        hsplitU.2]
      congr 2
      change List.ofFn _ = (List.ofFn _).map fR
      rw [List.map_ofFn]
      congr 1
      funext i
      exact (hfRb i).symm
    · intro c hc
      rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · change H₂.O (Sum.inr (q.1.val + 2, q.2)) = fR (blockO _ _ _ (Sum.inr (q.1.val, q.2)))
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
              exact Prod.ext (Fin.ext e.1) e.2)), hfRw, hH₂Ow q hq]
      · rw [hfCb]
        change H₂.O (P.hc j) = fR (blockO _ _ _ ((markBlock t H hX hO).hc j))
        rw [blockO_hc, hOF, (hHmB j).1]
        unfold ProtBlock.oRow
        change (if H.O j = 0 then _ else _) = fR (if H.O j = 0 then _ else _)
        split_ifs <;> rw [hfRb]; rfl
    · intro c hc
      rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · change H₂.X (Sum.inr (q.1.val + 2, q.2)) = fR (blockX _ _ _ (Sum.inr (q.1.val, q.2)))
        rw [(endData t κ' ht p' H hX hO).blockX_old (by
          rw [plainGrid_cols]; exact List.mem_map.mpr ⟨q, mem_sCols t q, sfCol_zero t q⟩),
          plainGrid_X, hXfin q]
        by_cases hq : (sM t).symm q = p'
        · rw [hq, if_pos rfl, hfRb, winBlock_hr_last, ← hα, ← hgp]
        · rw [if_neg (fun e => hq (by
              simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
              exact Prod.ext (Fin.ext e.1) e.2)), hfRw]
      · rw [hfCb]
        change H₂.X (P.hc j) = fR (blockX _ _ _ ((markBlock t H hX hO).hc j))
        rw [blockX_hc, hXFB]
        exact (hfRb _).symm
  refine ⟨(markedGrid t κ' ht p' H hX hO).toGrid, ⟨κ', hadm, rfl⟩, ?_⟩
  have hfin := movesTo_insertBlock (endData t κ' ht p' H hX hO) (markData t κ' ht p' H hX hO)
  rw [← hLdef, ← hrec] at hfin
  exact hmv.trans (hm₁.trans (hm₂.trans hfin))

end OnLeConjecture.KnotTheory.MarkedCancel
