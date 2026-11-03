/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesContract

/-! # Cancellation of consecutive inverse letters

For a signed word `t` in which the ranks `r` and `r + 1` occur, some signed word grid of
`σ_r^e σ_r^{-e} t` is related by grid moves to a signed word grid of `t`
(`SignedGrid.cancel_front_of_data`). The window of the two letters is reduced by the local
sequence of the written proof of Statement E (`statement_E_complete_proof.tex`, Section 7,
*Cancellation of consecutive inverse letters*) to two bivalent columns, which are then contracted
(`LabeledGrid.exists_contract`). The resulting grid is checked to be a signed word grid of `t`
directly from the definition (`SignedGrid.isSignedWordGrid_iff`). All results are
unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

/-- The final window state of a cancellation: two bivalent columns. -/
def Fbiv : WState := ⟨[(30, 20), (31, 21)], [20, 30, 21, 31]⟩

/-- The finite checks on the heights and the order of the connecting labels of a cancellation
window. -/
def CancelOK (S : WState) (sg : List Bool) : Prop :=
  lvlRelS S [0, 0] sg 20 = 0 ∧ lvlRelS S [0, 0] sg 30 = 0 ∧ lvlRelS S [0, 0] sg 21 = 2 ∧
    lvlRelS S [0, 0] sg 31 = 2 ∧ S.ri 20 < S.ri 30 ∧ S.ri 21 < S.ri 31

instance (S : WState) (sg : List Bool) : Decidable (CancelOK S sg) := by
  unfold CancelOK; infer_instance

/-! ### Auxiliary facts on initial grids -/

section Aux

variable {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
  {B t : SignedAdjacentWord m} (S : WState)

theorem outsideQK_getElem (K L k : ℕ) (hk : k < (outsideQK K L).length) :
    (outsideQK K L)[k] = kc (3 * K + k) := by
  simp [outsideQK]

theorem outsideQK_length (K L : ℕ) : (outsideQK K L).length = L * 3 - 3 * K := by
  simp [outsideQK]

theorem mem_outsideQK {K L : ℕ} {q : ℕ × Fin 3} (hq : q ∈ outsideQK K L) :
    K ≤ q.1 ∧ q.1 < L ∧ 3 * K ≤ cidx q.1 q.2 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  rw [cidx_kc]
  simp only [kc]
  omega

theorem outsideQK_split (K L : ℕ) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K L) :
    ∃ Q₁ Q₂, outsideQK K L = Q₁ ++ q :: Q₂ ∧ (∀ q' ∈ Q₁, cidx q'.1 q'.2 < cidx q.1 q.2) ∧
      (∀ q' ∈ Q₂, cidx q.1 q.2 < cidx q'.1 q'.2) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  refine ⟨(List.range' (3 * K) (k - 3 * K)).map kc,
    (List.range' (k + 1) (L * 3 - 3 * K - (k - 3 * K) - 1)).map kc, ?_, ?_, ?_⟩
  · unfold outsideQK
    have e := List.range'_append (s := 3 * K) (m := k - 3 * K)
      (n := L * 3 - 3 * K - (k - 3 * K)) (step := 1)
    simp only [Nat.one_mul] at e
    rw [show L * 3 - 3 * K = (k - 3 * K) + (L * 3 - 3 * K - (k - 3 * K)) by omega, ← e,
      show 3 * K + (k - 3 * K) = k by omega,
      show L * 3 - 3 * K - (k - 3 * K) = (L * 3 - 3 * K - (k - 3 * K) - 1) + 1 by omega,
      List.range'_succ]
    simp
  · intro q' hq'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq'
    rw [List.mem_range'_1] at hj
    rw [cidx_kc, cidx_kc]; omega
  · intro q' hq'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq'
    rw [List.mem_range'_1] at hj
    rw [cidx_kc, cidx_kc]; omega

theorem sKf_sgRow (hB : BlockS K E i offs sg B t (flagOf flags)) (hS : InitOKS K S offs sg flags)
    (p : Fin (B ++ t).length × Fin 3) :
    sKf S offs sg i K t (BIG (K + t.length)) (sgRow K S (B ++ t) p) =
      (B ++ t).oHeight2 p * BIG (K + t.length) + tbR S (sgRow K S (B ++ t) p) := by
  rcases hp : sgRow K S (B ++ t) p with x | a
  · rw [slvl_of_gRow S hB hS hp]; rfl
  · have hp' := hp
    unfold sgRow at hp'
    split_ifs at hp' with h1 h2
    simp only [Sum.inr.injEq] at hp'
    subst hp'
    have hget : (B ++ t)[p.1.val] = t[p.1.val - K]'(by have := hB.len_append; omega) :=
      hB.getR (by omega) p.1.isLt
    have hopt : t[p.1.val - K]? = some (t[p.1.val - K]'(by have := hB.len_append; omega)) :=
      List.getElem?_eq_getElem _
    simp only [sKf, tbR, oHAt, SignedAdjacentWord.oHeight2, hget, hopt]

theorem idx_lt_of_key {α : Type*} [DecidableEq α] {K : α → ℕ} {l : List α}
    (hl : l.Pairwise (fun a b => K a < K b)) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hxy : K x < K y) : l.idxOf x < l.idxOf y :=
  idxOf_lt_of_level (hl.imp le_of_lt) hx hy hxy

/-- The ordering of the ends of the two outside arcs of a rank meeting the block. -/
theorem order_NP (hB : BlockS K E i offs sg B t (flagOf flags))
    {qN qP : Fin (B ++ t).length × Fin 3} (hN : K ≤ qN.1.val) (hP : K ≤ qP.1.val)
    (hbN : ((sM (B ++ t)).symm qN).1.val < K) (hbP : (sM (B ++ t) qP).1.val < K)
    (hh : (B ++ t).xHeight2 qN = (B ++ t).oHeight2 qP) :
    (finProdFinEquiv qN).val < (finProdFinEquiv qP).val := by
  have hP0 : qP.2 ≠ 0 := scorner_ne_zero_of_in qP hP hbP
  set b := (sM (B ++ t)).symm qN with hb
  have hMb : sM (B ++ t) b = qN := by rw [hb]; exact Equiv.apply_symm_apply _ _
  have hb0 : b.2 ≠ 0 := by
    intro h0
    have := sM_middle (B ++ t) b.1
    rw [show ((b.1, 0) : Fin (B ++ t).length × Fin 3) = b from Prod.ext rfl h0.symm, hMb] at this
    have := congrArg (fun z => z.1.val) this
    simp only at this
    omega
  have hs : (B ++ t).oHeight2 b / 2 = (B ++ t).oHeight2 qP / 2 := by
    rw [← sM_height, hMb, hh]
  have oP := occ_of_oHeight2 (B ++ t) hP0
  rw [← hs] at oP
  rcases sM_spec (B ++ t) b hb0 with ⟨hlt, hmin⟩ | ⟨hle, -⟩
  · rw [hMb] at hmin
    have hle' := hmin qP.1 oP (by change b.1.val < qP.1.val; omega)
    have hle'' : qN.1.val ≤ qP.1.val := hle'
    rw [finProdFinEquiv_val3, finProdFinEquiv_val3]
    rcases Nat.lt_or_ge qN.1.val qP.1.val with h | h
    · have := qN.2.isLt; have := qP.2.isLt; omega
    · have he : qP.1 = qN.1 := Fin.ext (by omega)
      have := in_lt_out (B ++ t) he hP0 hh.symm
      rw [Fin.lt_def] at this
      omega
  · rw [hMb] at hle
    have : qN.1.val ≤ b.1.val := hle
    omega

theorem oH_ge_of_in (hB : BlockS K E i offs sg B t (flagOf flags))
    (p : Fin (B ++ t).length × Fin 3) (hp : (sM (B ++ t) p).1.val < K) :
    2 * i ≤ (B ++ t).oHeight2 p := by
  rw [← sM_height]
  have := hB.xH_block' hp (sM (B ++ t) p).1.isLt (sM (B ++ t) p).2
  simp only [Fin.eta, Prod.mk.eta] at this
  omega

theorem xH_ge_of_in (hB : BlockS K E i offs sg B t (flagOf flags))
    (q : Fin (B ++ t).length × Fin 3) (hq : ((sM (B ++ t)).symm q).1.val < K) :
    2 * i ≤ (B ++ t).xHeight2 q := by
  have hMq : sM (B ++ t) ((sM (B ++ t)).symm q) = q := Equiv.apply_symm_apply _ _
  rw [← hMq, sM_height]
  have := hB.oH_block' hq ((sM (B ++ t)).symm q).1.isLt ((sM (B ++ t)).symm q).2
  simp only [Fin.eta, Prod.mk.eta] at this
  omega

theorem even_oH_of_in (p : Fin (B ++ t).length × Fin 3) (hpK : K ≤ p.1.val)
    (hp : (sM (B ++ t) p).1.val < K) : (B ++ t).oHeight2 p % 2 = 0 := by
  have := (oHeight2_odd_iff _ p).not.mpr (scorner_ne_zero_of_in p hpK hp); omega

theorem key_lt_iff {N a a' b b' : ℕ} (hb : b < N) (hb' : b' < N) :
    a * N + b < a' * N + b' ↔ a < a' ∨ (a = a' ∧ b < b') := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy a a' with ha | ha | ha
    · exact Or.inl ha
    · subst ha; exact Or.inr ⟨rfl, by omega⟩
    · have := Nat.mul_le_mul_right N (show a' + 1 ≤ a by omega)
      rw [Nat.add_one_mul] at this
      omega
  · rintro (ha | ⟨rfl, hb''⟩)
    · have := Nat.mul_le_mul_right N (show a + 1 ≤ a' by omega)
      rw [Nat.add_one_mul] at this
      omega
    · omega

theorem sInitGrid_inr {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
    {B t : SignedAdjacentWord m} (S : WState) (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K (K + t.length)) :
    ∃ hq1 : q.1 < (B ++ t).length, K ≤ q.1 ∧
      (sInitGrid S hB hS).O (Sum.inr q) = sgRow K S (B ++ t) (⟨q.1, hq1⟩, q.2) ∧
      (sInitGrid S hB hS).X (Sum.inr q) =
        sgRow K S (B ++ t) ((sM (B ++ t)).symm (⟨q.1, hq1⟩, q.2)) := by
  obtain ⟨h1, h2, -⟩ := mem_outsideQK hq
  have hq1 : q.1 < (B ++ t).length := by rw [hB.len_append]; exact h2
  refine ⟨hq1, h1, ?_, ?_⟩
  · rw [sInitGrid_O]; simp only [sfColInv]; rw [sCornerOf_eq _ _ hq1]
  · rw [sInitGrid_X]; simp only [sfColInv]; rw [sCornerOf_eq _ _ hq1]

theorem outsideQK_colAt {K L : ℕ} (k : ℕ) (hk : k < (outsideQK K L).length) :
    (outsideQK K L)[k] = ((k + 3 * K) / 3, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩) := by
  rw [outsideQK_getElem]
  simp only [kc, Prod.mk.injEq]
  refine ⟨by omega, Fin.ext (by simp <;> omega)⟩

theorem X_label_inv {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
    {B t : SignedAdjacentWord m} (S : WState) (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K (K + t.length))
    {e' : ℕ} (h : (sInitGrid S hB hS).X (Sum.inr q) = Sum.inl (30 + e')) :
    ∃ hq1 : q.1 < (B ++ t).length,
      ((sM (B ++ t)).symm (⟨q.1, hq1⟩, q.2)).1.val < K ∧
        (B ++ t).xHeight2 (⟨q.1, hq1⟩, q.2) = 2 * i + 2 * e' := by
  obtain ⟨hq1, hK, -, hX⟩ := sInitGrid_inr S hB hS hq
  rw [hX, sgRow_symm_out S hB hS _ hK] at h
  split_ifs at h with hc
  · simp only [Sum.inl.injEq] at h
    refine ⟨hq1, hc, ?_⟩
    have hge := xH_ge_of_in hB _ hc
    set b := (sM (B ++ t)).symm (⟨q.1, hq1⟩, q.2) with hb
    have hMb : sM (B ++ t) b = (⟨q.1, hq1⟩, q.2) := by rw [hb]; exact Equiv.apply_symm_apply _ _
    have hb0 : b.2 ≠ 0 := by
      intro h0
      have := sM_middle (B ++ t) b.1
      rw [show ((b.1, 0) : Fin (B ++ t).length × Fin 3) = b from Prod.ext rfl h0.symm,
        hMb] at this
      have := congrArg (fun z => z.1.val) this
      simp only at this
      omega
    have hev : (B ++ t).xHeight2 (⟨q.1, hq1⟩, q.2) % 2 = 0 := by
      rw [← hMb, sM_height]
      have := (oHeight2_odd_iff _ b).not.mpr hb0; omega
    omega

theorem O_label_inv {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
    {B t : SignedAdjacentWord m} (S : WState) (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K (K + t.length))
    {e' : ℕ} (h : (sInitGrid S hB hS).O (Sum.inr q) = Sum.inl (20 + e')) :
    ∃ hq1 : q.1 < (B ++ t).length, K ≤ q.1 ∧
      (sM (B ++ t) (⟨q.1, hq1⟩, q.2)).1.val < K ∧
        (B ++ t).oHeight2 (⟨q.1, hq1⟩, q.2) = 2 * i + 2 * e' := by
  obtain ⟨hq1, hK, hO, -⟩ := sInitGrid_inr S hB hS hq
  rw [hO, sgRow_out S hB hS _ hK] at h
  split_ifs at h with hc
  · simp only [Sum.inl.injEq] at h
    refine ⟨hq1, hK, hc, ?_⟩
    have hge := oH_ge_of_in hB _ hc
    have hev := even_oH_of_in (K := K) (⟨q.1, hq1⟩, q.2) hK hc
    omega

end Aux

/-! ### The cancellation -/

section Main

variable {r : ℕ} {sg : List Bool} {X t : SignedAdjacentWord m}

/-- **Cancellation at the front of a word, from the finite data of a window sequence.** -/
theorem cancel_front_of_data (hB : BlockS 2 1 r [0, 0] sg X t (flagOf [true, true]))
    (S : WState) (hS : InitOKS 2 S [0, 0] sg [true, true]) {ms : List WMove}
    (hr : run S ms = some Fbiv) (hC : CancelOK S sg) :
    ∃ (G : GridDiagram ((X ++ t).length * 3)) (H : GridDiagram (t.length * 3)),
      IsSignedWordGrid (X ++ t) G ∧ IsSignedWordGrid t H ∧ G.MovesTo H := by
  obtain ⟨hl20, hl30, hl21, hl31, hri0, hri1⟩ := hC
  have hXl : X.length = 2 := hB.len
  have hL := hB.len_append
  set Gx := sInitGrid S hB hS with hGx
  set Q := outsideQK 2 (2 + t.length) with hQ
  have hR : Real S Gx (List.range (3 * 2)) Q := by
    have := sInitGrid_real S hB hS; rw [soutsideQ_len hB] at this; exact this
  obtain ⟨n, W, H, hH, hso, hmv⟩ := run_sound hR hr
  have hWl : W.length = 2 := by rw [hH.len]; rfl
  obtain ⟨w₀, w₁, rfl⟩ : ∃ w₀ w₁, W = [w₀, w₁] := by
    match W, hWl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hO₀ : H.O (Sum.inl w₀) = Sum.inl 30 := hH.O_w 0 (by simp)
  have hX₀ : H.X (Sum.inl w₀) = Sum.inl 20 := hH.X_w 0 (by simp)
  have hO₁ : H.O (Sum.inl w₁) = Sum.inl 31 := hH.O_w 1 (by simp)
  have hX₁ : H.X (Sum.inl w₁) = Sum.inl 21 := hH.X_w 1 (by simp)
  have hlefts : lefts H.rows = [20, 30, 21, 31] := hH.rows
  have hmemL : ∀ y, Sum.inl y ∈ H.rows ↔ y = 20 ∨ y = 30 ∨ y = 21 ∨ y = 31 := by
    intro y; rw [← mem_lefts, hlefts]; simp
  have hnon : ∀ x ∈ H.rows, nonInt x = true := by
    intro x hx
    rcases x with y | a
    · rcases (hmemL y).mp hx with rfl | rfl | rfl | rfl <;> decide
    · rfl
  have hHrows : H.rows = Gx.rows.filter nonInt := by
    rw [← hso.2]; exact (List.filter_eq_self.mpr hnon).symm
  set N := BIG (2 + t.length) with hN
  have hN16 : 16 ≤ N := by simp only [hN, BIG]; omega
  have hri : ∀ x, S.ri x < 16 := fun x => by
    have := List.idxOf_le_length (a := x) (l := S.rows); have := hS.2.2.2.2.1
    simp only [WState.ri]; omega
  have hsort : H.rows.Pairwise (fun a b => sKf S [0, 0] sg r 2 t N a <
      sKf S [0, 0] sg r 2 t N b) := by
    rw [hHrows]; exact (srows_pairwise_Kf S hB hS).filter _
  have hinr : ∀ a, Sum.inr a ∈ H.rows → 16 + cidx a.1 a.2 < N := by
    intro a ha
    rw [hHrows, List.mem_filter] at ha
    obtain ⟨h, -, -⟩ := (smem_rows_inr S hB hS a).mp ha.1
    have := a.2.isLt
    simp only [hN, BIG, cidx]
    omega
  -- no row of `H` has a key strictly between two connecting labels of the same rank
  have hnone : ∀ (l : List BRow), l ⊆ H.rows → ∀ (y z : ℕ), (y = 20 ∧ z = 30 ∨ y = 21 ∧ z = 31) →
      ∀ x ∈ l, ¬ (sKf S [0, 0] sg r 2 t N (Sum.inl y) < sKf S [0, 0] sg r 2 t N x ∧
        sKf S [0, 0] sg r 2 t N x < sKf S [0, 0] sg r 2 t N (Sum.inl z)) := by
    intro l hl y z hyz x hx
    have hxH := hl hx
    rcases x with y' | a
    · simp only [sKf]
      have hy' := (hmemL y').mp hxH
      rw [key_lt_iff (hri _ |>.trans_le hN16) (hri _ |>.trans_le hN16),
        key_lt_iff (hri _ |>.trans_le hN16) (hri _ |>.trans_le hN16)]
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hy' with rfl | rfl | rfl | rfl <;> simp only [hl20, hl30, hl21, hl31] <;> omega
    · simp only [sKf]
      have hb := hinr a hxH
      rw [key_lt_iff (hri _ |>.trans_le hN16) hb, key_lt_iff hb (hri _ |>.trans_le hN16)]
      have h1 := hri y
      have h2 := hri z
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [hl20, hl30, hl21, hl31] <;> omega
  -- the outside columns carrying the connecting labels
  have hout : ∀ c ∈ H.cols, (∀ k (hk : k < 2), c ≠ Sum.inl ([w₀, w₁][k]'(by simpa using hk))) →
      ∃ q ∈ Q, c = Sum.inr q := by
    intro c hc hne
    rcases hH.mem_cols hc with ⟨k, hk, rfl⟩ | hq
    · exact absurd rfl (hne k (by simpa using hk))
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hq; exact ⟨q, hq', rfl⟩
  have hwin : ∀ k (hk : k < 2), [w₀, w₁][k]'(by simpa using hk) = w₀ ∨
      [w₀, w₁][k]'(by simpa using hk) = w₁ := by
    intro k hk; interval_cases k <;> simp
  have findX : ∀ e', e' ≤ 1 → ∃ q ∈ Q, H.X (Sum.inr q) = Sum.inl (30 + e') := by
    intro e' he'
    have hm : Sum.inl (30 + e') ∈ H.rows := (hmemL _).mpr (by omega)
    obtain ⟨c, hc, hXc⟩ := H.exists_X_eq hm
    obtain ⟨q, hq, rfl⟩ := hout c hc (fun k hk he => by
      rcases hwin k hk with h | h <;> rw [he, h] at hXc
      · rw [hX₀] at hXc; simp at hXc; omega
      · rw [hX₁] at hXc; simp at hXc; omega)
    exact ⟨q, hq, hXc⟩
  have findO : ∀ e', e' ≤ 1 → ∃ q ∈ Q, H.O (Sum.inr q) = Sum.inl (20 + e') := by
    intro e' he'
    have hm : Sum.inl (20 + e') ∈ H.rows := (hmemL _).mpr (by omega)
    obtain ⟨c, hc, hOc⟩ := H.exists_O_eq hm
    obtain ⟨q, hq, rfl⟩ := hout c hc (fun k hk he => by
      rcases hwin k hk with h | h <;> rw [he, h] at hOc
      · rw [hO₀] at hOc; simp at hOc; omega
      · rw [hO₁] at hOc; simp at hOc; omega)
    exact ⟨q, hq, hOc⟩
  obtain ⟨qN, hqN, hXN⟩ := findX 0 (by norm_num)
  obtain ⟨qN', hqN', hXN'⟩ := findX 1 le_rfl
  obtain ⟨qP, hqP, hOP⟩ := findO 0 (by norm_num)
  obtain ⟨qP', hqP', hOP'⟩ := findO 1 le_rfl
  simp only [Nat.add_zero] at hXN hOP
  have hcolQ : ∀ q ∈ Q, Sum.inr q ∈ H.cols := fun q hq => by
    rw [hH.cols]; exact List.mem_append_right _ (List.mem_map_of_mem hq)
  -- the order of the ends of the connecting arcs
  have horder : ∀ {qn qp : ℕ × Fin 3} {e' : ℕ}, qn ∈ Q → qp ∈ Q →
      H.X (Sum.inr qn) = Sum.inl (30 + e') → H.O (Sum.inr qp) = Sum.inl (20 + e') →
      cidx qn.1 qn.2 < cidx qp.1 qp.2 := by
    intro qn qp e' hqn hqp hx ho
    rw [(hso.1 qn hqn).2] at hx
    rw [(hso.1 qp hqp).1] at ho
    obtain ⟨h1, hb1, hx1⟩ := X_label_inv S hB hS hqn hx
    obtain ⟨h2, hK2, hb2, ho2⟩ := O_label_inv S hB hS hqp ho
    obtain ⟨hK1, -, -⟩ := mem_outsideQK hqn
    have := order_NP hB (qN := (⟨qn.1, h1⟩, qn.2)) (qP := (⟨qp.1, h2⟩, qp.2)) hK1 hK2 hb1 hb2
      (by rw [hx1, ho2])
    simp only [finProdFinEquiv_val3, Fin.val_mk] at this
    simp only [cidx]; omega
  have hNP := horder (e' := 0) hqN hqP (by simpa using hXN) (by simpa using hOP)
  have hNP' := horder hqN' hqP' hXN' hOP'
  -- injectivity on the columns
  have hOinj : ∀ q q' : ℕ × Fin 3, q ∈ Q → q' ∈ Q → H.O (Sum.inr q) = H.O (Sum.inr q') →
      q = q' := fun q q' hq hq' h => by
    have := H.O_inj _ (hcolQ q hq) _ (hcolQ q' hq') h; simpa using this
  have hXinj : ∀ q q' : ℕ × Fin 3, q ∈ Q → q' ∈ Q → H.X (Sum.inr q) = H.X (Sum.inr q') →
      q = q' := fun q q' hq hq' h => by
    have := H.X_inj _ (hcolQ q hq) _ (hcolQ q' hq') h; simpa using this
  have hQs_mem : ∀ q, q ∈ Q → q ∈ outsideQK 2 (2 + t.length) := fun q hq => hq
  have hqNN' : qN ≠ qN' := by
    intro h; rw [h, hXN'] at hXN; simp at hXN
  -- first contraction
  obtain ⟨Q₁, Q₂, hQs, hQ₁, hQ₂⟩ := outsideQK_split 2 (2 + t.length) hqN
  have hQs' : Q = Q₁ ++ qN :: Q₂ := hQs
  obtain ⟨n₁, rfl⟩ : ∃ n₁, n = n₁ + 1 := ⟨n - 1, by
    have := H.cols_length; rw [hH.cols] at this; simp at this; omega⟩
  have hcols1 : H.cols = Sum.inl w₀ ::
      ((Sum.inl w₁ :: Q₁.map Sum.inr) ++ Sum.inr qN :: Q₂.map Sum.inr) := by
    rw [hH.cols, hQs']; simp
  have hk20 : sKf S [0, 0] sg r 2 t N (Sum.inl 20) < sKf S [0, 0] sg r 2 t N (Sum.inl 30) := by
    simp only [sKf, hl20, hl30]; omega
  have hk21 : sKf S [0, 0] sg r 2 t N (Sum.inl 21) < sKf S [0, 0] sg r 2 t N (Sum.inl 31) := by
    simp only [sKf, hl21, hl31]; omega
  obtain ⟨m₁, m₂, hrows1⟩ := consecutive_of_key hsort ((hmemL 20).mpr (by simp))
    ((hmemL 30).mpr (by simp)) hk20 (hnone H.rows (fun _ h => h) 20 30 (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨H₁, hc₁, hr₁, hOH₁, hXH₁, hm₁⟩ := H.exists_contract hcols1 hO₀ hX₀ hXN
    (fun h => by
      have := hOinj qN qP hqN hqP (h.trans hOP.symm)
      subst this; omega)
    (Or.inr hrows1) (by
      intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · rw [hO₁, hX₁]; simp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd'
        have hqQ : q ∈ Q := by rw [hQs']; simp [hq]
        have hc := hQ₁ q hq
        constructor
        · intro h
          have := hOinj q qP hqQ hqP (h.trans hOP.symm)
          subst this; omega
        · intro h
          have := hXinj q qN hqQ hqN (h.trans hXN.symm)
          subst this; omega)
  -- second contraction
  obtain ⟨Q₁', Q₂', hQs2, hQ₁', hQ₂'⟩ := outsideQK_split 2 (2 + t.length) hqN'
  have hQs2' : Q = Q₁' ++ qN' :: Q₂' := hQs2
  obtain ⟨n₂, rfl⟩ : ∃ n₂, n₁ = n₂ + 1 := ⟨n₁ - 1, by
    have := H₁.cols_length; rw [hc₁] at this; simp at this; omega⟩
  have hcols2 : H₁.cols = Sum.inl w₁ :: (Q₁'.map Sum.inr ++ Sum.inr qN' :: Q₂'.map Sum.inr) := by
    rw [hc₁]
    have e1 : (Sum.inl w₁ :: Q₁.map Sum.inr) ++ Sum.inr qN :: Q₂.map Sum.inr =
        Sum.inl w₁ :: Q.map (Sum.inr : ℕ × Fin 3 → BCol) := by rw [hQs']; simp
    rw [e1, hQs2']; simp
  have hO1w : H₁.O (Sum.inl w₁) = Sum.inl 31 := by rw [hOH₁, hO₁]
  have hX1w : H₁.X (Sum.inl w₁) = Sum.inl 21 := by
    rw [hXH₁, Function.update_of_ne (by simp), hX₁]
  have hX1N' : H₁.X (Sum.inr qN') = Sum.inl 31 := by
    rw [hXH₁, Function.update_of_ne (by simpa using hqNN'.symm), hXN']
  have hsl1 : H₁.rows.Sublist H.rows := by
    rw [hr₁, hrows1]
    exact ((List.sublist_cons_self _ m₂).cons₂ _).append_left m₁
  have hsort1 : H₁.rows.Pairwise (fun a b => sKf S [0, 0] sg r 2 t N a <
      sKf S [0, 0] sg r 2 t N b) := hsort.sublist hsl1
  have hsub1 : H₁.rows ⊆ H.rows := hsl1.subset
  have hm21 : Sum.inl 21 ∈ H₁.rows := by
    have h := (hmemL 21).mpr (by simp)
    rw [hrows1] at h
    rw [hr₁]
    simp only [List.mem_append, List.mem_cons] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl h
    · simp at h
    · simp at h
    · exact Or.inr (Or.inr h)
  have hm31 : Sum.inl 31 ∈ H₁.rows := by
    have h := (hmemL 31).mpr (by simp)
    rw [hrows1] at h
    rw [hr₁]
    simp only [List.mem_append, List.mem_cons] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl h
    · simp at h
    · simp at h
    · exact Or.inr (Or.inr h)
  obtain ⟨m₁', m₂', hrows2⟩ := consecutive_of_key hsort1 hm21 hm31 hk21
    (hnone H₁.rows hsub1 21 31 (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨H₂, hc₂, hr₂, hOH₂, hXH₂, hm₂⟩ := H₁.exists_contract hcols2 hO1w hX1w hX1N'
    (fun h => by
      rw [hOH₁] at h
      have := hOinj qN' qP' hqN' hqP' (h.trans hOP'.symm)
      subst this; omega)
    (Or.inr hrows2) (by
      intro d' hd'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd'
      have hqQ : q ∈ Q := by rw [hQs2']; simp [hq]
      have hc := hQ₁' q hq
      constructor
      · rw [hOH₁]; intro h
        have := hOinj q qP' hqQ hqP' (h.trans hOP'.symm)
        subst this; omega
      · rw [hXH₁]; intro h
        by_cases hq0 : (Sum.inr q : BCol) = Sum.inr qN
        · rw [hq0, Function.update_self] at h; simp at h
        · rw [Function.update_of_ne hq0] at h
          have := hXinj q qN' hqQ hqN' (h.trans hXN'.symm)
          subst this; omega)
  -- the final grid
  have hcolsF : H₂.cols = Q.map Sum.inr := by
    rw [hc₂, hQs2']; simp
  have hn : n₂ = t.length * 3 := by
    have := H₂.cols_length
    rw [hcolsF, List.length_map, hQ, outsideQK_length] at this
    omega
  have hOF : ∀ q ∈ Q, H₂.O (Sum.inr q) = Gx.O (Sum.inr q) := fun q hq => by
    rw [hOH₂, hOH₁, (hso.1 q hq).1]
  have hXF : ∀ q ∈ Q, H₂.X (Sum.inr q) = Function.update (Function.update H.X (Sum.inr qN)
      (Sum.inl 20)) (Sum.inr qN') (Sum.inl 21) (Sum.inr q) := fun q hq => by
    rw [hXH₂, hXH₁]
  have hsort2 : H₂.rows.Pairwise (fun a b => sKf S [0, 0] sg r 2 t N a <
      sKf S [0, 0] sg r 2 t N b) := by
    rw [hr₂]
    refine hsort1.sublist ?_
    rw [hrows2]
    exact ((List.sublist_cons_self _ m₂').cons₂ _).append_left m₁'
  -- the corners of `t` inside `X ++ t`
  have hshQ : ∀ a : Fin t.length × Fin 3, (a.1.val + 2, a.2) ∈ Q := by
    intro a
    rw [hQ]
    apply List.mem_map.mpr
    refine ⟨a.2.val + 3 * (a.1.val + 2), ?_, ?_⟩
    · rw [List.mem_range'_1]; have := a.1.isLt; have := a.2.isLt; omega
    · have := a.2.isLt
      simp only [kc, Prod.mk.injEq]
      exact ⟨by omega, Fin.ext (by simp <;> omega)⟩
  have hcolAt : ∀ a : Fin t.length × Fin 3,
      H₂.colAt (Fin.cast hn.symm (finProdFinEquiv a)) = Sum.inr (a.1.val + 2, a.2) := by
    intro a
    rw [H₂.colAt_eq_of_cols hcolsF]
    simp only [List.getElem_map, Fin.val_cast]
    congr 1
    refine (outsideQK_colAt (K := 2) (L := 2 + t.length) _ _).trans ?_
    have := a.2.isLt
    simp only [finProdFinEquiv_val3, Prod.mk.injEq]
    exact ⟨by omega, Fin.ext (by simp <;> omega)⟩
  have hcorner : ∀ a : Fin t.length × Fin 3, ∃ ha : a.1.val + 2 < (X ++ t).length,
      Gx.O (Sum.inr (a.1.val + 2, a.2)) = sgRow 2 S (X ++ t) (⟨a.1.val + 2, ha⟩, a.2) ∧
      Gx.X (Sum.inr (a.1.val + 2, a.2)) =
        sgRow 2 S (X ++ t) ((sM (X ++ t)).symm (⟨a.1.val + 2, ha⟩, a.2)) := by
    intro a
    obtain ⟨ha, -, hO, hX⟩ := sInitGrid_inr S hB hS (hshQ a)
    exact ⟨ha, hO, hX⟩
  have hoH : ∀ (a : Fin t.length × Fin 3) (ha : a.1.val + 2 < (X ++ t).length),
      (X ++ t).oHeight2 (⟨a.1.val + 2, ha⟩, a.2) = t.oHeight2 a := by
    intro a ha
    simp only [SignedAdjacentWord.oHeight2, getElem_shift X t hXl a.1.isLt]
  have hxH : ∀ (a : Fin t.length × Fin 3) (ha : a.1.val + 2 < (X ++ t).length),
      (X ++ t).xHeight2 (⟨a.1.val + 2, ha⟩, a.2) = t.xHeight2 a := by
    intro a ha
    simp only [SignedAdjacentWord.xHeight2, getElem_shift X t hXl a.1.isLt]
  have hBIG : BIG (X ++ t).length = N := by rw [hN, hL]
  refine ⟨Gx.toGrid, GridDiagram.castSize hn H₂.toGrid, sInitGrid_signed S hB hS, ?_,
    hmv.trans (hm₁.trans (hm₂.trans (GridDiagram.movesTo_castSize hn _)))⟩
  rw [isSignedWordGrid_iff]
  constructor
  · intro a b hab
    rw [Fin.lt_def, GridDiagram.castSize_O_apply, GridDiagram.castSize_O_apply, Fin.val_cast,
      Fin.val_cast, LabeledGrid.toGrid_O_val, LabeledGrid.toGrid_O_val, hcolAt, hcolAt,
      hOF _ (hshQ a), hOF _ (hshQ b)]
    obtain ⟨ha, hOa, -⟩ := hcorner a
    obtain ⟨hb, hOb, -⟩ := hcorner b
    rw [hOa, hOb]
    apply idx_lt_of_key hsort2
    · rw [← hOa, ← hOF _ (hshQ a)]; exact H₂.O_mem _ (by rw [hcolsF]; exact List.mem_map_of_mem (hshQ a))
    · rw [← hOb, ← hOF _ (hshQ b)]; exact H₂.O_mem _ (by rw [hcolsF]; exact List.mem_map_of_mem (hshQ b))
    rw [sKf_sgRow S hB hS, sKf_sgRow S hB hS, hoH, hoH, ← hN]
    have h1 := stb_lt (K := 2) S (X ++ t) hS.2.2.2.2.1 (⟨a.1.val + 2, ha⟩, a.2)
    have h2 := stb_lt (K := 2) S (X ++ t) hS.2.2.2.2.1 (⟨b.1.val + 2, hb⟩, b.2)
    rw [hBIG] at h1 h2
    have := Nat.mul_le_mul_right N (show t.oHeight2 a + 1 ≤ t.oHeight2 b by omega)
    rw [Nat.add_one_mul] at this
    omega
  · intro q
    apply Fin.ext
    rw [GridDiagram.castSize_X_apply, GridDiagram.castSize_O_apply, Fin.val_cast, Fin.val_cast,
      LabeledGrid.toGrid_X_val, LabeledGrid.toGrid_O_val, hcolAt, hcolAt]
    congr 1
    set p := (sM t).symm q with hpdef
    have hMp : sM t p = q := by rw [hpdef]; exact Equiv.apply_symm_apply _ _
    rw [hXF _ (hshQ q), hOF _ (hshQ p)]
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
      have hX' : H.X (Sum.inr (q.1.val + 2, q.2)) = Sum.inr (p.1.val + 2, p.2) := by
        rw [(hso.1 _ (hshQ q)).2, hXq, ← hsMx, Equiv.symm_apply_apply, hO']
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
      have hX' : H.X (Sum.inr (q.1.val + 2, q.2)) =
          Sum.inl (30 + ((X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r)) := by
        rw [(hso.1 _ (hshQ q)).2, hXq, hX'', hheq]
      have hmem : Sum.inl (30 + ((X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r)) ∈ H.rows := by
        rw [← hX']; exact H.X_mem _ (hcolQ _ (hshQ q))
      rcases (hmemL _).mp hmem with h | h | h | h
      · omega
      · -- rank `r`
        have he : (X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r = 0 := by omega
        rw [he] at hX'
        have hqq : (q.1.val + 2, q.2) = qN :=
          hXinj _ _ (hshQ q) hqN (hX'.trans hXN.symm)
        have hne2 : (Sum.inr (q.1.val + 2, q.2) : BCol) ≠ Sum.inr qN' := by
          rw [hqq]; simpa using hqNN'
        rw [Function.update_of_ne hne2, hqq, Function.update_self, hOp, hO', he]
      · omega
      · -- rank `r + 1`
        have he : (X ++ t).oHeight2 (⟨p.1.val + 2, hp⟩, p.2) / 2 - r = 1 := by omega
        rw [he] at hX'
        have hqq : (q.1.val + 2, q.2) = qN' :=
          hXinj _ _ (hshQ q) hqN' (hX'.trans hXN'.symm)
        rw [hqq, Function.update_self, hOp, hO', he]

end Main

end OnLeConjecture.KnotTheory.SignedGrid
