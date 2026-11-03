/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesInit
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationAgree

/-! # Two initial grids agree outside the window

For two blocks `B₁`, `B₂` of `K` signed letters involving the same ranks, and initial window
states satisfying `SignedGrid.InitOKS` and the comparison `SignedGrid.PairOKS`, the initial grids
of `B₁ ++ t` and `B₂ ++ t` have the same markings in the outside columns
(`SignedGrid.sagree_O`, `SignedGrid.sagree_X`) and the same connecting and external rows in the
same order (`SignedGrid.sagree_rows`). This is the signed version of `BraidWindow.agree_O`,
`BraidWindow.agree_X` and `BraidWindow.agree_rows`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

/-! ### The matchings of two words agree away from the first letters -/

/-- Two signed words that agree from position `K` on, and whose first `K` letters involve the same
ranks, have the same matching on the corners from position `K` on, up to corners of the first
`K` letters. -/
theorem sM_outside_agree (w₁ w₂ : SignedAdjacentWord m) (K : ℕ)
    (hlet : ∀ k (h₁ : k < w₁.length) (h₂ : k < w₂.length), K ≤ k → w₁[k] = w₂[k])
    (hlen : w₁.length = w₂.length)
    (hblk : ∀ s, (∃ k : Fin w₁.length, k.val < K ∧ Occ w₁ s k) ↔
      (∃ k : Fin w₂.length, k.val < K ∧ Occ w₂ s k))
    {h : ℕ} (h₁ : h < w₁.length) (h₂ : h < w₂.length) (hK : K ≤ h) (c : Fin 3) :
    (K ≤ (sM w₁ (⟨h, h₁⟩, c)).1.val ↔ K ≤ (sM w₂ (⟨h, h₂⟩, c)).1.val) ∧
      (K ≤ (sM w₁ (⟨h, h₁⟩, c)).1.val →
        (sM w₁ (⟨h, h₁⟩, c)).1.val = (sM w₂ (⟨h, h₂⟩, c)).1.val ∧
        (sM w₁ (⟨h, h₁⟩, c)).2 = (sM w₂ (⟨h, h₂⟩, c)).2) := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [sM_middle, sM_middle]
    exact ⟨Iff.rfl, fun _ => ⟨rfl, rfl⟩⟩
  have hw : w₁[h] = w₂[h] := hlet h h₁ h₂ hK
  have hO : w₂.oHeight2 (⟨h, h₂⟩, c) = w₁.oHeight2 (⟨h, h₁⟩, c) := by
    simp only [SignedAdjacentWord.oHeight2, hw]
  set s := w₁.oHeight2 (⟨h, h₁⟩, c) / 2 with hs
  have spec₁ := sM_spec w₁ (⟨h, h₁⟩, c) hc0
  have spec₂ := sM_spec w₂ (⟨h, h₂⟩, c) hc0
  rw [hO, ← hs] at spec₂
  rw [← hs] at spec₁
  set q₁ := sM w₁ (⟨h, h₁⟩, c) with hq₁
  set q₂ := sM w₂ (⟨h, h₂⟩, c) with hq₂
  have hev : w₁.oHeight2 (⟨h, h₁⟩, c) % 2 = 0 := by
    have := (oHeight2_odd_iff w₁ (⟨h, h₁⟩, c)).not.mpr hc0; omega
  have hx₁ : w₁.xHeight2 q₁ = w₁.oHeight2 (⟨h, h₁⟩, c) := sM_height _ _
  have hx₂ : w₂.xHeight2 q₂ = w₁.oHeight2 (⟨h, h₁⟩, c) := by rw [hq₂, sM_height, hO]
  have hq₁2 : q₁.2 ≠ 2 := fun e => by
    have := (xHeight2_odd_iff w₁ q₁).mpr e; omega
  have hq₂2 : q₂.2 ≠ 2 := fun e => by
    have := (xHeight2_odd_iff w₂ q₂).mpr e; omega
  have o₁ : Occ w₁ s q₁.1 := by
    have := occ_of_xHeight2 w₁ hq₁2; rwa [hx₁] at this
  have o₂ : Occ w₂ s q₂.1 := by
    have := occ_of_xHeight2 w₂ hq₂2; rwa [hx₂] at this
  have tr₁₂ : ∀ k (hk₁ : k < w₁.length) (hk₂ : k < w₂.length), K ≤ k →
      Occ w₁ s ⟨k, hk₁⟩ → Occ w₂ s ⟨k, hk₂⟩ := by
    intro k hk₁ hk₂ hk ho; unfold Occ at ho ⊢; simp only at ho ⊢; rw [← hlet k hk₁ hk₂ hk]; exact ho
  have tr₂₁ : ∀ k (hk₁ : k < w₁.length) (hk₂ : k < w₂.length), K ≤ k →
      Occ w₂ s ⟨k, hk₂⟩ → Occ w₁ s ⟨k, hk₁⟩ := by
    intro k hk₁ hk₂ hk ho; unfold Occ at ho ⊢; simp only at ho ⊢; rw [hlet k hk₁ hk₂ hk]; exact ho
  have fin_corner : q₁.1.val = q₂.1.val → K ≤ q₁.1.val → q₁.2 = q₂.2 := by
    intro hab h3
    have hl : w₂[q₂.1.val] = w₁[q₁.1.val] := by
      rw [hlet q₁.1.val q₁.1.isLt (by omega) h3]; congr 1; exact hab.symm
    have e : w₂.xHeight2 (q₂.1, q₁.2) = w₂.xHeight2 q₂ := by
      rw [hx₂, ← hx₁]
      simp only [SignedAdjacentWord.xHeight2, hl]
    exact congrArg Prod.snd (eq_of_xHeight2_eq w₂ (p := (q₂.1, q₁.2)) (p' := q₂) rfl e)
  have hql₁ := q₁.1.isLt
  have hql₂ := q₂.1.isLt
  rcases spec₁ with ⟨lt₁, min₁⟩ | ⟨le₁, all₁⟩ <;> rcases spec₂ with ⟨lt₂, min₂⟩ | ⟨le₂, all₂⟩
  · have lt₁' : h < q₁.1.val := lt₁
    have lt₂' : h < q₂.1.val := lt₂
    have a₁ : q₂.1.val ≤ q₁.1.val := min₂ ⟨q₁.1.val, by omega⟩
      (tr₁₂ q₁.1.val q₁.1.isLt (by omega) (by omega) o₁) lt₁
    have a₂ : q₁.1.val ≤ q₂.1.val := min₁ ⟨q₂.1.val, by omega⟩
      (tr₂₁ q₂.1.val (by omega) q₂.1.isLt (by omega) o₂) lt₂
    have hab : q₁.1.val = q₂.1.val := by omega
    exact ⟨⟨fun _ => by omega, fun _ => by omega⟩, fun h3 => ⟨hab, fin_corner hab h3⟩⟩
  · exfalso
    have lt₁' : h < q₁.1.val := lt₁
    have := (all₂ ⟨q₁.1.val, by omega⟩ (tr₁₂ q₁.1.val q₁.1.isLt (by omega) (by omega) o₁)).2
    have : q₁.1.val ≤ h := this
    omega
  · exfalso
    have lt₂' : h < q₂.1.val := lt₂
    have := (all₁ ⟨q₂.1.val, by omega⟩ (tr₂₁ q₂.1.val (by omega) q₂.1.isLt (by omega) o₂)).2
    have : q₂.1.val ≤ h := this
    omega
  · by_cases hbl : ∃ k : Fin w₁.length, k.val < K ∧ Occ w₁ s k
    · obtain ⟨k₁, hk₁3, ho₁⟩ := hbl
      obtain ⟨k₂, hk₂3, ho₂⟩ := (hblk s).mp ⟨k₁, hk₁3, ho₁⟩
      have b₁ : q₁.1.val ≤ k₁.val := (all₁ k₁ ho₁).1
      have b₂ : q₂.1.val ≤ k₂.val := (all₂ k₂ ho₂).1
      exact ⟨⟨fun h3 => by omega, fun h3 => by omega⟩, fun h3 => by omega⟩
    · have h31 : K ≤ q₁.1.val := by
        by_contra hlt
        exact hbl ⟨q₁.1, by omega, o₁⟩
      have h32 : K ≤ q₂.1.val := by
        by_contra hlt
        exact hbl ((hblk s).mpr ⟨q₂.1, by omega, o₂⟩)
      have a₁ : q₂.1.val ≤ q₁.1.val := (all₂ ⟨q₁.1.val, by omega⟩
        (tr₁₂ q₁.1.val q₁.1.isLt (by omega) h31 o₁)).1
      have a₂ : q₁.1.val ≤ q₂.1.val := (all₁ ⟨q₂.1.val, by omega⟩
        (tr₂₁ q₂.1.val (by omega) q₂.1.isLt h32 o₂)).1
      have hab : q₁.1.val = q₂.1.val := by omega
      exact ⟨⟨fun _ => h32, fun _ => h31⟩, fun h3 => ⟨hab, fin_corner hab h3⟩⟩

/-! ### Labels of the outside arcs -/

section Outside

variable {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
  {B t : SignedAdjacentWord m} (S : WState)

theorem scorner_ne_zero_of_in {v : SignedAdjacentWord m} (p : Fin v.length × Fin 3)
    (hp : K ≤ p.1.val) (hq : (sM v p).1.val < K) : p.2 ≠ 0 := by
  intro h0
  have := sM_middle v p.1
  rw [← h0] at this
  simp only [Prod.mk.eta] at this
  rw [this] at hq
  dsimp only at hq
  omega

/-- The label of an arc leaving an outside corner. -/
theorem sgRow_out (hB : BlockS K E i offs sg B t (flagOf flags)) (hS : InitOKS K S offs sg flags)
    (p : Fin (B ++ t).length × Fin 3) (hp : K ≤ p.1.val) :
    sgRow K S (B ++ t) p = if (sM (B ++ t) p).1.val < K then
      Sum.inl (20 + ((B ++ t).oHeight2 p / 2 - i)) else Sum.inr (p.1.val, p.2) := by
  have hC2 := hS.2.2.2.2.2.2.2.2.2.1
  unfold sgRow
  rw [if_neg (by omega)]
  split_ifs with h2
  · have hnot := sxlabel_not_mem_ol S hB hS p hp h2
    have hc0 := scorner_ne_zero_of_in p hp h2
    have h20 := hC2 _ (mem_cornersK h2 _) hnot
    dsimp only at h20
    rw [h20]
    have hx := hB.xH_block' h2 (sM (B ++ t) p).1.isLt (sM (B ++ t) p).2
    have hx' : (B ++ t).xHeight2 (sM (B ++ t) p) =
        2 * i + inLvlS offs sg (sM (B ++ t) p).1.val (sM (B ++ t) p).2 := hx
    rw [sM_height] at hx'
    have hq2 : (sM (B ++ t) p).2 ≠ 2 := fun e => by
      have h1 := (xHeight2_odd_iff _ _).mpr e
      rw [sM_height] at h1
      have := (oHeight2_odd_iff _ p).mp h1
      exact hc0 this
    have hl : inLvlS offs sg (sM (B ++ t) p).1.val (sM (B ++ t) p).2 =
        2 * inRelS offs sg (sM (B ++ t) p).1.val (sM (B ++ t) p).2 := by
      unfold inLvlS; rw [if_neg hq2]
    rw [hx', hl]
    generalize inRelS offs sg (sM (B ++ t) p).1.val (sM (B ++ t) p).2 = x
    have : (2 * i + 2 * x) / 2 - i = x := by omega
    rw [this]
  · rfl

/-- The label of an arc entering an outside corner. -/
theorem sgRow_symm_out (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (q : Fin (B ++ t).length × Fin 3) (hq : K ≤ q.1.val) :
    sgRow K S (B ++ t) ((sM (B ++ t)).symm q) =
      if ((sM (B ++ t)).symm q).1.val < K then
        Sum.inl (30 + ((B ++ t).xHeight2 q / 2 - i))
      else Sum.inr (((sM (B ++ t)).symm q).1.val, ((sM (B ++ t)).symm q).2) := by
  have hbm := hS.2.2.2.2.2.2.2.1
  have hMp : sM (B ++ t) ((sM (B ++ t)).symm q) = q := Equiv.apply_symm_apply _ _
  generalize (sM (B ++ t)).symm q = p at hMp ⊢
  unfold sgRow
  split_ifs with h1 h2
  · have hb := hbm (p.1.val, p.2) (mem_cornersK h1 p.2)
    unfold bmOKS at hb
    rcases hBM : BMs K offs sg (flagOf flags) p.1.val p.2 with _ | q'
    · rw [hBM] at hb
      simp only [beq_iff_eq] at hb
      rw [hb]
      have hc0 : p.2 ≠ 0 := by
        intro h0
        have := sM_middle (B ++ t) p.1
        rw [← h0] at this
        simp only [Prod.mk.eta] at this
        rw [this] at hMp
        rw [← hMp] at hq
        exact absurd hq (by simp only; omega)
      have hO := hB.oH_block h1 p.1.isLt hc0
      simp only [Fin.eta, Prod.mk.eta] at hO
      rw [← hMp, sM_height, hO]
      congr 2
      omega
    · exfalso
      obtain ⟨hq3, hq'3, hM⟩ := hB.blockMs_some h1 p.1.isLt p.2 hBM
      simp only [Fin.eta, Prod.mk.eta, hMp] at hM
      rw [hM] at hq
      exact absurd hq (by simp only; omega)
  · exfalso; rw [hMp] at h2; omega
  · rfl

theorem smem_rows_inr (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (a : ℕ × Fin 3) :
    Sum.inr a ∈ (sInitGrid S hB hS).rows ↔
      ∃ h : a.1 < (B ++ t).length, K ≤ a.1 ∧ K ≤ (sM (B ++ t) (⟨a.1, h⟩, a.2)).1.val := by
  rw [mem_sInitGrid_rows]
  constructor
  · rintro ⟨p, hp⟩
    unfold sgRow at hp
    split_ifs at hp with h1 h2
    simp only [Sum.inr.injEq] at hp
    subst hp
    exact ⟨p.1.isLt, by omega, by simp only [Fin.eta, Prod.mk.eta]; omega⟩
  · rintro ⟨h, h3, hM⟩
    refine ⟨(⟨a.1, h⟩, a.2), ?_⟩
    unfold sgRow
    rw [if_neg (by simp only; omega), if_neg (by omega)]

theorem smem_rows_inl (hB : BlockS K E i offs sg B t (flagOf flags))
    (hS : InitOKS K S offs sg flags) (x : ℕ) :
    Sum.inl x ∈ (sInitGrid S hB hS).rows ↔ x ∈ S.rows := by
  rw [← mem_lefts, sInitGrid_lefts]

end Outside

/-! ### Comparison of two initial grids -/

/-- The finite comparison of two initial window states: the same connecting labels, at the same
heights and in the same order. -/
def PairOKS (S₁ : WState) (offs₁ : List ℕ) (sg₁ : List Bool) (S₂ : WState) (offs₂ : List ℕ)
    (sg₂ : List Bool) : Prop :=
  (∀ x ∈ connL, x ∈ S₁.rows ↔ x ∈ S₂.rows) ∧
  (∀ x ∈ connL, x ∈ S₁.rows → lvlRelS S₁ offs₁ sg₁ x = lvlRelS S₂ offs₂ sg₂ x) ∧
  (∀ x ∈ connL, ∀ y ∈ connL, x ∈ S₁.rows → y ∈ S₁.rows →
    (S₁.ri x < S₁.ri y ↔ S₂.ri x < S₂.ri y))

instance (S₁ : WState) (offs₁ : List ℕ) (sg₁ : List Bool) (S₂ : WState) (offs₂ : List ℕ)
    (sg₂ : List Bool) : Decidable (PairOKS S₁ offs₁ sg₁ S₂ offs₂ sg₂) := by
  unfold PairOKS; infer_instance

theorem getElem_append_K {B₁ B₂ t : SignedAdjacentWord m} {K : ℕ} (h₁ : B₁.length = K)
    (h₂ : B₂.length = K) (k : ℕ) (hk₁ : k < (B₁ ++ t).length) (hk₂ : k < (B₂ ++ t).length)
    (hk : K ≤ k) : (B₁ ++ t)[k] = (B₂ ++ t)[k] := by
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
  simp only [h₁, h₂]

/-- The outgoing height of the corner `a` of `t`, shifted by `K` letters. -/
def oHAt (t : SignedAdjacentWord m) (K : ℕ) (a : ℕ × Fin 3) : ℕ :=
  match t[a.1 - K]? with
  | some l => signedOHeight2 l a.2
  | none => 0

section Agree

variable {K E i : ℕ} {offs₁ offs₂ : List ℕ} {sg₁ sg₂ : List Bool} {flags : List Bool}
  {B₁ B₂ t : SignedAdjacentWord m} (S₁ S₂ : WState)

/-- The key of a row label of an initial grid, as a formula. -/
def sKf (S : WState) (offs : List ℕ) (sg : List Bool) (i K : ℕ) (t : SignedAdjacentWord m)
    (N : ℕ) : BRow → ℕ
  | Sum.inl x => (2 * i + lvlRelS S offs sg x) * N + S.ri x
  | Sum.inr a => oHAt t K a * N + (16 + cidx a.1 a.2)

theorem srows_pairwise_Kf {offs : List ℕ} {sg : List Bool} {B : SignedAdjacentWord m}
    (S : WState) (hB : BlockS K E i offs sg B t (flagOf flags)) (hS : InitOKS K S offs sg flags) :
    (sInitGrid S hB hS).rows.Pairwise (fun r r' =>
      sKf S offs sg i K t (BIG (K + t.length)) r <
        sKf S offs sg i K t (BIG (K + t.length)) r') := by
  have h := List.Pairwise.and_mem.mp (sInitGrid_rows_pairwise S hB hS)
  refine h.imp fun {r r'} ⟨hr, hr', hlt⟩ => ?_
  have hBIG : BIG (B ++ t).length = BIG (K + t.length) := by rw [hB.len_append]
  have hK : ∀ r ∈ (sInitGrid S hB hS).rows,
      skappa K S (B ++ t) (sgRowInv S (B ++ t) hB.len_pos r) =
        sKf S offs sg i K t (BIG (K + t.length)) r := by
    intro r hr
    obtain ⟨p, hp⟩ := (mem_sInitGrid_rows S hB hS r).mp hr
    rw [← hp, sgRowInv_sgRow S hB hS]
    rw [hp]
    rcases r with x | a
    · rw [skappa_inl S hB hS hp, hBIG]; rfl
    · unfold sgRow at hp
      split_ifs at hp with h1 h2
      simp only [Sum.inr.injEq] at hp
      subst hp
      unfold skappa
      have hget : (B ++ t)[p.1.val] = t[p.1.val - K]'(by have := hB.len_append; omega) :=
        hB.getR (by omega) p.1.isLt
      have hopt : t[p.1.val - K]? = some (t[p.1.val - K]'(by have := hB.len_append; omega)) :=
        List.getElem?_eq_getElem _
      unfold sgRow
      rw [if_neg h1, if_neg h2, hBIG]
      simp only [sKf, tbR, oHAt, SignedAdjacentWord.oHeight2, hget, hopt]
  rw [← hK r hr, ← hK r' hr']
  exact hlt

/-- The outside agreement hypothesis: the two blocks involve the same ranks. -/
structure AgreeS (hB₁ : BlockS K E i offs₁ sg₁ B₁ t (flagOf flags))
    (hB₂ : BlockS K E i offs₂ sg₂ B₂ t (flagOf flags)) : Prop where
  blk : ∀ s, (∃ k : Fin (B₁ ++ t).length, k.val < K ∧ Occ (B₁ ++ t) s k) ↔
    (∃ k : Fin (B₂ ++ t).length, k.val < K ∧ Occ (B₂ ++ t) s k)

variable {hB₁ : BlockS K E i offs₁ sg₁ B₁ t (flagOf flags)}
  {hB₂ : BlockS K E i offs₂ sg₂ B₂ t (flagOf flags)}

theorem AgreeS.symm (ha : AgreeS hB₁ hB₂) : AgreeS hB₂ hB₁ := ⟨fun s => (ha.blk s).symm⟩

theorem AgreeS.out (ha : AgreeS hB₁ hB₂) {h : ℕ} (h₁ : h < (B₁ ++ t).length)
    (h₂ : h < (B₂ ++ t).length) (hK : K ≤ h) (c : Fin 3) :
    (K ≤ (sM (B₁ ++ t) (⟨h, h₁⟩, c)).1.val ↔ K ≤ (sM (B₂ ++ t) (⟨h, h₂⟩, c)).1.val) ∧
      (K ≤ (sM (B₁ ++ t) (⟨h, h₁⟩, c)).1.val →
        (sM (B₁ ++ t) (⟨h, h₁⟩, c)).1.val = (sM (B₂ ++ t) (⟨h, h₂⟩, c)).1.val ∧
        (sM (B₁ ++ t) (⟨h, h₁⟩, c)).2 = (sM (B₂ ++ t) (⟨h, h₂⟩, c)).2) :=
  sM_outside_agree (B₁ ++ t) (B₂ ++ t) K (getElem_append_K hB₁.len hB₂.len)
    (by rw [hB₁.len_append, hB₂.len_append]) ha.blk h₁ h₂ hK c

theorem AgreeS.symm_out (ha : AgreeS hB₁ hB₂) {h : ℕ} (h₁ : h < (B₁ ++ t).length)
    (h₂ : h < (B₂ ++ t).length) (hK : K ≤ h) (c : Fin 3)
    (hs : K ≤ ((sM (B₁ ++ t)).symm (⟨h, h₁⟩, c)).1.val) :
    ((sM (B₁ ++ t)).symm (⟨h, h₁⟩, c)).1.val = ((sM (B₂ ++ t)).symm (⟨h, h₂⟩, c)).1.val ∧
      ((sM (B₁ ++ t)).symm (⟨h, h₁⟩, c)).2 = ((sM (B₂ ++ t)).symm (⟨h, h₂⟩, c)).2 := by
  set a := (sM (B₁ ++ t)).symm (⟨h, h₁⟩, c) with ha_def
  have hMa : sM (B₁ ++ t) a = (⟨h, h₁⟩, c) := by rw [ha_def]; exact Equiv.apply_symm_apply _ _
  have ha₂ : a.1.val < (B₂ ++ t).length := by
    have := a.1.isLt; have := hB₁.len_append; have := hB₂.len_append; omega
  have ag := ha.out a.1.isLt ha₂ hs a.2
  simp only [Fin.eta, Prod.mk.eta, hMa] at ag
  obtain ⟨hiff, himp⟩ := ag
  obtain ⟨e1, e2⟩ := himp hK
  have hM₂ : sM (B₂ ++ t) (⟨a.1.val, ha₂⟩, a.2) = (⟨h, h₂⟩, c) := by
    apply Prod.ext
    · exact Fin.ext e1.symm
    · exact e2.symm
  rw [← hM₂, Equiv.symm_apply_apply]
  exact ⟨rfl, rfl⟩

theorem sagree_O (hS₁ : InitOKS K S₁ offs₁ sg₁ flags) (hS₂ : InitOKS K S₂ offs₂ sg₂ flags)
    (ha : AgreeS hB₁ hB₂) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K (K + t.length)) :
    (sInitGrid S₁ hB₁ hS₁).O (Sum.inr q) = (sInitGrid S₂ hB₂ hS₂).O (Sum.inr q) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL₁ := hB₁.len_append
  have hL₂ := hB₂.len_append
  have h3 : K ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B₁ ++ t).length := by simp only [kc]; omega
  have h₂ : (kc k).1 < (B₂ ++ t).length := by simp only [kc]; omega
  rw [sInitGrid_O, sInitGrid_O]
  simp only [sfColInv]
  rw [sCornerOf_eq _ _ h₁, sCornerOf_eq _ _ h₂, sgRow_out S₁ hB₁ hS₁ _ h3,
    sgRow_out S₂ hB₂ hS₂ _ h3]
  have ag := ha.out h₁ h₂ h3 (kc k).2
  have hor : (B₁ ++ t).oHeight2 (⟨(kc k).1, h₁⟩, (kc k).2) =
      (B₂ ++ t).oHeight2 (⟨(kc k).1, h₂⟩, (kc k).2) := by
    unfold SignedAdjacentWord.oHeight2
    simp only
    rw [getElem_append_K hB₁.len hB₂.len _ h₁ h₂ h3]
  by_cases hc : (sM (B₁ ++ t) (⟨(kc k).1, h₁⟩, (kc k).2)).1.val < K
  · have hc' : (sM (B₂ ++ t) (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < K := by
      by_contra hh
      have := ag.1.mpr (by omega)
      omega
    rw [if_pos hc, if_pos hc', hor]
  · have hc' : ¬ (sM (B₂ ++ t) (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < K :=
      fun hh => hc (by have := ag.1; omega)
    rw [if_neg hc, if_neg hc']

theorem sagree_X (hS₁ : InitOKS K S₁ offs₁ sg₁ flags) (hS₂ : InitOKS K S₂ offs₂ sg₂ flags)
    (ha : AgreeS hB₁ hB₂) {q : ℕ × Fin 3} (hq : q ∈ outsideQK K (K + t.length)) :
    (sInitGrid S₁ hB₁ hS₁).X (Sum.inr q) = (sInitGrid S₂ hB₂ hS₂).X (Sum.inr q) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range'_1] at hk
  have hL₁ := hB₁.len_append
  have hL₂ := hB₂.len_append
  have h3 : K ≤ (kc k).1 := by simp only [kc]; omega
  have h₁ : (kc k).1 < (B₁ ++ t).length := by simp only [kc]; omega
  have h₂ : (kc k).1 < (B₂ ++ t).length := by simp only [kc]; omega
  rw [sInitGrid_X, sInitGrid_X]
  simp only [sfColInv]
  rw [sCornerOf_eq _ _ h₁, sCornerOf_eq _ _ h₂, sgRow_symm_out S₁ hB₁ hS₁ _ h3,
    sgRow_symm_out S₂ hB₂ hS₂ _ h3]
  have hir : (B₁ ++ t).xHeight2 (⟨(kc k).1, h₁⟩, (kc k).2) =
      (B₂ ++ t).xHeight2 (⟨(kc k).1, h₂⟩, (kc k).2) := by
    unfold SignedAdjacentWord.xHeight2
    simp only
    rw [getElem_append_K hB₁.len hB₂.len _ h₁ h₂ h3]
  have s₁ := ha.symm_out h₁ h₂ h3 (kc k).2
  have s₂ := ha.symm.symm_out h₂ h₁ h3 (kc k).2
  by_cases hc : ((sM (B₁ ++ t)).symm (⟨(kc k).1, h₁⟩, (kc k).2)).1.val < K
  · have hc' : ((sM (B₂ ++ t)).symm (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < K := by
      by_contra hh
      have := (s₂ (by omega)).1
      omega
    rw [if_pos hc, if_pos hc', hir]
  · obtain ⟨e1, e2⟩ := s₁ (by omega)
    have hc' : ¬ ((sM (B₂ ++ t)).symm (⟨(kc k).1, h₂⟩, (kc k).2)).1.val < K := by omega
    rw [if_neg hc, if_neg hc', e1, e2]

theorem sagree_rows (hS₁ : InitOKS K S₁ offs₁ sg₁ flags) (hS₂ : InitOKS K S₂ offs₂ sg₂ flags)
    (ha : AgreeS hB₁ hB₂) (hP : PairOKS S₁ offs₁ sg₁ S₂ offs₂ sg₂) :
    (sInitGrid S₁ hB₁ hS₁).rows.filter nonInt = (sInitGrid S₂ hB₂ hS₂).rows.filter nonInt := by
  obtain ⟨hPm, hPl, hPo⟩ := hP
  set N := BIG (K + t.length) with hN
  have hN16 : 16 ≤ N := by simp only [hN, BIG]; omega
  have hri : ∀ (S : WState) x, S.rows.length < 16 → S.ri x < 16 := fun S x h => by
    have := List.idxOf_le_length (a := x) (l := S.rows); simp only [WState.ri]; omega
  have hS₁16 : S₁.rows.length < 16 := hS₁.2.2.2.2.1
  have hS₂16 : S₂.rows.length < 16 := hS₂.2.2.2.2.1
  apply eq_of_pairwise_key (K := sKf S₁ offs₁ sg₁ i K t N)
  · exact (srows_pairwise_Kf S₁ hB₁ hS₁).filter _
  · have h := List.Pairwise.and_mem.mp ((srows_pairwise_Kf S₂ hB₂ hS₂).filter nonInt)
    refine h.imp fun {r r'} ⟨hr, hr', hlt⟩ => ?_
    rw [List.mem_filter] at hr hr'
    have hlev : ∀ x, Sum.inl x ∈ (sInitGrid S₂ hB₂ hS₂).rows → nonInt (Sum.inl x) = true →
        2 * i + lvlRelS S₂ offs₂ sg₂ x = 2 * i + lvlRelS S₁ offs₁ sg₁ x ∧ x ∈ S₁.rows := by
      intro x hx hc
      have hxc := mem_connL hc
      have hx₂ := (smem_rows_inl S₂ hB₂ hS₂ x).mp hx
      have hx₁ := (hPm x hxc).mpr hx₂
      exact ⟨by rw [hPl x hxc hx₁], hx₁⟩
    have hbd : ∀ a, Sum.inr a ∈ (sInitGrid S₂ hB₂ hS₂).rows → 16 + cidx a.1 a.2 < N := by
      intro a ha'
      obtain ⟨h, -, -⟩ := (smem_rows_inr S₂ hB₂ hS₂ a).mp ha'
      have := hB₂.len_append
      have := a.2.isLt
      simp only [hN, BIG, cidx]
      omega
    rcases r with x | a <;> rcases r' with y | b
    · obtain ⟨ex, hx₁⟩ := hlev x hr.1 hr.2
      obtain ⟨ey, hy₁⟩ := hlev y hr'.1 hr'.2
      simp only [sKf] at hlt ⊢
      rw [ex, ey] at hlt
      exact lex_transfer ((hri S₁ x hS₁16).trans_le hN16) ((hri S₂ y hS₂16).trans_le hN16)
        (fun h => (hPo x (mem_connL hr.2) y (mem_connL hr'.2) hx₁ hy₁).mpr h) hlt
    · obtain ⟨ex, -⟩ := hlev x hr.1 hr.2
      simp only [sKf] at hlt ⊢
      rw [ex] at hlt
      have := hri S₁ x hS₁16
      exact lex_transfer (by omega) (hbd b hr'.1) (fun _ => by omega) hlt
    · obtain ⟨ey, -⟩ := hlev y hr'.1 hr'.2
      simp only [sKf] at hlt ⊢
      rw [ey] at hlt
      have := hri S₂ y hS₂16
      exact lex_transfer (hbd a hr.1) (by omega) (fun h => by omega) hlt
    · exact hlt
  · intro r
    rw [List.mem_filter, List.mem_filter]
    rcases r with x | a
    · rw [smem_rows_inl, smem_rows_inl]
      constructor
      · rintro ⟨hx, hc⟩; exact ⟨(hPm x (mem_connL hc)).mp hx, hc⟩
      · rintro ⟨hx, hc⟩; exact ⟨(hPm x (mem_connL hc)).mpr hx, hc⟩
    · rw [smem_rows_inr, smem_rows_inr]
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

end OnLeConjecture.KnotTheory.SignedGrid
