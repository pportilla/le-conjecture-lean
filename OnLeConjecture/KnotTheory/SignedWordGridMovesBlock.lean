/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesTransport

/-! # The matching near a block of signed letters

For a signed word `B ++ t` whose first `K` letters `B` have indices `i + offs[k]` and signs
`sg[k]` (`true` for a positive letter), the matching `SignedGrid.sM` on the corners of `B` is
given by the computable function `SignedGrid.BMs` of the rank offsets, the signs and the set of
relative ranks occurring in `t` (`SignedGrid.BlockS.blockMs_some`,
`SignedGrid.BlockS.blockMs_none`): the arc leaving a corner goes to the next occurrence of its rank
in `B` if there is one, outside `B` if the rank occurs in `t`, and otherwise to the first
occurrence in `B`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti BraidWindow

variable {m : ℕ}

/-- The sign of the block letter `k` (`true` for a positive letter). -/
def posB (sg : List Bool) (k : ℕ) : Bool := sg.getD k true

/-- The rank offset of the arc leaving the corner `(h, c)` of the block. -/
def rankOffS (offs : List ℕ) (sg : List Bool) (h : ℕ) (c : Fin 3) : ℕ :=
  offs.getD h 0 + if (c = 2 ∧ posB sg h = true) ∨ (c = 1 ∧ posB sg h = false) then 1 else 0

/-- The incoming corner of the rank offset `e` at the block letter `k`. -/
def inCS (offs : List ℕ) (sg : List Bool) (e k : ℕ) : Fin 3 :=
  if offs.getD k 0 = e then (if posB sg k = true then 0 else 1)
  else (if posB sg k = true then 1 else 0)

/-- The next block position after `h` where the offset `e` occurs. -/
def nextInK (K : ℕ) (offs : List ℕ) (e h : ℕ) : Option ℕ :=
  (List.range' (h + 1) (K - 1 - h)).find? (occB offs e)

/-- The first block position where the offset `e` occurs. -/
def firstInK (K : ℕ) (offs : List ℕ) (e : ℕ) : Option ℕ := (List.range K).find? (occB offs e)

/-- The matching on the block corners: `some` corner of the block, or `none` for a corner
outside the block. -/
def BMs (K : ℕ) (offs : List ℕ) (sg : List Bool) (fl : ℕ → Bool) (h : ℕ) (c : Fin 3) :
    Option (ℕ × Fin 3) :=
  if c = 0 then some (h, 2) else
    match nextInK K offs (rankOffS offs sg h c) h with
    | some h' => some (h', inCS offs sg (rankOffS offs sg h c) h')
    | none => if fl (rankOffS offs sg h c) then none else
        (firstInK K offs (rankOffS offs sg h c)).map
          fun h' => (h', inCS offs sg (rankOffS offs sg h c) h')

theorem occB_rankOffS (offs : List ℕ) (sg : List Bool) (h : ℕ) {c : Fin 3} (_hc : c ≠ 0) :
    occB offs (rankOffS offs sg h c) h = true := by
  unfold occB rankOffS; split <;> simp

theorem rankOffS_le (offs : List ℕ) (sg : List Bool) (h : ℕ) (c : Fin 3) :
    rankOffS offs sg h c ≤ offs.getD h 0 + 1 := by
  unfold rankOffS; split <;> omega

theorem nextInK_some {K : ℕ} {offs : List ℕ} {e h h' : ℕ} (hn : nextInK K offs e h = some h') :
    h < h' ∧ h' < K ∧ occB offs e h' = true ∧ ∀ j, h < j → j < h' → occB offs e j = false := by
  unfold nextInK at hn
  rw [List.find?_range'_eq_some] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  rw [List.mem_range'_1] at h2
  refine ⟨by omega, by omega, h1, fun j hj hj' => ?_⟩
  simpa using h3 j (by omega) hj'

theorem nextInK_none {K : ℕ} {offs : List ℕ} {e h : ℕ} (hn : nextInK K offs e h = none) :
    ∀ j, h < j → j < K → occB offs e j = false := by
  intro j hj hjK
  unfold nextInK at hn
  rw [List.find?_range'_eq_none] at hn
  simpa using hn j (by omega) (by omega)

theorem firstInK_some {K : ℕ} {offs : List ℕ} {e h₀ : ℕ} (hn : firstInK K offs e = some h₀) :
    h₀ < K ∧ occB offs e h₀ = true ∧ ∀ j < h₀, occB offs e j = false := by
  unfold firstInK at hn
  rw [List.find?_range_eq_some] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  rw [List.mem_range] at h2
  exact ⟨h2, h1, fun j hj => by simpa using h3 j hj⟩

/-- Hypotheses on a block `B` of `K` signed letters with indices `i + offs[k]` and signs `sg[k]`,
and on the set `fl` of relative ranks up to `E` occurring in `t`. -/
structure BlockS (K E i : ℕ) (offs : List ℕ) (sg : List Bool) (B t : SignedAdjacentWord m)
    (fl : ℕ → Bool) : Prop where
  kpos : 0 < K
  len : B.length = K
  val : ∀ k (hk : k < B.length), (B[k]).1.val = i + offs.getD k 0
  sgn : ∀ k (hk : k < B.length), ((B[k]).2 = 1 ↔ posB sg k = true)
  offs_le : ∀ k < K, offs.getD k 0 + 1 ≤ E
  fl_iff : ∀ e ≤ E, fl e = true ↔ ∃ k, ∃ hk : k < t.length,
    i + e = (t[k]).1.val ∨ i + e = (t[k]).1.val + 1

namespace BlockS

variable {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {B t : SignedAdjacentWord m}
  {fl : ℕ → Bool}

theorem len_append (hB : BlockS K E i offs sg B t fl) : (B ++ t).length = K + t.length := by
  rw [List.length_append, hB.len]

theorem getL (hB : BlockS K E i offs sg B t fl) {k : ℕ} (hk : k < K)
    (hk' : k < (B ++ t).length) : (B ++ t)[k] = B[k]'(by rw [hB.len]; exact hk) :=
  List.getElem_append_left _

theorem getR (hB : BlockS K E i offs sg B t fl) {k : ℕ} (hk : K ≤ k)
    (hk' : k < (B ++ t).length) :
    (B ++ t)[k] = t[k - K]'(by rw [hB.len_append] at hk'; omega) := by
  rw [List.getElem_append_right (by rw [hB.len]; exact hk)]
  simp only [hB.len]

theorem occ_iff (hB : BlockS K E i offs sg B t fl) (k : Fin (B ++ t).length) (e : ℕ) :
    Occ (B ++ t) (i + e) k ↔ (k.val < K ∧ occB offs e k.val = true) ∨
      (K ≤ k.val ∧ ∃ hk : k.val - K < t.length,
        i + e = (t[k.val - K]).1.val ∨ i + e = (t[k.val - K]).1.val + 1) := by
  have hk : k.val < K + t.length := by have := k.isLt; have := hB.len_append; omega
  unfold Occ
  by_cases hK : k.val < K
  · rw [hB.getL hK k.isLt]
    have hv := hB.val k.val (by rw [hB.len]; exact hK)
    simp only [hv, occB, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (h | h) <;> exact Or.inl ⟨hK, by omega⟩
    · rintro (⟨-, h | h⟩ | ⟨h, -⟩) <;> omega
  · rw [hB.getR (by omega) k.isLt]
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨by omega, by omega, Or.inl h.symm⟩
      · exact Or.inr ⟨by omega, by omega, Or.inr h.symm⟩
    · rintro (⟨h, -⟩ | ⟨-, hk', h | h⟩)
      · omega
      · exact Or.inl h.symm
      · exact Or.inr h.symm

theorem oH_block (hB : BlockS K E i offs sg B t fl) {h : ℕ} (hh : h < K)
    (hhL : h < (B ++ t).length) {c : Fin 3} (hc : c ≠ 0) :
    (B ++ t).oHeight2 (⟨h, hhL⟩, c) = 2 * (i + rankOffS offs sg h c) := by
  have hv := hB.val h (by rw [hB.len]; exact hh)
  have hs := hB.sgn h (by rw [hB.len]; exact hh)
  unfold SignedAdjacentWord.oHeight2 rankOffS
  simp only [hB.getL hh hhL]
  generalize offs.getD h 0 = o at hv ⊢
  simp only [signedOHeight2, hv]
  by_cases hp : posB sg h = true
  · rw [if_pos (hs.mpr hp)]
    fin_cases c <;> simp_all
    omega
  · rw [if_neg (fun h' => hp (hs.mp h'))]
    have hp' : posB sg h = false := by simpa using hp
    fin_cases c <;> simp_all
    omega

theorem xH_block (hB : BlockS K E i offs sg B t fl) {h' e : ℕ} (hh : h' < K)
    (hhL : h' < (B ++ t).length) (hocc : occB offs e h' = true) :
    (B ++ t).xHeight2 (⟨h', hhL⟩, inCS offs sg e h') = 2 * (i + e) := by
  have hv := hB.val h' (by rw [hB.len]; exact hh)
  have hs := hB.sgn h' (by rw [hB.len]; exact hh)
  simp only [occB, Bool.or_eq_true, beq_iff_eq] at hocc
  unfold SignedAdjacentWord.xHeight2 inCS
  simp only [hB.getL hh hhL]
  generalize offs.getD h' 0 = o at hv hocc ⊢
  simp only [signedXHeight2, hv]
  by_cases hp : posB sg h' = true
  · rw [if_pos (hs.mpr hp)]
    by_cases he : o = e
    · subst he; simp [hp]
    · simp only [he, if_false, hp, if_true]; simp; omega
  · rw [if_neg (fun h'' => hp (hs.mp h''))]
    have hp' : posB sg h' = false := by simpa using hp
    by_cases he : o = e
    · subst he; simp [hp']
    · simp only [he, if_false, hp']; simp; omega

/-- Correctness of `BMs` for a block corner with an image in the block. -/
theorem blockMs_some (hB : BlockS K E i offs sg B t fl) {h : ℕ} (hh : h < K)
    (hhL : h < (B ++ t).length) (c : Fin 3) {q : ℕ × Fin 3} (hq : BMs K offs sg fl h c = some q) :
    ∃ hq3 : q.1 < (B ++ t).length, q.1 < K ∧
      sM (B ++ t) (⟨h, hhL⟩, c) = (⟨q.1, hq3⟩, q.2) := by
  have hlen := hB.len_append
  unfold BMs at hq
  by_cases hc0 : c = 0
  · subst hc0
    simp only [if_true, Option.some.injEq] at hq
    subst hq
    exact ⟨hhL, hh, sM_middle _ _⟩
  rw [if_neg hc0] at hq
  have hO := hB.oH_block hh hhL hc0
  have hs : (B ++ t).oHeight2 (⟨h, hhL⟩, c) / 2 = i + rankOffS offs sg h c := by omega
  rcases hn : nextInK K offs (rankOffS offs sg h c) h with _ | h'
  · rw [hn] at hq
    cases hfl : fl (rankOffS offs sg h c)
    · rw [hfl] at hq
      simp only [Bool.false_eq_true, if_false] at hq
      obtain ⟨h₀, h0eq, rfl⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨h03, hocc0, hmin0⟩ := firstInK_some h0eq
      have hh0 : h₀ < (B ++ t).length := by omega
      refine ⟨hh0, h03, ?_⟩
      apply sM_eq_of_spec _ _ _ hc0
      · rw [hB.xH_block h03 hh0 hocc0, hO]
      · right
        rw [hs]
        refine ⟨?_, fun k hk => ?_⟩
        · change h₀ ≤ h
          by_contra hlt
          have := hmin0 h (by omega)
          rw [occB_rankOffS offs sg h hc0] at this
          exact absurd this (by simp)
        · rcases (hB.occ_iff k _).mp hk with ⟨hk3, hko⟩ | ⟨hk3, hkt, hkr⟩
          · refine ⟨?_, ?_⟩
            · change h₀ ≤ k.val
              by_contra hlt
              rw [hmin0 _ (by omega)] at hko
              exact absurd hko (by simp)
            · change k.val ≤ h
              by_contra hlt
              rw [nextInK_none hn _ (by omega) hk3] at hko
              exact absurd hko (by simp)
          · exfalso
            have hle : rankOffS offs sg h c ≤ E :=
              (rankOffS_le offs sg h c).trans (hB.offs_le h hh)
            have : fl (rankOffS offs sg h c) = true := (hB.fl_iff _ hle).mpr ⟨_, hkt, hkr⟩
            rw [hfl] at this
            exact absurd this (by simp)
    · rw [hfl] at hq
      simp at hq
  · rw [hn] at hq
    simp only [Option.some.injEq] at hq
    subst hq
    obtain ⟨hlt, h'K, hocc', hmin'⟩ := nextInK_some hn
    have hh' : h' < (B ++ t).length := by omega
    refine ⟨hh', h'K, ?_⟩
    apply sM_eq_of_spec _ _ _ hc0
    · rw [hB.xH_block h'K hh' hocc', hO]
    · left
      rw [hs]
      refine ⟨hlt, fun k hk hkl => ?_⟩
      change h' ≤ k.val
      rcases (hB.occ_iff k _).mp hk with ⟨hk3, hko⟩ | ⟨hk3, -, -⟩
      · by_contra hlt'
        rw [hmin' _ hkl (by omega)] at hko
        exact absurd hko (by simp)
      · omega

/-- Correctness of `BMs` for a block corner with an image outside the block. -/
theorem blockMs_none (hB : BlockS K E i offs sg B t fl) {h : ℕ} (hh : h < K)
    (hhL : h < (B ++ t).length) (c : Fin 3) (hq : BMs K offs sg fl h c = none) :
    K ≤ (sM (B ++ t) (⟨h, hhL⟩, c)).1.val := by
  have hlen := hB.len_append
  unfold BMs at hq
  by_cases hc0 : c = 0
  · rw [if_pos hc0] at hq; exact absurd hq (by simp)
  rw [if_neg hc0] at hq
  have hO := hB.oH_block hh hhL hc0
  have hs : (B ++ t).oHeight2 (⟨h, hhL⟩, c) / 2 = i + rankOffS offs sg h c := by omega
  rcases hn : nextInK K offs (rankOffS offs sg h c) h with _ | h'
  · rw [hn] at hq
    cases hfl : fl (rankOffS offs sg h c)
    · rw [hfl] at hq
      simp only [Bool.false_eq_true, if_false, Option.map_eq_none_iff] at hq
      unfold firstInK at hq
      rw [List.find?_range_eq_none] at hq
      have := hq h hh
      rw [occB_rankOffS offs sg h hc0] at this
      exact absurd this (by simp)
    · have hspec := sM_spec (B ++ t) (⟨h, hhL⟩, c) hc0
      rw [hs] at hspec
      have hq2 : (sM (B ++ t) (⟨h, hhL⟩, c)).2 ≠ 2 := fun h2 => by
        have := (xHeight2_odd_iff _ _).mpr h2
        rw [sM_height, hO] at this; omega
      have hocc : Occ (B ++ t) (i + rankOffS offs sg h c) (sM (B ++ t) (⟨h, hhL⟩, c)).1 := by
        have := occ_of_xHeight2 _ hq2
        rwa [sM_height, hO, show 2 * (i + rankOffS offs sg h c) / 2 =
          i + rankOffS offs sg h c by omega] at this
      rcases hspec with ⟨hlt, -⟩ | ⟨-, hall⟩
      · by_contra h3
        rcases (hB.occ_iff _ _).mp hocc with ⟨-, hko⟩ | ⟨h3', -⟩
        · rw [nextInK_none hn _ hlt (by omega)] at hko
          exact absurd hko (by simp)
        · omega
      · exfalso
        have hle : rankOffS offs sg h c ≤ E :=
          (rankOffS_le offs sg h c).trans (hB.offs_le h hh)
        obtain ⟨k, hkt, hkr⟩ := (hB.fl_iff _ hle).mp hfl
        have hk' : k + K < (B ++ t).length := by omega
        have hocc' := (hB.occ_iff ⟨k + K, hk'⟩ _).mpr
          (Or.inr ⟨by simp, by simpa using hkt, by simpa using hkr⟩)
        have := (hall ⟨k + K, hk'⟩ hocc').2
        have : k + K ≤ h := this
        omega
  · rw [hn] at hq; simp at hq

end BlockS

/-- Twice the relative height of the arc leaving the block corner `(h, c)`. -/
def outLvlS (offs : List ℕ) (sg : List Bool) (h : ℕ) (c : Fin 3) : ℕ :=
  if c = 0 then 2 * offs.getD h 0 + 1 else 2 * rankOffS offs sg h c

/-- The relative rank of the integer arc entering the block corner `(h, c)`. -/
def inRelS (offs : List ℕ) (sg : List Bool) (h : ℕ) (c : Fin 3) : ℕ :=
  offs.getD h 0 + if (c = 1 ∧ posB sg h = true) ∨ (c = 0 ∧ posB sg h = false) then 1 else 0

/-- Twice the relative height of the arc entering the block corner `(h, c)`. -/
def inLvlS (offs : List ℕ) (sg : List Bool) (h : ℕ) (c : Fin 3) : ℕ :=
  if c = 2 then 2 * offs.getD h 0 + 1 else 2 * inRelS offs sg h c

namespace BlockS

variable {K E i : ℕ} {offs : List ℕ} {sg : List Bool} {B t : SignedAdjacentWord m}
  {fl : ℕ → Bool}

theorem len_pos (hB : BlockS K E i offs sg B t fl) : 0 < (B ++ t).length := by
  rw [hB.len_append]; have := hB.kpos; omega

theorem oH_block' (hB : BlockS K E i offs sg B t fl) {h : ℕ} (hh : h < K)
    (hhL : h < (B ++ t).length) (c : Fin 3) :
    (B ++ t).oHeight2 (⟨h, hhL⟩, c) = 2 * i + outLvlS offs sg h c := by
  by_cases hc : c = 0
  · subst hc
    have hv := hB.val h (by rw [hB.len]; exact hh)
    unfold SignedAdjacentWord.oHeight2 outLvlS
    simp only [hB.getL hh hhL]
    generalize offs.getD h 0 = o at hv ⊢
    simp only [signedOHeight2, hv]
    split_ifs <;> simp <;> omega
  · rw [hB.oH_block hh hhL hc]
    unfold outLvlS
    rw [if_neg hc]; ring

theorem xH_block' (hB : BlockS K E i offs sg B t fl) {h : ℕ} (hh : h < K)
    (hhL : h < (B ++ t).length) (c : Fin 3) :
    (B ++ t).xHeight2 (⟨h, hhL⟩, c) = 2 * i + inLvlS offs sg h c := by
  have hv := hB.val h (by rw [hB.len]; exact hh)
  have hs := hB.sgn h (by rw [hB.len]; exact hh)
  unfold SignedAdjacentWord.xHeight2 inLvlS inRelS
  simp only [hB.getL hh hhL]
  generalize offs.getD h 0 = o at hv ⊢
  simp only [signedXHeight2, hv]
  by_cases hp : posB sg h = true
  · rw [if_pos (hs.mpr hp)]
    fin_cases c <;> simp_all <;> omega
  · rw [if_neg (fun h' => hp (hs.mp h'))]
    have hp' : posB sg h = false := by simpa using hp
    fin_cases c <;> simp_all <;> omega

end BlockS

end OnLeConjecture.KnotTheory.SignedGrid
