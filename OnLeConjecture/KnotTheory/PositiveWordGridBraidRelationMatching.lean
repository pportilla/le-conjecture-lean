/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationShuffle
public import OnLeConjecture.KnotTheory.TorusWordGridBaseWord

/-! # The cyclic matching near a block of three letters

For a word `B ++ t` whose first three letters `B` involve the ranks `i, i + 1, i + 2`, the cyclic
matching `positiveRectilinearWordMatching` on the corners of `B` is given by the computable
function `BraidWindow.BM` of the rank offsets of `B` and of the set of ranks occurring in `t`
(`BraidWindow.blockM_some`, `BraidWindow.blockM_none`): the arc leaving an occurrence goes to the
next occurrence in `B` if there is one, outside `B` if the rank occurs in `t`, and otherwise to
the first occurrence in `B`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-- The arc leaving an occurrence goes to the next occurrence, cyclically. -/
theorem matching_spec {m : ℕ} (w : PositiveAdjacentWord m) (r : Fin m) (h : Fin w.length)
    (c : Fin 3)
    (hc : (c = 1 ∧ r = adjacentLower w[h.val]) ∨ (c = 2 ∧ r = adjacentUpper w[h.val])) :
    ∃ q : Fin w.length × Fin 3, positiveRectilinearWordMatching w (h, c) = q ∧
      ((q.2 = 0 ∧ r = adjacentLower w[q.1.val]) ∨ (q.2 = 1 ∧ r = adjacentUpper w[q.1.val])) ∧
      ((h < q.1 ∧ ∀ k : Fin w.length, (r = adjacentLower w[k.val] ∨
          r = adjacentUpper w[k.val]) → h < k → q.1 ≤ k) ∨
        (q.1 ≤ h ∧ ∀ k : Fin w.length, (r = adjacentLower w[k.val] ∨
          r = adjacentUpper w[k.val]) → q.1 ≤ k ∧ k ≤ h)) := by
  have hlu : ∀ i : Fin (m - 1), adjacentLower i ≠ adjacentUpper i := fun i e => by
    have := congrArg Fin.val e; simp at this
  have hocc : r = adjacentLower w[h.val] ∨ r = adjacentUpper w[h.val] := by
    rcases hc with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr e
  have e1 : (h, c) = (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, ⟨h, hocc⟩⟩) := by
    rw [positiveRectilinearOutgoingArc_symm_inr]
    rcases hc with ⟨rfl, e⟩ | ⟨rfl, e⟩
    · simp [e]
    · simp [e, (hlu _).symm]
  set s := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) ⟨h, hocc⟩
    with hs
  refine ⟨(s.val, if r = adjacentLower w[s.val.val] then 0 else 1), ?_, ?_, ?_⟩
  · rw [e1, positiveRectilinearWordMatching_outgoingArc_symm_inr,
      positiveRectilinearIncomingArc_symm_inr]
  · by_cases hl : r = adjacentLower w[s.val.val]
    · exact Or.inl ⟨by simp [hl], hl⟩
    · exact Or.inr ⟨by simp [hl], s.property.resolve_left hl⟩
  · rcases positiveRectilinearSortedSuccessor_next (PositiveRectilinearRowOccurrences w r)
      ⟨h, hocc⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun k hk hlt => h2 ⟨k, hk⟩ hlt⟩
    · exact Or.inr ⟨h1, fun k hk => h2 ⟨k, hk⟩⟩

/-- The rank of the arc leaving an integer corner. -/
def outRank {m : ℕ} (w : PositiveAdjacentWord m) (p : Fin w.length × Fin 3) : ℕ :=
  (w[p.1.val]).val + if p.2 = 2 then 1 else 0

/-- The rank of the arc entering an integer corner. -/
def inRank {m : ℕ} (w : PositiveAdjacentWord m) (q : Fin w.length × Fin 3) : ℕ :=
  (w[q.1.val]).val + if q.2 = 1 then 1 else 0

/-- An integer arc enters an integer corner of the same rank. -/
theorem matching_inRank {m : ℕ} (w : PositiveAdjacentWord m) (p : Fin w.length × Fin 3)
    (hc : p.2 ≠ 0) : (positiveRectilinearWordMatching w p).2 ≠ 2 ∧
      inRank w (positiveRectilinearWordMatching w p) = outRank w p := by
  obtain ⟨h, c⟩ := p
  let r : Fin m := if c = 2 then adjacentUpper w[h.val] else adjacentLower w[h.val]
  have hcr : (c = 1 ∧ r = adjacentLower w[h.val]) ∨ (c = 2 ∧ r = adjacentUpper w[h.val]) := by
    by_cases h2 : c = 2
    · exact Or.inr ⟨h2, by simp [r, h2]⟩
    · refine Or.inl ⟨?_, by simp [r, h2]⟩
      simp only at hc
      fin_cases c <;> simp_all
  obtain ⟨q, hq1, hq2, -⟩ := matching_spec w r h c hcr
  rw [hq1]
  have hrv : r.val = outRank w (h, c) := by
    by_cases h2 : c = 2 <;> simp [outRank, r, h2, adjacentLower, adjacentUpper]
  rcases hq2 with ⟨h0, hl⟩ | ⟨h1, hu⟩
  · refine ⟨by rw [h0]; decide, ?_⟩
    rw [← hrv, hl]; simp [inRank, h0, adjacentLower]
  · refine ⟨by rw [h1]; decide, ?_⟩
    rw [← hrv, hu]; simp [inRank, h1, adjacentUpper]

theorem corner_eq_of_rank {m : ℕ} {x : Fin (m - 1)} {r : Fin m} {a b : Fin 3}
    (ha : (a = 0 ∧ r = adjacentLower x) ∨ (a = 1 ∧ r = adjacentUpper x))
    (hb : (b = 0 ∧ r = adjacentLower x) ∨ (b = 1 ∧ r = adjacentUpper x)) : a = b := by
  have hlu : adjacentLower x ≠ adjacentUpper x := fun e => by
    have := congrArg Fin.val e; simp [adjacentLower, adjacentUpper] at this
  rcases ha with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases hb with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · rfl
  · exact absurd (h1.symm.trans h2) hlu
  · exact absurd (h2.symm.trans h1) hlu
  · rfl

theorem occ_of_corner {m : ℕ} {w : PositiveAdjacentWord m} {r : Fin m} {q : Fin w.length × Fin 3}
    (h : (q.2 = 0 ∧ r = adjacentLower w[q.1.val]) ∨ (q.2 = 1 ∧ r = adjacentUpper w[q.1.val])) :
    r = adjacentLower w[q.1.val] ∨ r = adjacentUpper w[q.1.val] := by
  rcases h with ⟨-, e⟩ | ⟨-, e⟩
  · exact Or.inl e
  · exact Or.inr e

/-- Two words that agree from position `3` on, and whose first three letters involve the same
ranks, have the same matching on the corners from position `3` on, up to corners of the first
three letters. -/
theorem matching_outside_agree {m : ℕ} (w₁ w₂ : PositiveAdjacentWord m)
    (hlet : ∀ k (h₁ : k < w₁.length) (h₂ : k < w₂.length), 3 ≤ k → w₁[k] = w₂[k])
    (hlen : w₁.length = w₂.length)
    (hblk : ∀ r : Fin m, (∃ k, ∃ h₁ : k < w₁.length, k < 3 ∧
        (r = adjacentLower w₁[k] ∨ r = adjacentUpper w₁[k])) ↔
      (∃ k, ∃ h₂ : k < w₂.length, k < 3 ∧ (r = adjacentLower w₂[k] ∨ r = adjacentUpper w₂[k])))
    {h : ℕ} (h₁ : h < w₁.length) (h₂ : h < w₂.length) (hh3 : 3 ≤ h) (c : Fin 3) :
    (3 ≤ (positiveRectilinearWordMatching w₁ (⟨h, h₁⟩, c)).1.val ↔
        3 ≤ (positiveRectilinearWordMatching w₂ (⟨h, h₂⟩, c)).1.val) ∧
      (3 ≤ (positiveRectilinearWordMatching w₁ (⟨h, h₁⟩, c)).1.val →
        (positiveRectilinearWordMatching w₁ (⟨h, h₁⟩, c)).1.val =
          (positiveRectilinearWordMatching w₂ (⟨h, h₂⟩, c)).1.val ∧
        (positiveRectilinearWordMatching w₁ (⟨h, h₁⟩, c)).2 =
          (positiveRectilinearWordMatching w₂ (⟨h, h₂⟩, c)).2) := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [positiveRectilinearWordMatching_middle, positiveRectilinearWordMatching_middle]
    exact ⟨Iff.rfl, fun _ => ⟨rfl, rfl⟩⟩
  have hw : w₁[h] = w₂[h] := hlet h h₁ h₂ hh3
  let r : Fin m := if c = 2 then adjacentUpper w₁[h] else adjacentLower w₁[h]
  have hc1 : c ≠ 2 → c = 1 := fun h2 => by fin_cases c <;> simp_all
  have hcr₁ : (c = 1 ∧ r = adjacentLower w₁[(⟨h, h₁⟩ : Fin w₁.length).val]) ∨
      (c = 2 ∧ r = adjacentUpper w₁[(⟨h, h₁⟩ : Fin w₁.length).val]) := by
    by_cases h2 : c = 2
    · exact Or.inr ⟨h2, by simp [r, h2]⟩
    · exact Or.inl ⟨hc1 h2, by simp [r, h2]⟩
  have hcr₂ : (c = 1 ∧ r = adjacentLower w₂[(⟨h, h₂⟩ : Fin w₂.length).val]) ∨
      (c = 2 ∧ r = adjacentUpper w₂[(⟨h, h₂⟩ : Fin w₂.length).val]) := by
    simp only at hcr₁ ⊢
    rw [← hw]; exact hcr₁
  obtain ⟨q₁, e₁, s₁, n₁⟩ := matching_spec w₁ r ⟨h, h₁⟩ c hcr₁
  obtain ⟨q₂, e₂, s₂, n₂⟩ := matching_spec w₂ r ⟨h, h₂⟩ c hcr₂
  rw [e₁, e₂]
  have o₁ := occ_of_corner s₁
  have o₂ := occ_of_corner s₂
  -- transfer of occurrences from position `3` on
  have tr₁₂ : ∀ k (hk₁ : k < w₁.length) (hk₂ : k < w₂.length), 3 ≤ k →
      (r = adjacentLower w₁[k] ∨ r = adjacentUpper w₁[k]) →
        (r = adjacentLower w₂[k] ∨ r = adjacentUpper w₂[k]) := by
    intro k hk₁ hk₂ hk3 ho; rw [← hlet k hk₁ hk₂ hk3]; exact ho
  have tr₂₁ : ∀ k (hk₁ : k < w₁.length) (hk₂ : k < w₂.length), 3 ≤ k →
      (r = adjacentLower w₂[k] ∨ r = adjacentUpper w₂[k]) →
        (r = adjacentLower w₁[k] ∨ r = adjacentUpper w₁[k]) := by
    intro k hk₁ hk₂ hk3 ho; rw [hlet k hk₁ hk₂ hk3]; exact ho
  have fin_corner : q₁.1.val = q₂.1.val → 3 ≤ q₁.1.val → q₁.2 = q₂.2 := by
    intro hab h3
    have hx : w₂[q₂.1.val] = w₁[q₁.1.val] := by
      rw [hlet q₁.1.val q₁.1.isLt (by omega) h3]; congr 1; exact hab.symm
    rw [hx] at s₂
    exact corner_eq_of_rank s₁ s₂
  have hq₁ := q₁.1.isLt
  have hq₂ := q₂.1.isLt
  rcases n₁ with ⟨lt₁, min₁⟩ | ⟨le₁, all₁⟩ <;> rcases n₂ with ⟨lt₂, min₂⟩ | ⟨le₂, all₂⟩
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
  · by_cases hbl : ∃ k, ∃ hk : k < w₁.length, k < 3 ∧
        (r = adjacentLower w₁[k] ∨ r = adjacentUpper w₁[k])
    · obtain ⟨k₁, hk₁, hk₁3, ho₁⟩ := hbl
      obtain ⟨k₂, hk₂, hk₂3, ho₂⟩ := (hblk r).mp ⟨k₁, hk₁, hk₁3, ho₁⟩
      have b₁ : q₁.1.val ≤ k₁ := (all₁ ⟨k₁, hk₁⟩ ho₁).1
      have b₂ : q₂.1.val ≤ k₂ := (all₂ ⟨k₂, hk₂⟩ ho₂).1
      exact ⟨⟨fun h3 => by omega, fun h3 => by omega⟩, fun h3 => by omega⟩
    · have h31 : 3 ≤ q₁.1.val := by
        by_contra hlt
        exact hbl ⟨q₁.1.val, q₁.1.isLt, by omega, o₁⟩
      have h32 : 3 ≤ q₂.1.val := by
        by_contra hlt
        exact hbl ((hblk r).mpr ⟨q₂.1.val, q₂.1.isLt, by omega, o₂⟩)
      have a₁ : q₂.1.val ≤ q₁.1.val := (all₂ ⟨q₁.1.val, by omega⟩
        (tr₁₂ q₁.1.val q₁.1.isLt (by omega) h31 o₁)).1
      have a₂ : q₁.1.val ≤ q₂.1.val := (all₁ ⟨q₂.1.val, by omega⟩
        (tr₂₁ q₂.1.val (by omega) q₂.1.isLt h32 o₂)).1
      have hab : q₁.1.val = q₂.1.val := by omega
      exact ⟨⟨fun _ => h32, fun _ => h31⟩, fun h3 => ⟨hab, fin_corner hab h3⟩⟩

namespace BraidWindow

/-- The rank offset `e` occurs at the block position `k`. -/
def occB (offs : List ℕ) (e k : ℕ) : Bool := offs.getD k 0 == e || offs.getD k 0 + 1 == e

/-- The incoming corner of the offset `e` at the block position `k`. -/
def inC (offs : List ℕ) (e k : ℕ) : Fin 3 := if offs.getD k 0 = e then 0 else 1

/-- The next block position after `h` where the offset `e` occurs. -/
def nextIn (offs : List ℕ) (e h : ℕ) : Option ℕ := (List.range' (h + 1) (2 - h)).find? (occB offs e)

/-- The first block position where the offset `e` occurs. -/
def firstIn (offs : List ℕ) (e : ℕ) : Option ℕ := (List.range 3).find? (occB offs e)

/-- The rank offset of the arc leaving the corner `(h, c)`. -/
def rankOff (offs : List ℕ) (h : ℕ) (c : Fin 3) : ℕ := offs.getD h 0 + if c = 2 then 1 else 0

/-- The cyclic matching on the block corners: `some` corner of the block, or `none` for a corner
outside the block. -/
def BM (offs : List ℕ) (fl : ℕ → Bool) (h : ℕ) (c : Fin 3) : Option (ℕ × Fin 3) :=
  if c = 0 then some (h, 2) else
    match nextIn offs (rankOff offs h c) h with
    | some h' => some (h', inC offs (rankOff offs h c) h')
    | none => if fl (rankOff offs h c) then none else
        (firstIn offs (rankOff offs h c)).map fun h' => (h', inC offs (rankOff offs h c) h')

theorem occB_rankOff (offs : List ℕ) (h : ℕ) {c : Fin 3} (hc : c ≠ 0) :
    occB offs (rankOff offs h c) h = true := by
  unfold occB rankOff; split <;> simp

theorem nextIn_some {offs : List ℕ} {e h h' : ℕ} (hn : nextIn offs e h = some h') :
    h < h' ∧ h' < 3 ∧ occB offs e h' = true ∧ ∀ j, h < j → j < h' → occB offs e j = false := by
  unfold nextIn at hn
  rw [List.find?_range'_eq_some] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  rw [List.mem_range'_1] at h2
  refine ⟨by omega, by omega, h1, fun j hj hj' => ?_⟩
  simpa using h3 j (by omega) hj'

theorem nextIn_none {offs : List ℕ} {e h : ℕ} (hn : nextIn offs e h = none) :
    ∀ j, h < j → j < 3 → occB offs e j = false := by
  intro j hj hj3
  unfold nextIn at hn
  rw [List.find?_range'_eq_none] at hn
  simpa using hn j (by omega) (by omega)

theorem firstIn_some {offs : List ℕ} {e h₀ : ℕ} (hn : firstIn offs e = some h₀) :
    h₀ < 3 ∧ occB offs e h₀ = true ∧ ∀ j < h₀, occB offs e j = false := by
  unfold firstIn at hn
  rw [List.find?_range_eq_some] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  rw [List.mem_range] at h2
  exact ⟨h2, h1, fun j hj => by simpa using h3 j hj⟩

/-- Hypotheses on a block `B` of three letters with rank offsets `offs` relative to `i`, and on
the set `fl` of offsets occurring in `t`. -/
structure BlockHyp {m : ℕ} (i : Fin (m - 1)) (offs : List ℕ) (B t : PositiveAdjacentWord m)
    (fl : ℕ → Bool) : Prop where
  len : B.length = 3
  val : ∀ k (hk : k < B.length), (B[k]).val = i.val + offs.getD k 0
  offs_le : ∀ k < 3, offs.getD k 0 ≤ 1
  room : i.val + 2 < m
  fl_iff : ∀ e ≤ 2, fl e = true ↔ ∃ k, ∃ hk : k < t.length,
    i.val + e = (t[k]).val ∨ i.val + e = (t[k]).val + 1

namespace BlockHyp

variable {m : ℕ} {i : Fin (m - 1)} {offs : List ℕ} {B t : PositiveAdjacentWord m} {fl : ℕ → Bool}

theorem occ_iff (hB : BlockHyp i offs B t fl) (k : Fin (B ++ t).length) (r : Fin m) {e : ℕ}
    (hr : r.val = i.val + e) :
    (r = adjacentLower (B ++ t)[k.val] ∨ r = adjacentUpper (B ++ t)[k.val]) ↔
      (k.val < 3 ∧ occB offs e k.val = true) ∨
      (3 ≤ k.val ∧ ∃ hk : k.val - 3 < t.length,
        i.val + e = (t[k.val - 3]).val ∨ i.val + e = (t[k.val - 3]).val + 1) := by
  have hlen := hB.len
  have hk := k.isLt
  simp only [List.length_append] at hk
  by_cases h3 : k.val < 3
  · have hget : (B ++ t)[k.val] = B[k.val]'(by omega) := List.getElem_append_left (by omega)
    have hv := hB.val k.val (by omega)
    simp only [hget, Fin.ext_iff, adjacentLower, adjacentUpper, hr, hv, occB, Bool.or_eq_true,
      beq_iff_eq]
    constructor
    · rintro (h | h) <;> left <;> refine ⟨h3, ?_⟩ <;> omega
    · rintro (⟨-, h | h⟩ | ⟨h, -⟩) <;> omega
  · have hget : (B ++ t)[k.val] = t[k.val - 3]'(by omega) := by
      rw [List.getElem_append_right (by omega)]; congr 1; omega
    simp only [hget, Fin.ext_iff, adjacentLower, adjacentUpper, hr]
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨by omega, by omega, Or.inl h⟩
      · exact Or.inr ⟨by omega, by omega, Or.inr h⟩
    · rintro (⟨h, -⟩ | ⟨-, hk', h | h⟩)
      · omega
      · exact Or.inl h
      · exact Or.inr h

theorem rank_of (hB : BlockHyp i offs B t fl) {h : ℕ} (hh : h < (B ++ t).length) (hh3 : h < 3)
    {c : Fin 3} (hc : c ≠ 0) (r : Fin m) (hr : r.val = i.val + rankOff offs h c) :
    (c = 1 ∧ r = adjacentLower (B ++ t)[h]) ∨ (c = 2 ∧ r = adjacentUpper (B ++ t)[h]) := by
  have hget : (B ++ t)[h] = B[h]'(by rw [hB.len]; omega) :=
    List.getElem_append_left (by rw [hB.len]; omega)
  have hv := hB.val h (by rw [hB.len]; omega)
  rw [hget]
  rcases (show c = 1 ∨ c = 2 by fin_cases c <;> simp_all) with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    simp only [Fin.ext_iff, adjacentLower, hr, hv, rankOff]; simp
  · right; refine ⟨rfl, ?_⟩
    simp only [Fin.ext_iff, adjacentUpper, hr, hv, rankOff]; simp; omega

theorem inC_spec (hB : BlockHyp i offs B t fl) {e h' : ℕ} (hh : h' < (B ++ t).length)
    (hh3 : h' < 3) (hocc : occB offs e h' = true) (r : Fin m) (hr : r.val = i.val + e) :
    (inC offs e h' = 0 ∧ r = adjacentLower (B ++ t)[h']) ∨
      (inC offs e h' = 1 ∧ r = adjacentUpper (B ++ t)[h']) := by
  have hget : (B ++ t)[h'] = B[h']'(by rw [hB.len]; omega) :=
    List.getElem_append_left (by rw [hB.len]; omega)
  have hv := hB.val h' (by rw [hB.len]; omega)
  rw [hget]
  simp only [occB, Bool.or_eq_true, beq_iff_eq] at hocc
  unfold inC
  generalize offs.getD h' 0 = o at hv hocc ⊢
  simp only [Fin.ext_iff, adjacentLower, adjacentUpper, hr, hv]
  by_cases he : o = e
  · left; subst he; simp
  · right; simp only [he, if_false]; simp; omega

theorem rankOff_le (hB : BlockHyp i offs B t fl) {h : ℕ} (hh3 : h < 3) (c : Fin 3) :
    rankOff offs h c ≤ 2 := by
  have := hB.offs_le h hh3; unfold rankOff; split <;> omega

/-- Correctness of `BM` for a corner of the block with an image in the block. -/
theorem blockM_some (hB : BlockHyp i offs B t fl) {h : ℕ} (hh : h < (B ++ t).length)
    (hh3 : h < 3) (c : Fin 3) {q : ℕ × Fin 3} (hq : BM offs fl h c = some q) :
    ∃ hq3 : q.1 < (B ++ t).length, q.1 < 3 ∧
      positiveRectilinearWordMatching (B ++ t) (⟨h, hh⟩, c) = (⟨q.1, hq3⟩, q.2) := by
  unfold BM at hq
  by_cases hc0 : c = 0
  · subst hc0
    simp only [if_true, Option.some.injEq] at hq
    subst hq
    exact ⟨hh, hh3, positiveRectilinearWordMatching_middle _ _⟩
  · rw [if_neg hc0] at hq
    have he2 := hB.rankOff_le hh3 c
    let r : Fin m := ⟨i.val + rankOff offs h c, by have := hB.room; omega⟩
    have hc := hB.rank_of hh hh3 hc0 r rfl
    rcases hn : nextIn offs (rankOff offs h c) h with _ | h'
    · rw [hn] at hq
      cases hfl : fl (rankOff offs h c)
      · rw [hfl] at hq
        simp only [Bool.false_eq_true, if_false] at hq
        obtain ⟨h₀, h0eq, rfl⟩ := Option.map_eq_some_iff.mp hq
        obtain ⟨h03, hocc0, hmin0⟩ := firstIn_some h0eq
        have hh0 : h₀ < (B ++ t).length := by
          rw [List.length_append, hB.len]; omega
        refine ⟨hh0, h03, ?_⟩
        apply matching_eq_of_next (B ++ t) r ⟨h, hh⟩ ⟨h₀, hh0⟩ c _ hc
          (hB.inC_spec hh0 h03 hocc0 r rfl)
        right
        refine ⟨?_, fun k hk => ?_⟩
        · change h₀ ≤ h
          by_contra hlt
          have := hmin0 h (by omega)
          rw [occB_rankOff offs h hc0] at this
          exact absurd this (by simp)
        · rcases (hB.occ_iff k r rfl).mp hk with ⟨hk3, hko⟩ | ⟨hk3, hkt, hkr⟩
          · refine ⟨?_, ?_⟩
            · change h₀ ≤ k.val
              by_contra hlt
              rw [hmin0 _ (by omega)] at hko
              exact absurd hko (by simp)
            · change k.val ≤ h
              by_contra hlt
              rw [nextIn_none hn _ (by omega) hk3] at hko
              exact absurd hko (by simp)
          · exfalso
            have : fl (rankOff offs h c) = true := (hB.fl_iff _ he2).mpr ⟨_, hkt, hkr⟩
            rw [hfl] at this
            exact absurd this (by simp)
      · rw [hfl] at hq
        simp at hq
    · rw [hn] at hq
      simp only [Option.some.injEq] at hq
      subst hq
      obtain ⟨hlt, h'3, hocc', hmin'⟩ := nextIn_some hn
      have hh' : h' < (B ++ t).length := by
        rw [List.length_append, hB.len]; omega
      refine ⟨hh', h'3, ?_⟩
      apply matching_eq_of_next (B ++ t) r ⟨h, hh⟩ ⟨h', hh'⟩ c _ hc
        (hB.inC_spec hh' h'3 hocc' r rfl)
      left
      refine ⟨hlt, fun k hk hkl => ?_⟩
      change h' ≤ k.val
      rcases (hB.occ_iff k r rfl).mp hk with ⟨hk3, hko⟩ | ⟨hk3, -, -⟩
      · by_contra hlt'
        rw [hmin' _ hkl (by omega)] at hko
        exact absurd hko (by simp)
      · omega

/-- Correctness of `BM` for a corner of the block with an image outside the block. -/
theorem blockM_none (hB : BlockHyp i offs B t fl) {h : ℕ} (hh : h < (B ++ t).length)
    (hh3 : h < 3) (c : Fin 3) (hq : BM offs fl h c = none) :
    3 ≤ (positiveRectilinearWordMatching (B ++ t) (⟨h, hh⟩, c)).1.val := by
  unfold BM at hq
  by_cases hc0 : c = 0
  · rw [if_pos hc0] at hq; exact absurd hq (by simp)
  · rw [if_neg hc0] at hq
    have he2 := hB.rankOff_le hh3 c
    let r : Fin m := ⟨i.val + rankOff offs h c, by have := hB.room; omega⟩
    have hc := hB.rank_of hh hh3 hc0 r rfl
    rcases hn : nextIn offs (rankOff offs h c) h with _ | h'
    · rw [hn] at hq
      cases hfl : fl (rankOff offs h c)
      · rw [hfl] at hq
        simp only [Bool.false_eq_true, if_false, Option.map_eq_none_iff] at hq
        unfold firstIn at hq
        rw [List.find?_range_eq_none] at hq
        have := hq h hh3
        rw [occB_rankOff offs h hc0] at this
        exact absurd this (by simp)
      · obtain ⟨q, hq1, hq2, hq3⟩ := matching_spec (B ++ t) r ⟨h, hh⟩ c hc
        rw [hq1]
        have hocc : r = adjacentLower (B ++ t)[q.1.val] ∨ r = adjacentUpper (B ++ t)[q.1.val] := by
          rcases hq2 with ⟨-, e'⟩ | ⟨-, e'⟩
          · exact Or.inl e'
          · exact Or.inr e'
        rcases hq3 with ⟨hlt, -⟩ | ⟨-, hall⟩
        · by_contra h3
          rcases (hB.occ_iff q.1 r rfl).mp hocc with ⟨-, hko⟩ | ⟨h3', -⟩
          · rw [nextIn_none hn _ hlt (by omega)] at hko
            exact absurd hko (by simp)
          · omega
        · exfalso
          obtain ⟨k, hkt, hkr⟩ := (hB.fl_iff _ he2).mp hfl
          have hk' : k + 3 < (B ++ t).length := by simp [hB.len]; omega
          have hocc' := (hB.occ_iff ⟨k + 3, hk'⟩ r rfl).mpr
            (Or.inr ⟨by simp, by simpa using hkt, by simpa using hkr⟩)
          have := (hall ⟨k + 3, hk'⟩ hocc').2
          have : k + 3 ≤ h := this
          omega
    · rw [hn] at hq; simp at hq

end BlockHyp

end BraidWindow

end OnLeConjecture.KnotTheory
