/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamCompression

/-!
# Counting the columns kept by a compression

Let `π` be a correction path from `seamState p.1 p.2`, and let `L, R` be two columns. Assume that
`π` keeps fixed every west column other than `L` and `R`, and every column `c` with
`n < c < n + m` whose initial row is high. Deleting these columns with
`SeamCorrectionPath.compress` keeps at most two west columns and at most three east columns:
the columns `n` and `n + m` and the unique east column with a low initial row. The compressed path
therefore lives on a seam with parameters `n' ≤ 2` and `m' ≤ 2`
(`SeamCorrectionPath.exists_small_of_fixesColumn`).
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n m k : ℕ}

/-- A retained state has exactly one southwest column. -/
private theorem seamSouthwestColumns_seamState_card (x : GridState (n + 1))
    (z : GridState (m + 1)) :
    (seamSouthwestColumns (n := n) (m := m) (seamState x z)).card = 1 := by
  rw [seamSouthwestColumns_card]
  have h : seamNortheastColumns (n := n) (m := m) (seamState x z) = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty, seamNortheastColumns_nonempty_iff, not_not]
    exact seamState_mem_pairSector x z
  rw [h, Finset.card_empty]

/-- The seam grid has `m + 1` east columns. -/
private theorem seam_east_columns_card :
    (Finset.univ.filter fun c : Fin (n + m + 1) => n ≤ c.val).card = m + 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun c : Fin (n + m + 1) => c.val < n)
  rw [seam_first_columns_card, Finset.card_univ, Fintype.card_fin] at h
  have he : (Finset.univ.filter fun c : Fin (n + m + 1) => ¬ c.val < n) =
      Finset.univ.filter fun c => n ≤ c.val := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [he] at h
  omega

/-- A correction path that keeps fixed every west column except `L` and `R`, and every column
strictly between `n` and `n + m` with a high initial row, compresses to a correction path of the
same length on a seam with both parameters at most two. -/
theorem SeamCorrectionPath.exists_small_of_fixesColumn {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (L R : Fin (n + m + 1))
    (hwest : ∀ c : Fin (n + m + 1), c.val < n → c ≠ L → c ≠ R → π.FixesColumn c)
    (heast : ∀ c : Fin (n + m + 1), n < c.val → c.val < n + m →
      n < (seamState p.1 p.2 c).val → π.FixesColumn c) :
    ∃ (n' m' : ℕ) (p' q' : SeamRetainedIndex n' m'), n' ≤ 2 ∧ m' ≤ 2 ∧
      Nonempty (SeamCorrectionPath (n := n') (m := m') k p' q') := by
  classical
  let U : Finset (Fin (n + m + 1)) := Finset.univ.filter fun c =>
    (c.val < n ∧ c ≠ L ∧ c ≠ R) ∨ (n < c.val ∧ c.val < n + m ∧ n < (seamState p.1 p.2 c).val)
  have hfix : ∀ c ∈ U, π.FixesColumn c := by
    intro c hc
    rcases (Finset.mem_filter.mp hc).2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact hwest c h1 h2 h3
    · exact heast c h1 h2 h3
  have htype : ∀ c ∈ U, c.val < n ∨ n < (seamState p.1 p.2 c).val := by
    intro c hc
    rcases (Finset.mem_filter.mp hc).2 with ⟨h1, -, -⟩ | ⟨-, -, h3⟩
    · exact Or.inl h1
    · exact Or.inr h3
  obtain ⟨n', m', p', q', hn', hm', hπ'⟩ := π.compress U hfix htype
  refine ⟨n', m', p', q', ?_, ?_, hπ'⟩
  · have hsub : (Finset.univ.filter fun c : Fin (n + m + 1) => c.val < n) ⊆
        (U.filter fun c => c.val < n) ∪ {L, R} := by
      intro c hc
      rw [Finset.mem_filter] at hc
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      by_cases hL : c = L
      · exact Or.inr (Or.inl hL)
      by_cases hR : c = R
      · exact Or.inr (Or.inr hR)
      exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hc.2, hL, hR⟩⟩, hc.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (U.filter fun c => c.val < n) {L, R}
    have h3 : ({L, R} : Finset (Fin (n + m + 1))).card ≤ 2 := Finset.card_le_two
    rw [seam_first_columns_card] at h1
    omega
  · let S : Finset (Fin (n + m + 1)) := {⟨n, by omega⟩, Fin.last (n + m)}
    have hsub : (Finset.univ.filter fun c : Fin (n + m + 1) => n ≤ c.val) ⊆
        (U.filter fun c => n ≤ c.val) ∪
          (S ∪ seamSouthwestColumns (n := n) (m := m) (seamState p.1 p.2)) := by
      intro c hc
      rw [Finset.mem_filter] at hc
      simp only [S, U, Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton, mem_seamSouthwestColumns, Finset.mem_univ, true_and]
      by_cases h1 : c.val = n
      · exact Or.inr (Or.inl (Or.inl (Fin.ext h1)))
      by_cases h2 : c.val = n + m
      · exact Or.inr (Or.inl (Or.inr (Fin.ext (by rw [h2, Fin.val_last]))))
      by_cases h3 : (seamState p.1 p.2 c).val ≤ n
      · exact Or.inr (Or.inr ⟨hc.2, h3⟩)
      · have hc' := c.isLt
        exact Or.inl ⟨Or.inr ⟨by omega, by omega, by omega⟩, hc.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (U.filter fun c => n ≤ c.val)
      (S ∪ seamSouthwestColumns (n := n) (m := m) (seamState p.1 p.2))
    have h3 := Finset.card_union_le S (seamSouthwestColumns (n := n) (m := m) (seamState p.1 p.2))
    have h4 : S.card ≤ 2 := Finset.card_le_two
    rw [seam_east_columns_card] at h1
    rw [seamSouthwestColumns_seamState_card] at h3
    omega

end OnLeConjecture.KnotFloer.GridFull
