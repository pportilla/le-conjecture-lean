/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelChain
public import OnLeConjecture.KnotTheory.MarkedCancelOrbit
public import OnLeConjecture.KnotTheory.BraidMonodromyLayered

/-!
# Reduction of a marked conjugate to its core

Let `q = A η A⁻¹` be a signed word on `m` strands, where `A` uses every strand and `η` uses the
strands `0, …, a - 1`, and let the marked arc leave a corner of `η`. Then the marked word grids
of `q` are related by grid moves to marked word grids of `η` at the same corner, with a frame
tower of `m - a` blocks over the protected grid (`mrel_conj_core`).

The proof inserts the ladder `ρ' ρ'⁻¹`, with `ρ' = σ_{a-1} ⋯ σ_{m-2}`, after `η`
(`mrelF_pad_insert`), cancels `A` against `A⁻¹` letter by letter (`mrelF_conj_reduce`), and
removes the ladder from the inside, each step cancelling an inverse pair whose upper strand is no
longer used (`mrel_pad_remove`). This is the marked inverse cancellation of the written proof of
Statement E (`statement_E_complete_proof.tex`, Section 8) applied to one padded factor.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid
  OnLeConjecture.KnotFloer.GridFull SignedAdjacentWord

variable {m : ℕ}

/-! ### Letters of inverse words -/

theorem mem_inv_iff {w : SignedAdjacentWord m} {a : Fin (m - 1) × ℤˣ} :
    a ∈ inv w ↔ (a.1, -a.2) ∈ w := by
  simp only [inv, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩; simpa using hb
  · intro h; exact ⟨(a.1, -a.2), h, by simp⟩

theorem length_inv (w : SignedAdjacentWord m) : (inv w).length = w.length := by
  simp [inv]

/-! ### Ladders -/

/-- The ladder `σ_s σ_{s+1} ⋯ σ_{s+j-1}`. -/
def ladder (s : ℕ) : (j : ℕ) → s + j ≤ m - 1 → SignedAdjacentWord m
  | 0, _ => []
  | j + 1, h => ladder s j (by omega) ++ [(⟨s + j, by omega⟩, 1)]

theorem ladder_length (s : ℕ) : ∀ (j : ℕ) (h : s + j ≤ m - 1), (ladder s j h).length = j
  | 0, _ => rfl
  | j + 1, h => by simp [ladder, ladder_length s j]

theorem ladder_rank (s : ℕ) : ∀ (j : ℕ) (h : s + j ≤ m - 1), ∀ a ∈ ladder s j h,
    s ≤ a.1.val ∧ a.1.val < s + j
  | 0, _ => by simp [ladder]
  | j + 1, h => by
    intro a ha
    simp only [ladder, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have := ladder_rank s j (by omega) a ha; omega
    · simp

theorem ladder_rankIn (s : ℕ) : ∀ (j : ℕ) (h : s + j ≤ m - 1) (x : ℕ), s ≤ x → x ≤ s + j →
    0 < j → RankIn (ladder s j h) x
  | 0, _, _, _, _, hj => absurd hj (lt_irrefl 0)
  | j + 1, h, x, hx1, hx2, _ => by
    by_cases hx : x ≤ s + j ∧ 0 < j
    · exact (ladder_rankIn s j (by omega) x hx1 hx.1 hx.2).mono
        (fun a ha => List.mem_append_left _ ha)
    · refine ⟨(⟨s + j, by omega⟩, 1), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      simp only
      omega

theorem follow_ladder_zero : ∀ (j : ℕ) (h : 0 + j ≤ m - 1), follow 0 (ladder 0 j h) = j
  | 0, _ => rfl
  | j + 1, h => by
    rw [ladder, follow_concat, follow_ladder_zero j (by omega)]
    simp [swapAt]

/-! ### Cancellation of a conjugating word -/

/-- **Cancellation of a conjugating word.** If the strands of every letter of `A` are used by
`Z`, the marked word grids of `A Z A⁻¹` at a corner of `Z` are related to the marked word grids of
`Z` at the same corner. -/
theorem mrelF_conj_reduce (Z : SignedAdjacentWord m) {i : ℕ} (hi : i < Z.length) (c : Fin 3) :
    ∀ A : SignedAdjacentWord m, (∀ a ∈ A, RankIn Z a.1.val ∧ RankIn Z (a.1.val + 1)) →
      MRelF (A ++ Z ++ inv A) (A.length + i, c) Z (i, c)
  | [], _ => (MRelF.refl hi).cast (by simp) (by simp) rfl rfl
  | a :: A, hA => by
    have ih := mrelF_conj_reduce Z hi c A (fun b hb => hA b (List.mem_cons_of_mem _ hb))
    set T := A ++ Z ++ inv A with hT
    have hTZ : ∀ s, RankIn Z s → RankIn T s := fun s h =>
      h.mono (fun b hb => by rw [hT]; simp [hb])
    obtain ⟨h0, h1⟩ := hA a (List.mem_cons_self ..)
    have hlenT : T.length = A.length + Z.length + A.length := by
      rw [hT]; simp only [List.length_append, length_inv]
    have s1 := mrelF_rotate_left (a :: T) [(a.1, -a.2)] (h := A.length + 1 + i)
      (by simp only [List.length_cons]; omega) c
    have s2 := mrelF_cancel_front a.1 (-a.2) T (hTZ _ h0) (hTZ _ h1) (i := A.length + i)
      (by omega) c
    refine (s1.cast ?_ ?_ ?_ ?_).trans (s2.trans ih)
    · rw [inv_cons]; simp [hT]
    · simp only [List.length_cons]
    · simp
    · simp only [List.length_cons, List.length_nil, Prod.mk.injEq, and_true]; omega

/-! ### Insertion and removal of a ladder -/

/-- **Insertion of a ladder** after the core, when `A` uses every strand. -/
theorem mrelF_pad_insert (A η : SignedAdjacentWord m) (s : ℕ)
    (hA : ∀ x, x ≤ m - 1 → RankIn A x) {i : ℕ} (hi : i < η.length) (c : Fin 3) :
    ∀ (j : ℕ) (hj : s + j ≤ m - 1), MRelF (A ++ η ++ inv A) (A.length + i, c)
      (A ++ (η ++ ladder s j hj ++ inv (ladder s j hj)) ++ inv A) (A.length + i, c)
  | 0, _ => (MRelF.refl (by simp; omega)).cast rfl rfl (by simp [ladder]) rfl
  | j + 1, hj => by
    have ih := mrelF_pad_insert A η s hA hi c j (by omega)
    set L' : SignedAdjacentWord m := ladder s j (by omega) with hL'
    set r : Fin (m - 1) := ⟨s + j, by omega⟩ with hr
    have hA' : ∀ x, x ≤ m - 1 → RankIn ((A ++ η ++ L') ++ (inv L' ++ inv A)) x := fun x hx =>
      (hA x hx).mono (fun b hb => by simp [hb])
    have s1 := mrelF_insert_mid (A ++ η ++ L') (inv L' ++ inv A) r 1 (hA' _ (by omega))
      (hA' _ (by omega)) (i := A.length + i) (by simp only [List.length_append]; omega) c
    refine ih.trans (s1.cast (by simp) rfl ?_ rfl)
    change _ = A ++ (η ++ (L' ++ [(r, 1)]) ++ inv (L' ++ [(r, 1)])) ++ inv A
    rw [inv_append]
    simp [inv]

/-- **Removal of a ladder** from the inside: each step cancels an inverse pair whose upper strand
is not used by the rest of the word, and adds one block to the protected grid. -/
theorem mrel_pad_remove (η : SignedAdjacentWord m) (s : ℕ) (hη : ∀ a ∈ η, a.1.val < s)
    (hηs : RankIn η s) {i : ℕ} (hi : i < η.length) (c : Fin 3) :
    ∀ (j : ℕ) (hj : s + j ≤ m - 1),
      MRel (η ++ ladder s j hj ++ inv (ladder s j hj)) (i, c) η (i, c) j
  | 0, _ => (MRelF.refl hi).toMRel.cast (by simp [ladder]) rfl rfl rfl rfl
  | j + 1, hj => by
    have ih := mrel_pad_remove η s hη hηs hi c j (by omega)
    set L' : SignedAdjacentWord m := ladder s j (by omega) with hL'
    set r : Fin (m - 1) := ⟨s + j, by omega⟩ with hr
    have hlenL : L'.length = j := ladder_length s j _
    have hrankL := ladder_rank (m := m) s j (by omega)
    set T := inv L' ++ (η ++ L') with hT
    have h0 : RankIn T (s + j) := by
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · exact hηs.mono (fun b hb => by rw [hT]; simp [hb])
      · exact (ladder_rankIn s j (by omega) (s + j) (by omega) le_rfl hjp).mono
          (fun b hb => by rw [hT]; simp only [List.mem_append]; right; right; exact hb)
    have h1 : ¬ RankIn T (s + j + 1) := by
      rintro ⟨b, hb, hb'⟩
      rw [hT, List.mem_append, List.mem_append, mem_inv_iff] at hb
      rcases hb with hb | hb | hb
      · have := hrankL _ hb; simp only at this; omega
      · have := hη b hb; omega
      · have := hrankL b hb; omega
    have s1 := mrelF_rotate_left (η ++ L') ([(r, 1), (r, -1)] ++ inv L') (h := i)
      (by simp only [List.length_append]; omega) c
    have s2 := mrel_cancel_unused r T h0 h1 (i := i + j)
      (by rw [hT]; simp [length_inv, hlenL]; omega) c
    have s3 := mrelF_rotate_right (inv L') (η ++ L') (h := i + j) (by simp [length_inv, hlenL])
      (by simp [length_inv, hlenL]; omega) c
    have hw : η ++ ladder s (j + 1) hj ++ inv (ladder s (j + 1) hj) =
        (η ++ L') ++ ([(r, 1), (r, -1)] ++ inv L') := by
      change η ++ (L' ++ [(r, 1)]) ++ inv (L' ++ [(r, 1)]) = _
      rw [inv_append]
      simp [inv]
    refine ((((s1.toMRel).cast hw.symm rfl ?_ ?_ rfl).trans s2).trans
      ((s3.toMRel).cast rfl rfl rfl ?_ rfl)).trans ih |>.cast rfl rfl rfl rfl (by omega)
    · simp [hT]
    · simp only [List.length_append, List.length_cons, List.length_nil, length_inv, hlenL,
        Prod.mk.injEq, and_true]; omega
    · simp only [length_inv, hlenL, Prod.mk.injEq, and_true]; omega

/-! ### The core of a conjugate -/

/-- **The core of a marked conjugate.** If `A` uses every strand, `η` uses the strands below `a`
and every letter of `η` lies below `a`, then marked word grids of `A η A⁻¹` at a corner of `η`
are related to marked word grids of `η` at the same corner, with `m - a` blocks. -/
theorem mrel_conj_core (A η : SignedAdjacentWord m) {a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m)
    (hA : ∀ x, x ≤ m - 1 → RankIn A x) (hη : ∀ b ∈ η, b.1.val + 2 ≤ a)
    (hηr : ∀ x, x < a → RankIn η x) {i : ℕ} (hi : i < η.length) (c : Fin 3) :
    MRel (A ++ η ++ inv A) (A.length + i, c) η (i, c) (m - a) := by
  have hj : a - 1 + (m - a) ≤ m - 1 := by omega
  set L := ladder (a - 1) (m - a) hj with hL
  set Z := η ++ L ++ inv L with hZ
  have hZall : ∀ x, x ≤ m - 1 → RankIn Z x := by
    intro x hx
    by_cases hxa : x < a
    · exact (hηr x hxa).mono (fun b hb => by rw [hZ]; simp only [List.mem_append]; tauto)
    · exact (ladder_rankIn (a - 1) (m - a) hj x (by omega) (by omega) (by omega)).mono
        (fun b hb => by rw [hZ]; simp only [List.mem_append]; tauto)
  have s1 := mrelF_pad_insert A η (a - 1) hA hi c (m - a) hj
  have s2 := mrelF_conj_reduce Z (i := i) (by rw [hZ]; simp only [List.length_append]; omega) c A
    (fun b _ =>
    ⟨hZall _ (by omega), hZall _ (by omega)⟩)
  have s3 := mrel_pad_remove η (a - 1) (fun b hb => by have := hη b hb; omega)
    (hηr _ (by omega)) hi c (m - a) hj
  have := (s1.trans (s2.cast (by rw [hZ]) rfl rfl rfl)).toMRel.trans s3
  exact this.cast rfl rfl rfl rfl (Nat.zero_add _)

end OnLeConjecture.KnotTheory.MarkedCancel
