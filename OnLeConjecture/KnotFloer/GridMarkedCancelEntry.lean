/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelReduce

/-!
# Sliding the marked arc from the closing arc into the core

Let `v = A η u` be a signed word whose first letter is `σ_0` and whose last letter is `σ_0⁻¹`.
The closing arc of `v`, leaving the last corner, is followed by the matching through the first
letter and then along the strand `0` through `A` (`SignedGrid.sM`, `reach_core`). It reaches the
first letter of `η` that touches the strand `follow 0 A`, at the corner whose incoming height is
that strand. Hence the marked word grids of `v` at the last corner are related to the marked word
grids of `v` at that corner of `η` (`mrelF_entry`). This is the slide of the protected block of
the written proof of Statement E (`statement_E_complete_proof.tex`, Section 8) from the closing
arc into the core of a factor.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid
  OnLeConjecture.KnotFloer.GridFull SignedAdjacentWord

variable {m : ℕ}

/-- The incoming heights of the three corners of a letter are distinct. -/
theorem corner_eq_of_xHeight2 (a : Fin (m - 1) × ℤˣ) {c c' : Fin 3}
    (h : signedXHeight2 a c = signedXHeight2 a c') : c = c' := by
  unfold signedXHeight2 at h
  split_ifs at h <;> fin_cases c <;> fin_cases c' <;> simp at h <;> rfl

/-- A letter touching a strand has a corner whose incoming height is that strand. -/
theorem exists_first_occ (η : SignedAdjacentWord m) {s : ℕ} (h : RankIn η s) :
    ∃ (i : ℕ) (hi : i < η.length), Occ η s ⟨i, hi⟩ ∧
      ∀ i' (hi' : i' < i), ¬ Occ η s ⟨i', by omega⟩ := by
  classical
  have hex : ∃ i, ∃ hi : i < η.length, Occ η s ⟨i, hi⟩ := by
    obtain ⟨k, hk, hk'⟩ := (rankIn_iff η s).mp h
    exact ⟨k, hk, by unfold Occ; simp only; omega⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun i' hi' hocc => ?_⟩
  exact Nat.find_min hex hi' ⟨_, hocc⟩

/-- **The entry slide.** -/
theorem mrelF_entry (A' η u : SignedAdjacentWord m) (a₀ : Fin (m - 1)) (ha₀ : a₀.val = 0)
    (u' : SignedAdjacentWord m) (hu : u = u' ++ [(a₀, -1)]) {i : ℕ} (hi : i < η.length)
    (hfirst : Occ η (follow 0 ((a₀, 1) :: A')) ⟨i, hi⟩ ∧
      ∀ i' (hi' : i' < i), ¬ Occ η (follow 0 ((a₀, 1) :: A')) ⟨i', by omega⟩) :
    ∃ c : Fin 3, η.xHeight2 (⟨i, hi⟩, c) = 2 * follow 0 ((a₀, 1) :: A') ∧
      MRelF ((a₀, 1) :: A' ++ η ++ u) ((((a₀, 1) :: A' ++ η ++ u).length - 1, 2))
        ((a₀, 1) :: A' ++ η ++ u) (A'.length + 1 + i, c) := by
  subst hu
  have hv0 : 0 < ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])).length := by simp
  -- the first and the last letters
  have hfst : ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)]))[0]'hv0 = (a₀, 1) := by simp
  have hlst : ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)]))[
      ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])).length - 1]'(by omega) = (a₀, -1) := by
    rw [← List.getLast_eq_getElem] <;> simp
  -- the closing arc reaches the middle corner of the first letter
  have h1 : sM ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)]))
      (⟨((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])).length - 1, by omega⟩, 2) =
      (⟨0, hv0⟩, 0) := by
    apply sM_eq_of_spec _ _ _ (show (2 : Fin 3) ≠ 0 by decide)
    · simp only [SignedAdjacentWord.xHeight2, SignedAdjacentWord.oHeight2]
      rw [hfst, hlst]
      simp [signedXHeight2, signedOHeight2, ha₀]
    · right
      refine ⟨Nat.zero_le _, fun k _ => ⟨Nat.zero_le _, ?_⟩⟩
      change k.val ≤ _ - 1
      have := k.isLt; omega
  have h2 := sM_middle ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])) ⟨0, hv0⟩
  -- the strand `0` through `A`
  have hs : SignedAdjacentWord.oHeight2 ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)]))
      (⟨0, hv0⟩, 2) = 2 * 1 := by
    simp only [SignedAdjacentWord.oHeight2]
    rw [hfst]
    simp [signedOHeight2, ha₀]
  have hfollow : follow 1 (((a₀, 1) :: A' : SignedAdjacentWord m).drop 1) =
      follow 0 ((a₀, 1) :: A') := by
    rw [List.drop_one, List.tail_cons, show ((a₀, 1) :: A' : SignedAdjacentWord m) =
      [(a₀, 1)] ++ A' from rfl, follow_append]
    congr 1
    simp [follow, swapAt, ha₀]
  obtain ⟨j, q, hj, hq1, hq2⟩ := reach_core ((a₀, 1) :: A') η (u' ++ [(a₀, -1)])
    (p := (⟨0, hv0⟩, 2)) (show (2 : Fin 3) ≠ 0 by decide) hs (h₀ := 1) (by simp) (by simp)
    (fun k hk hk' => by exfalso; simp only [Fin.lt_def] at hk; omega) hi
    (by rw [hfollow]; exact hfirst)
  rw [hfollow] at hq2
  refine ⟨q.2, ?_, ?_⟩
  · have e : SignedAdjacentWord.xHeight2 ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])) q =
        η.xHeight2 (⟨i, hi⟩, q.2) := by
      simp only [SignedAdjacentWord.xHeight2]
      congr 1
      have hq1' : q.1.val = ((a₀, 1) :: A').length + i := hq1
      simp only [hq1', List.append_assoc]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem_append_left hi]
    rw [← e, hq2]
  · have s1 := mrelF_slide ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)]))
      (⟨((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])).length - 1, by omega⟩, 2)
    have s2 := mrelF_slide ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])) (⟨0, hv0⟩, 0)
    have s3 := mrelF_slide_pow ((a₀, 1) :: A' ++ η ++ (u' ++ [(a₀, -1)])) (⟨0, hv0⟩, 2) j
    rw [h1] at s1
    rw [h2] at s2
    rw [hj] at s3
    refine (s1.trans (s2.trans s3)).cast rfl rfl rfl ?_
    have hq1' : q.1.val = ((a₀, 1) :: A').length + i := hq1
    rw [hq1']
    simp only [List.length_cons]

end OnLeConjecture.KnotTheory.MarkedCancel
