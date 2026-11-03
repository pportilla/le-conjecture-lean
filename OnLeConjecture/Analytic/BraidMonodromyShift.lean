/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyGrid
public import OnLeConjecture.Analytic.BraidMonodromyFactorization

/-!
# Shifted positive words are conjugates of lifted words

In the local factors of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`, subsection "Local factors, without a generic-Morse
projection") the sheets of a local cluster occupy consecutive positions `p, …, p + a - 1` in the
real-coordinate order of the `S` sheets. Its local word is therefore a positive word `w` on `a`
strands placed on these positions (`shiftPositive p w`). The event factorization uses the same
word placed on the first `a` strands (`liftPositiveWord`). This module proves that the two are
conjugate by an explicit finite derivation.

* `ascRun S lo len`: the ascending run `σ_lo σ_{lo+1} ⋯ σ_{lo+len-1}`.
* `ascRun_append_letter`: `σ_0 ⋯ σ_{S-2}` conjugates `σ_k` to `σ_{k+1}` for `k + 1 ≤ S - 3`, by far
  commutation and one positive braid relation.
* `exists_shiftPositive_equiv_conjugate`: `shiftPositive p w ≡ c (liftPositiveWord w) c⁻¹` for some
  signed word `c`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

/-- A positive word on `a` strands placed on the strands `p, …, p + a - 1` of `S ≥ p + a`
strands. -/
def shiftPositive {a S : ℕ} (p : ℕ) (h : p + a ≤ S) (w : PositiveAdjacentWord a) :
    PositiveAdjacentWord S :=
  w.map fun i => ⟨i.val + p, by have := i.isLt; omega⟩

theorem length_shiftPositive {a S : ℕ} (p : ℕ) (h : p + a ≤ S) (w : PositiveAdjacentWord a) :
    (shiftPositive p h w).length = w.length := by
  simp [shiftPositive]

/-- The ascending run `σ_lo σ_{lo+1} ⋯ σ_{lo+len-1}` (letters at least `S - 1` are omitted). -/
def ascRun (S : ℕ) : ℕ → ℕ → SignedAdjacentWord S
  | _, 0 => []
  | lo, len + 1 => (if h : lo < S - 1 then [(⟨lo, h⟩, 1)] else []) ++ ascRun S (lo + 1) len

theorem ascRun_add (S : ℕ) : ∀ (lo l₁ l₂ : ℕ),
    ascRun S lo (l₁ + l₂) = ascRun S lo l₁ ++ ascRun S (lo + l₁) l₂
  | lo, 0, l₂ => by simp [ascRun]
  | lo, l₁ + 1, l₂ => by
    rw [show l₁ + 1 + l₂ = (l₁ + l₂) + 1 by omega, ascRun, ascRun, ascRun_add S (lo + 1) l₁ l₂,
      List.append_assoc, show lo + 1 + l₁ = lo + (l₁ + 1) by omega]

theorem mem_ascRun {S : ℕ} : ∀ {lo len : ℕ} {b : Fin (S - 1) × ℤˣ}, b ∈ ascRun S lo len →
    lo ≤ b.1.val ∧ b.1.val < lo + len
  | _, 0, _, hb => by simp [ascRun] at hb
  | lo, len + 1, b, hb => by
    rw [ascRun] at hb
    rcases List.mem_append.mp hb with hb | hb
    · split_ifs at hb with h
      · simp only [List.mem_singleton] at hb; subst hb; simp
      · simp at hb
    · have := mem_ascRun hb; omega

theorem ascRun_two {S : ℕ} (k k' : Fin (S - 1)) (hk : k'.val = k.val + 1) :
    ascRun S k.val 2 = [(k, 1), (k', 1)] := by
  have h1 : k.val + 1 < S - 1 := hk ▸ k'.isLt
  have hk' : (⟨k.val + 1, h1⟩ : Fin (S - 1)) = k' := Fin.ext hk.symm
  rw [ascRun, ascRun, ascRun, dif_pos k.isLt, dif_pos h1, hk']
  simp

/-- **The ascending run conjugates `σ_k` to `σ_{k+1}`.** If `lo ≤ k` and `k + 2 ≤ lo + len`, then
`ascRun lo len · σ_k ≡ σ_{k+1} · ascRun lo len`. -/
theorem ascRun_append_letter {S : ℕ} (lo len : ℕ) (k k' : Fin (S - 1))
    (hk : k'.val = k.val + 1) (hlo : lo ≤ k.val) (hlen : k.val + 2 ≤ lo + len) :
    SignedBraidEquiv (ascRun S lo len ++ [(k, 1)]) ((k', 1) :: ascRun S lo len) := by
  have hsplit : ascRun S lo len = ascRun S lo (k.val - lo) ++
      ([(k, 1), (k', 1)] ++ ascRun S (k.val + 2) (len - (k.val - lo) - 2)) := by
    have hl : len = (k.val - lo) + (2 + (len - (k.val - lo) - 2)) := by omega
    conv_lhs => rw [hl]
    rw [ascRun_add, ascRun_add, show lo + (k.val - lo) = k.val by omega, ascRun_two k k' hk]
  rw [hsplit]
  set A := ascRun S lo (k.val - lo)
  set B := ascRun S (k.val + 2) (len - (k.val - lo) - 2)
  -- `σ_k` commutes with the letters of `B`, which are at least `k + 2`.
  have hB : SignedBraidEquiv (B ++ [(k, 1)]) ((k, 1) :: B) :=
    (SignedBraidEquiv.far_past (k, 1) B fun b hb => Or.inl (mem_ascRun hb).1).symm
  -- `σ_{k+1}` commutes with the letters of `A`, which are at most `k - 1`.
  have hA : SignedBraidEquiv (A ++ [(k', 1)]) ((k', 1) :: A) :=
    (SignedBraidEquiv.far_past (k', 1) A fun b hb => Or.inr (by
      have := (mem_ascRun hb).2
      change b.1.val + 2 ≤ k'.val
      omega)).symm
  have s1 : SignedBraidEquiv (A ++ ([(k, 1), (k', 1)] ++ B) ++ [(k, 1)])
      (A ++ ([(k, 1), (k', 1), (k, 1)] ++ B)) := by
    have := (hB.append_left (A ++ [(k, 1), (k', 1)]))
    simpa [List.append_assoc] using this
  have s2 : SignedBraidEquiv (A ++ ([(k, 1), (k', 1), (k, 1)] ++ B))
      (A ++ ([(k', 1), (k, 1), (k', 1)] ++ B)) :=
    ((SignedBraidEquiv.braid_pos k k' hk).append_right B).append_left A
  have s3 : SignedBraidEquiv (A ++ ([(k', 1), (k, 1), (k', 1)] ++ B))
      ((k', 1) :: (A ++ ([(k, 1), (k', 1)] ++ B))) := by
    have := hA.append_right ([(k, 1), (k', 1)] ++ B)
    simpa [List.append_assoc] using this
  exact s1.trans (s2.trans s3)

theorem conjugateWord_congr {S : ℕ} (c : SignedAdjacentWord S) {x y : SignedAdjacentWord S}
    (h : SignedBraidEquiv x y) : SignedBraidEquiv (conjugateWord c x) (conjugateWord c y) :=
  ((SignedBraidEquiv.refl c).append h).append (SignedBraidEquiv.refl _)

/-- Shifting a positive word by one position is conjugation by `σ_0 ⋯ σ_{S-2}`. -/
theorem shiftPositive_succ_equiv {a S : ℕ} (p : ℕ) (h : p + 1 + a ≤ S) :
    ∀ w : PositiveAdjacentWord a,
      SignedBraidEquiv (shiftPositive (p + 1) h w).toSigned
        (conjugateWord (ascRun S 0 (S - 1)) (shiftPositive p (by omega) w).toSigned)
  | [] => by
    simpa [shiftPositive, PositiveAdjacentWord.toSigned, conjugateWord] using
      (SignedBraidEquiv.append_inv_self (ascRun S 0 (S - 1))).symm
  | i :: w => by
    set C := ascRun S 0 (S - 1)
    have ih := shiftPositive_succ_equiv p h w
    have hi := i.isLt
    have hk1 : i.val + p < S - 1 := by omega
    have hk2 : i.val + (p + 1) < S - 1 := by omega
    set k : Fin (S - 1) := ⟨i.val + p, hk1⟩
    set k' : Fin (S - 1) := ⟨i.val + (p + 1), hk2⟩
    have hletter : SignedBraidEquiv [(k', 1)] (conjugateWord C [(k, 1)]) := by
      have h1 := ascRun_append_letter (S := S) 0 (S - 1) k k' (by simp [k, k']; omega)
        (Nat.zero_le _) (by simp [k]; omega)
      have h2 := h1.append_right (inv C)
      have h3 : SignedBraidEquiv ((k', 1) :: C ++ inv C) [(k', 1)] := by
        simpa using SignedBraidEquiv.cancel_inv_mid [(k', 1)] C []
      simpa [conjugateWord, List.append_assoc] using (h2.trans h3).symm
    have e1 : (shiftPositive (p + 1) h (i :: w)).toSigned =
        [(k', 1)] ++ (shiftPositive (p + 1) h w).toSigned := rfl
    have e2 : (shiftPositive p (by omega) (i :: w)).toSigned =
        [(k, 1)] ++ (shiftPositive p (by omega) w).toSigned := rfl
    rw [e1, e2]
    exact (hletter.append ih).trans (conjugateWord_append C _ _).symm

/-- **Shifted words are conjugates of lifted words.** A positive word on `a` strands placed on
the strands `p, …, p + a - 1` is conjugate, by an explicit finite derivation, to the same word
placed on the first `a` strands. -/
theorem exists_shiftPositive_equiv_conjugate {a S : ℕ} :
    ∀ (p : ℕ) (h : p + a ≤ S) (w : PositiveAdjacentWord a), ∃ c : SignedAdjacentWord S,
      SignedBraidEquiv (shiftPositive p h w).toSigned
        (conjugateWord c (liftPositiveWord (by omega : a ≤ S) w))
  | 0, h, w => by
    refine ⟨[], SignedBraidEquiv.of_eq ?_⟩
    simp only [conjugateWord, inv_nil, List.nil_append, List.append_nil]
    simp only [shiftPositive, PositiveAdjacentWord.toSigned, liftPositiveWord, List.map_map]
    rfl
  | p + 1, h, w => by
    obtain ⟨c, hc⟩ := exists_shiftPositive_equiv_conjugate (a := a) (S := S) p (by omega) w
    refine ⟨ascRun S 0 (S - 1) ++ c, (shiftPositive_succ_equiv p h w).trans ?_⟩
    rw [← conjugateWord_conjugateWord]
    exact conjugateWord_congr _ hc

end OnLeConjecture.Analytic
