/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.BraidMonodromyLayered

/-!
# Conjugates of the first generator

This module contains the word combinatorics that turns local factors into the factors of an
event factorization (Section 3 of the written proof of Statement E,
`statement-E-complete-proof.tex`, subsection "Local factors, without a generic-Morse
projection").

* `SignedBraidConj.exists_conjugator`: a conjugacy derivation is a conjugation, that is,
  `u ∼ v` gives a word `x` with `u ≡ x v x⁻¹`.
* `exists_letter_equiv_conjugate_first`: every positive letter `σ_i` is equivalent to a
  conjugate `c σ_0 c⁻¹` of the first generator, by `σ_{i+1} = (σ_i σ_{i+1}) σ_i (σ_i σ_{i+1})⁻¹`.
* `exists_conjugate_positive_equiv_flatten`: a conjugate `x w x⁻¹` of a positive word `w` is
  equivalent to a product of `length w` conjugates of `σ_0`.

In the written proof an ordinary ramification of order `d` contributes `d - 1` positive single
generators: its local word is a positive word with `d - 1` letters, and the last lemma splits its
conjugate into `d - 1` conjugates of `σ_0`.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory

open SignedAdjacentWord

variable {m : ℕ}

/-- **Conjugacy derivations are conjugations.** -/
theorem SignedBraidConj.exists_conjugator {u v : SignedAdjacentWord m} (h : SignedBraidConj u v) :
    ∃ x, SignedBraidEquiv u (x ++ v ++ inv x) := by
  induction h with
  | rel u v h =>
    cases h with
    | step h => exact ⟨[], by simpa using SignedBraidEquiv.of_step h⟩
    | rotate w a =>
      refine ⟨[(a.1, -a.2)], ?_⟩
      have h1 := SignedBraidEquiv.cancel_front' a.1 a.2 (w ++ [a])
      simpa [List.append_assoc] using h1.symm
  | refl u => exact ⟨[], by simpa using SignedBraidEquiv.refl u⟩
  | symm u v _ ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨inv x, ?_⟩
    have h1 := ((hx.append_left (inv x)).append_right x)
    have h2 : SignedBraidEquiv (inv x ++ (x ++ v ++ inv x) ++ x) v := by
      have := SignedBraidEquiv.cancel_inv_mid' [] x (v ++ inv x ++ x)
      have h3 := SignedBraidEquiv.cancel_inv_mid' v x []
      simp only [List.nil_append, List.append_nil, List.append_assoc] at this h3 ⊢
      exact this.trans h3
    rw [inv_inv]
    exact (h1.trans h2).symm
  | trans u v w _ _ ih₁ ih₂ =>
    obtain ⟨x, hx⟩ := ih₁
    obtain ⟨y, hy⟩ := ih₂
    refine ⟨x ++ y, ?_⟩
    have := (hy.append_left x).append_right (inv x)
    refine hx.trans (this.trans (SignedBraidEquiv.of_eq ?_))
    rw [inv_append]
    simp [List.append_assoc]

/-- The first generator `σ_0` on `m ≥ 2` strands, as a signed word. -/
def firstLetterWord (hm : 2 ≤ m) : SignedAdjacentWord m := [(⟨0, by omega⟩, 1)]

/-- The relation `σ_{i+1} = (σ_i σ_{i+1}) σ_i (σ_i σ_{i+1})⁻¹`. -/
theorem letter_succ_equiv_conjugate (a b : Fin (m - 1)) (h : b.val = a.val + 1) :
    SignedBraidEquiv [(b, 1)] ([(a, 1), (b, 1)] ++ [(a, 1)] ++ inv [(a, 1), (b, 1)]) := by
  have h1 : SignedBraidEquiv ([(a, 1), (b, 1)] ++ [(a, 1)] ++ inv [(a, 1), (b, 1)])
      ([(b, 1), (a, 1), (b, 1)] ++ [(b, -1), (a, -1)]) := by
    have := (SignedBraidEquiv.braid_pos a b h).append_right [(b, -1), (a, -1)]
    simpa [inv] using this
  have h2 : SignedBraidEquiv ([(b, 1), (a, 1), (b, 1)] ++ [(b, -1), (a, -1)]) [(b, 1)] := by
    have c1 := SignedBraidEquiv.cancel_mid [(b, 1), (a, 1)] [(a, -1)] b 1
    have c2 := SignedBraidEquiv.cancel_mid [(b, 1)] [] a 1
    simp only [List.append_nil] at c1 c2
    simpa using c1.trans c2
  exact (h1.trans h2).symm

/-- **Every positive letter is a conjugate of the first generator.** -/
theorem exists_letter_equiv_conjugate_first (hm : 2 ≤ m) (i : Fin (m - 1)) :
    ∃ c : SignedAdjacentWord m,
      SignedBraidEquiv [(i, 1)] (c ++ firstLetterWord hm ++ inv c) := by
  suffices ∀ k (hk : k < m - 1), ∃ c : SignedAdjacentWord m,
      SignedBraidEquiv [(⟨k, hk⟩, 1)] (c ++ firstLetterWord hm ++ inv c) from this i.val i.isLt
  intro k
  induction k with
  | zero => intro hk; exact ⟨[], by simpa [firstLetterWord] using SignedBraidEquiv.refl _⟩
  | succ k ih =>
    intro hk
    obtain ⟨c, hc⟩ := ih (by omega)
    set a : Fin (m - 1) := ⟨k, by omega⟩
    set b : Fin (m - 1) := ⟨k + 1, hk⟩
    have h1 := letter_succ_equiv_conjugate a b rfl
    refine ⟨[(a, 1), (b, 1)] ++ c, h1.trans ?_⟩
    have h2 := (hc.append_left [(a, 1), (b, 1)]).append_right (inv [(a, 1), (b, 1)])
    refine h2.trans (SignedBraidEquiv.of_eq ?_)
    rw [inv_append]
    simp [List.append_assoc]

/-- **A conjugate of a positive word is a product of conjugates of `σ_0`.** For a positive word
`w` and any word `x`, there are words `c₁, …, c_{|w|}` with
`x w x⁻¹ ≡ (c₁ σ_0 c₁⁻¹) ⋯ (c_{|w|} σ_0 c_{|w|}⁻¹)`. -/
theorem exists_conjugate_positive_equiv_flatten (hm : 2 ≤ m) (x : SignedAdjacentWord m)
    (w : PositiveAdjacentWord m) :
    ∃ cs : List (SignedAdjacentWord m), cs.length = w.length ∧
      SignedBraidEquiv (x ++ w.toSigned ++ inv x)
        (cs.map fun c => conjugateWord c (firstLetterWord hm)).flatten := by
  induction w with
  | nil =>
    refine ⟨[], rfl, ?_⟩
    simpa [PositiveAdjacentWord.toSigned] using SignedBraidEquiv.append_inv_self x
  | cons i w ih =>
    obtain ⟨cs, hlen, hcs⟩ := ih
    obtain ⟨c, hc⟩ := exists_letter_equiv_conjugate_first hm i
    refine ⟨(x ++ c) :: cs, by simp [hlen], ?_⟩
    -- Split `x σ_i w x⁻¹` as `(x σ_i x⁻¹)(x w x⁻¹)`.
    have hsplit : SignedBraidEquiv (x ++ PositiveAdjacentWord.toSigned (i :: w) ++ inv x)
        ((x ++ [(i, 1)] ++ inv x) ++ (x ++ PositiveAdjacentWord.toSigned w ++ inv x)) := by
      have := SignedBraidEquiv.cancel_inv_mid' (x ++ [(i, 1)]) x
        (PositiveAdjacentWord.toSigned w ++ inv x)
      simp only [PositiveAdjacentWord.toSigned, List.map_cons, List.append_assoc,
        List.cons_append] at this ⊢
      exact this.symm
    have hfirst : SignedBraidEquiv (x ++ [(i, 1)] ++ inv x)
        (conjugateWord (x ++ c) (firstLetterWord hm)) := by
      have := (hc.append_left x).append_right (inv x)
      refine this.trans (SignedBraidEquiv.of_eq ?_)
      rw [conjugateWord, inv_append]
      simp [List.append_assoc]
    exact hsplit.trans ((hfirst.append hcs).trans (SignedBraidEquiv.of_eq rfl))

end OnLeConjecture.KnotTheory
