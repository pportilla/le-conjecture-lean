/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesTransport
public import OnLeConjecture.KnotTheory.PositiveWordCoxeterConjugacy

/-! # Positive word conjugacy as grid moves

This module assembles record M413 of the dependency audit from the three kinds of generators of
`PositiveWordConj`.

* Rotations and far commutations are proved in `PositiveWordGridMovesTransport.lean`
  (`wordGrid_movesTo_rotate`, `wordGrid_movesTo_far`).
* `wordGrid_movesTo_of_conj_of_braid`: if the selected grids of the two sides of every positive
  braid relation inside a word are related by grid moves, then the selected grids of any two
  words related by `PositiveWordConj` are related by grid moves. The braid relation itself is the
  input `hbraid`; its proof (`docs/route-n/J09-word-grid-moves.tex`, Section 5) is not formalized
  here, so this statement is conditional on `hbraid`.
* `wordGrid_movesTo_of_farRotationEquiv`, `wordGrid_torusWord_movesTo_pow`: far commutations and
  rotations of a word `γ` give grid moves between the selected grids of the powers `γ^q`. In
  particular the selected grids of `δ^q` and `β^q`, for the Coxeter word `δ` and any permutation
  `β` of it, are related by grid moves. These results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-- **Record M413, conditional on the braid relation.** -/
theorem wordGrid_movesTo_of_conj_of_braid {m : ℕ}
    (hbraid : ∀ (u v : PositiveAdjacentWord m) (i j : Fin (m - 1)), j.val = i.val + 1 →
      (wordGrid (u ++ [i, j, i] ++ v)).MovesTo (wordGrid (u ++ [j, i, j] ++ v)))
    {u v : PositiveAdjacentWord m} (h : PositiveWordConj u v) :
    (wordGrid u).MovesTo (wordGrid v) := by
  induction h with
  | cyclic u i => exact wordGrid_movesTo_rotate u i
  | far u v i j hij => exact wordGrid_movesTo_far u v i j hij
  | braid u v i j hij => exact hbraid u v i j hij
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The `q`-th power of a word, as a flattened list. -/
def wordPow {m : ℕ} (γ : PositiveAdjacentWord m) (q : ℕ) : PositiveAdjacentWord m :=
  (List.replicate q γ).flatten

theorem wordPow_succ {m : ℕ} (γ : PositiveAdjacentWord m) (q : ℕ) :
    wordPow γ (q + 1) = wordPow γ q ++ γ := by
  simp [wordPow, List.replicate_succ', List.flatten_append]

theorem torusWord_eq_wordPow (m q : ℕ) : torusWord m q = wordPow (coxeterWord m) q := rfl

/-- A far commutation inside every factor of a power is a sequence of grid moves. -/
theorem wordGrid_movesTo_pow_far {m : ℕ} (x y : PositiveAdjacentWord m) (a b : Fin (m - 1))
    (hab : a.val + 2 ≤ b.val ∨ b.val + 2 ≤ a.val) :
    ∀ (q : ℕ) (s : PositiveAdjacentWord m),
      (wordGrid (wordPow (x ++ a :: b :: y) q ++ s)).MovesTo
        (wordGrid (wordPow (x ++ b :: a :: y) q ++ s)) := by
  intro q
  induction q with
  | zero => intro s; exact GridDiagram.MovesTo.refl _
  | succ q ih =>
    intro s
    rw [wordPow_succ, wordPow_succ]
    have h1 := wordGrid_movesTo_far (wordPow (x ++ a :: b :: y) q ++ x) (y ++ s) a b hab
    have e1 : wordPow (x ++ a :: b :: y) q ++ (x ++ a :: b :: y) ++ s =
        wordPow (x ++ a :: b :: y) q ++ x ++ a :: b :: (y ++ s) := by simp
    have e2 : wordPow (x ++ a :: b :: y) q ++ x ++ b :: a :: (y ++ s) =
        wordPow (x ++ a :: b :: y) q ++ (x ++ b :: a :: (y ++ s)) := by simp
    have e3 : wordPow (x ++ b :: a :: y) q ++ (x ++ b :: a :: (y ++ s)) =
        wordPow (x ++ b :: a :: y) q ++ (x ++ b :: a :: y) ++ s := by simp
    rw [e1]
    refine h1.trans ?_
    rw [e2, ← e3]
    exact ih (x ++ b :: a :: (y ++ s))

theorem wordPow_rotate {m : ℕ} (x : PositiveAdjacentWord m) (c : Fin (m - 1)) (q : ℕ) :
    wordPow (x ++ [c]) (q + 1) = (wordPow (x ++ [c]) q ++ x) ++ [c] ∧
      c :: (wordPow (x ++ [c]) q ++ x) = wordPow (c :: x) (q + 1) := by
  constructor
  · rw [wordPow_succ]; simp
  · induction q with
    | zero => simp [wordPow]
    | succ q ih =>
      rw [wordPow_succ (c :: x) (q + 1), ← ih, wordPow_succ]
      simp

/-- A far commutation or a rotation of `γ` gives grid moves between the grids of the powers. -/
theorem wordGrid_movesTo_pow_of_step {m : ℕ} {γ γ' : PositiveAdjacentWord m}
    (h : FarRotationStep γ γ') (q : ℕ) :
    (wordGrid (wordPow γ q)).MovesTo (wordGrid (wordPow γ' q)) := by
  cases h with
  | far x y a b hab =>
    have := wordGrid_movesTo_pow_far x y a b hab q []
    rwa [List.append_nil, List.append_nil] at this
  | rotate x c =>
    cases q with
    | zero => exact GridDiagram.MovesTo.refl _
    | succ q =>
      obtain ⟨h1, h2⟩ := wordPow_rotate x c q
      rw [h1, ← h2]
      exact wordGrid_movesTo_rotate _ c

/-- **Far rotation equivalence and powers.** -/
theorem wordGrid_movesTo_of_farRotationEquiv {m : ℕ} {γ γ' : PositiveAdjacentWord m}
    (h : FarRotationEquiv γ γ') (q : ℕ) :
    (wordGrid (wordPow γ q)).MovesTo (wordGrid (wordPow γ' q)) := by
  induction h with
  | rel _ _ h => exact wordGrid_movesTo_pow_of_step h q
  | refl => exact GridDiagram.MovesTo.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The selected grid of `δ^q` is related to the selected grid of `γ^q` for every permutation `γ`
of the Coxeter word `δ`. -/
theorem wordGrid_torusWord_movesTo_pow {m : ℕ} (γ : PositiveAdjacentWord m)
    (hγ : γ.Perm (List.finRange (m - 1))) (q : ℕ) :
    (wordGrid (torusWord m q)).MovesTo (wordGrid (wordPow γ q)) :=
  (wordGrid_movesTo_of_farRotationEquiv (farRotationEquiv_coxeterWord γ hγ) q).symm

end OnLeConjecture.KnotTheory
