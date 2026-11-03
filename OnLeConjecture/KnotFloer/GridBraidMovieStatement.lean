/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalClass
public import OnLeConjecture.KnotTheory.PositiveWordNormalForms

/-!
# Statement of the braid grid movie

This module states the braid part of the native route (stage 1 of job J12).
For a positive word `w` on `S ≥ 2` strands with `b` permutation cycles, the
statement asks for a native chain map from the reflected torus grid of size
`2S + 1` to the selected grid of the word `Δ² w`, with Maslov shift zero,
Alexander shift `(|w| - (S - b) + (b - 1)) / 2`, carrying the anchor class to the
normalized canonical class. The proof is the content of stage 2.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex OnLeConjecture.KnotTheory

/-- The selected grid of a word with a full-twist prefix on at least two strands has size
at least two. -/
theorem two_le_wordGrid_size_fullTwist {S : ℕ} (hS : 2 ≤ S) (w : PositiveAdjacentWord S) :
    2 ≤ (fullTwistWord S ++ w).length * 3 := by
  rw [List.length_append, fullTwistWord, torusWord_length]
  have h1 : 1 ≤ S * (S - 1) := Nat.one_le_iff_ne_zero.mpr (by
    apply Nat.mul_ne_zero <;> omega)
  omega

/-- **Braid native map statement.** For every positive word `w` on `S ≥ 2` strands there
is a native chain map from the reflected torus grid to the selected grid of `Δ² w`, with
shifts `(0, (|w| - (S - b) + (b - 1)) / 2)` where `b` is the number of permutation cycles of
`w`, carrying the anchor class to the normalized canonical class. -/
def BraidNativeMapStatement : Prop :=
  ∀ (S : ℕ) (hS : 2 ≤ S) (w : PositiveAdjacentWord S),
    ∃ φ : laurentMaslovComplex (reflectedTorusGrid (S - 1)) (ZMod 2) ⟶
        laurentMaslovComplex (wordGrid (fullTwistWord S ++ w)) (ZMod 2),
      (laurentMaslovBifiltration (reflectedTorusGrid (S - 1)) (ZMod 2)).Shifts
          (laurentMaslovBifiltration (wordGrid (fullTwistWord S ++ w)) (ZMod 2)) φ 0
          (((w.length : ℝ) - ((S : ℝ) - w.toSigned.cycleCount) +
            ((w.toSigned.cycleCount : ℝ) - 1)) / 2) ∧
        homologyMap φ 0 (reflectedTorusAnchorClass (S - 1) (ZMod 2)) =
          gridCanonicalClass (wordGrid (fullTwistWord S ++ w))
            (two_le_wordGrid_size_fullTwist hS w)

end OnLeConjecture.KnotFloer.GridFull
