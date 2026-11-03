/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ExteriorSignedWordGrid
public import OnLeConjecture.KnotFloer.GridConnectedSumIterated
public import OnLeConjecture.KnotFloer.GridCanonicalClass

/-!
# The scissor and cleanup statement of the proof of Statement E

`ScissorCleanupStatement` is the grid-theoretic core of the written proof of Statement E
(`statement_E_complete_proof.tex`, Sections 4 to 6 and 8 to 12): for a normalized factorization on
`S` strands, in which strand `0` lies in the nontrivial cycle of every factor and the factor
permutations act transitively, there are prepared factor grids `D_j`, related by grid moves to the
selected word grids of the local words, and a native map from every signed word grid of the
padded product to the iterated seam grid of the `D_j`, with shifts `(0, (s - U)/2)` and
canonical-class identity. Here `s - U = Σ_l a_l - r - S + 1`
(`NormalizedFactorization.scissorShiftCount`).

The written proof constructs the map as the composite of the star scissors (adjacent-row X
identities and selected row O switches), the cleanup by cyclic seam exposures, marked inverse
cancellations and four-mark collapses, the auxiliary contractions, and the removal of the simple
factors. The statement is not proved here.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex OnLeConjecture.KnotTheory

/-- **Scissors and cleanup.** For a normalized factorization in which strand `0` lies in every
factor cycle and the factor permutations are transitive, there are prepared factor grids and a
native map from every signed word grid of the padded product to their iterated seam, with shifts
`(0, (s - U)/2)` and canonical-class identity. -/
def ScissorCleanupStatement : Prop :=
  ∀ (S N B : ℕ) (hS : 2 ≤ S) (hN : 0 < N) (F : NormalizedFactorization S N B),
    F.StrandZeroInEveryFactor (by omega) → F.Transitive →
    ∃ (sizes : Fin N → ℕ) (D : ∀ j, GridDiagram (sizes j)) (hprep : SeamPrepared D)
      (hD : ∀ j, 2 ≤ sizes j),
      (∀ j, (wordGrid (F.word j)).MovesTo (D j)) ∧
      ∀ (H : GridDiagram (F.product.length * 3)) (hH2 : 2 ≤ F.product.length * 3),
        IsSignedWordGrid F.product H →
        ∃ ψ : laurentMaslovComplex H (ZMod 2) ⟶ laurentMaslovComplex (iteratedSeamGrid D hprep)
            (ZMod 2),
          (laurentMaslovBifiltration H (ZMod 2)).Shifts
              (laurentMaslovBifiltration (iteratedSeamGrid D hprep) (ZMod 2)) ψ 0
              ((F.scissorShiftCount : ℝ) / 2) ∧
            homologyMap ψ 0 (gridCanonicalClass H hH2) =
              gridCanonicalClass (iteratedSeamGrid D hprep) (two_le_iteratedSeamSize hN hD)

end OnLeConjecture.KnotFloer.GridFull
