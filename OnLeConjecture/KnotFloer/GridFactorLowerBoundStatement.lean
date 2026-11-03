/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalClass
public import OnLeConjecture.KnotTheory.PositiveWordBraidMoviePlan

/-!
# Statement of the factor lower bound

This module states the factor lower bound of the native route (stage 1 of job J18). For a
positive word `w` on `a ≥ 2` strands whose permutation is one cycle, which uses every
generator, and whose length is `|w| = 2δ + a - 1`, the weighted spectral threshold of the
normalized class of the selected word grid is at least `δ t / 2` for every `0 ≤ t ≤ 2/a`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

/-- The selected grid of a word on at least two strands that uses every generator has size at
least two. -/
theorem two_le_wordGrid_size_of_generatorIndices {a : ℕ} (ha : 2 ≤ a)
    {w : PositiveAdjacentWord a} (hg : w.toSigned.generatorIndices = Finset.univ) :
    2 ≤ w.length * 3 := by
  have hmem : (⟨0, by omega⟩ : Fin (a - 1)) ∈ w.toFinset := by
    rw [← PositiveAdjacentWord.generatorIndices_toSigned, hg]
    exact Finset.mem_univ _
  have hpos : 0 < w.length := List.length_pos_of_mem (List.mem_toFinset.mp hmem)
  omega

/-- **Factor lower bound statement.** For every positive word on `a ≥ 2` strands with one
permutation cycle, using every generator, with `|w| + 1 = 2δ + a`, the weighted spectral
threshold of the normalized class of its selected grid is at least `δ t / 2` for
`0 ≤ t ≤ 2/a`. -/
def FactorWordLowerBound : Prop :=
  ∀ (a : ℕ) (ha : 2 ≤ a) (w : PositiveAdjacentWord a), w.toSigned.cycleCount = 1 →
    ∀ (hg : w.toSigned.generatorIndices = Finset.univ) (δ : ℕ), w.length + 1 = 2 * δ + a →
      ∀ t : ℝ, 0 ≤ t → t ≤ 2 / (a : ℝ) →
        (((δ : ℝ) * t / 2 : ℝ) : EReal) ≤
          ((laurentMaslovBifiltration (wordGrid w) (ZMod 2)).weighted t).spectralThreshold 0
            (gridCanonicalClass (wordGrid w) (two_le_wordGrid_size_of_generatorIndices ha hg))

end OnLeConjecture.KnotFloer.GridFull
