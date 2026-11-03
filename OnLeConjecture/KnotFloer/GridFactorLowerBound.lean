/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFactorWord
public import OnLeConjecture.KnotFloer.GridFactorLowerBoundStatement

/-!
# The factor lower bound (Statement F)

For a positive word `w` on `a ≥ 2` strands that uses every generator and has length
`|w| = 2δ + a - 1`, the canonical class of the selected word grid has weighted spectral threshold
at least `δ t/2` for every `0 ≤ t ≤ 2/a` (`FactorWordLowerBound`, field `factor` of the native
route inputs, job J18).

The selected grid `wordGrid w` is admissible (`wordGrid_isAdmissible`), every strand rank occurs
(`occurrences_nonempty`), and `|w| - a + 1 = 2δ`. The bound is Theorem 5.8 of the factor lower
bound proof (`admissible_spectralThreshold_lower`). The hypothesis that the permutation of `w`
is one cycle is not used. The proof uses neither the torus grids nor the letter deletion and
move equivalence statements M804 and M807.

## Main results

* `factorWordLowerBound`: the statement `FactorWordLowerBound`.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

/-- **Statement F (record M801, job J18).** -/
theorem factorWordLowerBound : FactorWordLowerBound := by
  intro a ha w _ hg δ hδ t ht0 ht
  have h := admissible_spectralThreshold_lower (wordGrid_isAdmissible w) ha
    (two_le_wordGrid_size_of_generatorIndices ha hg) (occurrences_nonempty w ha hg) t ht0 ht
  have hδ' : (((w.length : ℤ) - a + 1 : ℤ) : ℝ) = 2 * (δ : ℝ) := by
    have : (w.length : ℤ) - a + 1 = 2 * δ := by omega
    rw [this]
    push_cast
    ring
  rw [hδ'] at h
  convert h using 2
  ring

end OnLeConjecture.KnotFloer.GridFull
