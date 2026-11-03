/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridBraidMovieAssembly
public import OnLeConjecture.KnotFloer.GridMovieNativeMap
public import OnLeConjecture.KnotTheory.PositiveWordCoxeterConjugacy
public import OnLeConjecture.KnotTheory.PositiveWordGridLetterSwitch
public import OnLeConjecture.KnotTheory.PositiveWordGridMoves
public import OnLeConjecture.KnotTheory.TorusWordGridMoves

/-!
# The braid grid movie with the grid-move maps discharged

This module discharges the two map-level inputs of `braidNativeMap_of_inputs` by the
proved theorems of job J01, `exists_movesTo_canonical_map` and
`XSwitchSequence.nonempty_reverse_one`, and the word-level input by the proved theorem
`fullTwist_coxeter_conj` of job J08, and the letter deletion input by the proved theorem
`wordGrid_delete_letter` of job J10, and the torus input by the proved theorem
`reflectedTorusGrid_movesTo_coxeterPower` of job J11. Job J09 reduces the word-grid
conjugacy statement to the braid relation on word grids (`wordGrid_movesTo_of_conj_of_braid`),
so the only further input is `WordGridBraidRelationStatement`, proved as
`wordGrid_movesTo_braid` (`KnotTheory/PositiveWordGridBraidRelation.lean`).
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open OnLeConjecture.KnotTheory

/-- The grid-move map statement of job J01 holds. -/
theorem movesToCanonicalMapStatement : MovesToCanonicalMapStatement :=
  fun G H hn hk h => exists_movesTo_canonical_map G H hn hk h

/-- The X-switch reversal statement of job J01 holds. -/
theorem xSwitchReverseStatement : XSwitchReverseStatement :=
  fun h => XSwitchSequence.nonempty_reverse_one h

/-- The Coxeter conjugacy statement of job J08 holds. -/
theorem coxeterConjugacyStatement : CoxeterConjugacyStatement :=
  fun γ hγ hm => OnLeConjecture.KnotTheory.fullTwist_coxeter_conj γ hγ hm

/-- The letter deletion statement of job J10 holds. -/
theorem wordGridDeleteLetterStatement : WordGridDeleteLetterStatement :=
  fun hm u v i huv => OnLeConjecture.KnotTheory.wordGrid_delete_letter hm u v i huv

/-- The torus statement of job J11 holds. -/
theorem torusCoxeterPowerStatement : TorusCoxeterPowerStatement :=
  fun S hS => OnLeConjecture.KnotTheory.reflectedTorusGrid_movesTo_coxeterPower S hS

/-- The braid relation on selected word grids: inside arbitrary words, the grids of
`σᵢσᵢ₊₁σᵢ` and `σᵢ₊₁σᵢσᵢ₊₁` are related by grid moves. -/
def WordGridBraidRelationStatement : Prop :=
  ∀ {m : ℕ} (u v : PositiveAdjacentWord m) (i j : Fin (m - 1)), (j : ℕ) = i + 1 →
    (wordGrid (u ++ [i, j, i] ++ v)).MovesTo (wordGrid (u ++ [j, i, j] ++ v))

/-- The word-grid conjugacy statement of job J09 follows from the braid relation. -/
theorem wordGridConjugacyMovesStatement_of_braid (hbraid : WordGridBraidRelationStatement) :
    WordGridConjugacyMovesStatement :=
  fun _ _ _ _ h => OnLeConjecture.KnotTheory.wordGrid_movesTo_of_conj_of_braid
    (fun u v i j hij => hbraid u v i j hij) h

/-- **Braid native map, conditional on the braid relation on word grids.** -/
theorem braidNativeMap_of_braidRelation (hbraid : WordGridBraidRelationStatement) :
    BraidNativeMapStatement :=
  braidNativeMap_of_inputs movesToCanonicalMapStatement xSwitchReverseStatement
    coxeterConjugacyStatement (wordGridConjugacyMovesStatement_of_braid hbraid)
    wordGridDeleteLetterStatement torusCoxeterPowerStatement

/-- **Braid native map, conditional on jobs J09 and J11.** The word-grid conjugacy
statement of job J09 and the torus statement of job J11 imply the braid native map
statement. -/
theorem braidNativeMap_of_J09_J11 (h09 : WordGridConjugacyMovesStatement)
    (h11 : TorusCoxeterPowerStatement) : BraidNativeMapStatement :=
  braidNativeMap_of_inputs movesToCanonicalMapStatement xSwitchReverseStatement
    coxeterConjugacyStatement h09 wordGridDeleteLetterStatement h11

/-- **Braid native map, conditional on the grid statements.** The statements of jobs J09,
J10 and J11 imply the braid native map statement. -/
theorem braidNativeMap_of_grid_inputs (h09 : WordGridConjugacyMovesStatement)
    (h10 : WordGridDeleteLetterStatement) (h11 : TorusCoxeterPowerStatement) :
    BraidNativeMapStatement :=
  braidNativeMap_of_inputs movesToCanonicalMapStatement xSwitchReverseStatement
    coxeterConjugacyStatement h09 h10 h11

/-- **Braid native map, conditional on the word and grid statements.** The statements of
jobs J08, J09, J10 and J11 imply the braid native map statement. -/
theorem braidNativeMap_of_word_inputs (h08 : CoxeterConjugacyStatement)
    (h09 : WordGridConjugacyMovesStatement) (h10 : WordGridDeleteLetterStatement)
    (h11 : TorusCoxeterPowerStatement) : BraidNativeMapStatement :=
  braidNativeMap_of_inputs movesToCanonicalMapStatement xSwitchReverseStatement h08 h09 h10 h11

end OnLeConjecture.KnotFloer.GridFull
