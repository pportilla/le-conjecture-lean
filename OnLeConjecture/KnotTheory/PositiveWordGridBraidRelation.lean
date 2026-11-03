/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationFront
public import OnLeConjecture.KnotFloer.GridBraidMovie

/-! # The braid relation on selected word grids

`docs/route-n/J09-word-grid-moves.tex`, Proposition *braid*, in the form
`KnotFloer.GridFull.WordGridBraidRelationStatement` (`wordGrid_movesTo_braid`). As corollaries, the
word-grid conjugacy statement of job J09 and the braid native map statement hold
(`BraidWindow.wordGridConjugacyMovesStatement_holds`,
`BraidWindow.braidNativeMapStatement_holds`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

/-- **The braid relation on selected word grids**, `docs/route-n/J09-word-grid-moves.tex`,
Proposition *braid*. -/
theorem wordGrid_movesTo_braid : KnotFloer.GridFull.WordGridBraidRelationStatement :=
  fun u v i j hij => wordGrid_movesTo_braid' u v i j hij

namespace BraidWindow

/-- The word-grid conjugacy statement of job J09 holds. -/
theorem wordGridConjugacyMovesStatement_holds :
    KnotFloer.GridFull.WordGridConjugacyMovesStatement :=
  KnotFloer.GridFull.wordGridConjugacyMovesStatement_of_braid wordGrid_movesTo_braid

/-- The braid native map statement holds. -/
theorem braidNativeMapStatement_holds : KnotFloer.GridFull.BraidNativeMapStatement :=
  KnotFloer.GridFull.braidNativeMap_of_braidRelation wordGrid_movesTo_braid

end BraidWindow

end OnLeConjecture.KnotTheory
