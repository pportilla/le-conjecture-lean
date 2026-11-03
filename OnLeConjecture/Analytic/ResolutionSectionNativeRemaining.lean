/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionNativeAssembly
public import OnLeConjecture.KnotFloer.GridBraidMovie
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondCycle
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamParity
public import OnLeConjecture.KnotFloer.GridFactorLowerBound
public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelation

/-!
# Lê's conjecture from the exterior statement

This module reduces Lê's conjecture to the exterior statement of the native route, by
discharging the other inputs of `NativeRouteInputs`:

* the field `parity` by `seamPositivePathComparisons`;
* the field `braid` by `braidNativeMap_of_braidRelation` applied to the braid relation on word
  grids `wordGrid_movesTo_braid` (jobs J01, J08, J09, J10 and J11, all proved);
* the field `second` by the second torus representative of job J21,
  `reflectedTorusAnchorClass_representedBelow_second_vertex_of_lt`;
* the field `factor` by the proved factor lower bound `factorWordLowerBound`.

The only hypothesis of `leConjecture_of_remaining_inputs` is the exterior statement
`ExteriorNativeMapStatement`, which is proved through `exteriorNativeMapStatement_of_reductions`
(see `LeConjectureNative.lean`).
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.KnotFloer OnLeConjecture.KnotFloer.GridFull

/-- The native route inputs from the exterior statement. -/
theorem nativeRouteInputs_of_remaining (hext : ExteriorNativeMapStatement) : NativeRouteInputs where
  parity := seamPositivePathComparisons
  second := fun n m hn hm hS =>
    reflectedTorusAnchorClass_representedBelow_second_vertex_of_lt n m hn hm hS
  braid := braidNativeMap_of_braidRelation OnLeConjecture.KnotTheory.wordGrid_movesTo_braid
  factor := factorWordLowerBound
  exterior := hext

/-- **Lê's conjecture from the exterior statement.** -/
theorem leConjecture_of_remaining_inputs (hext : ExteriorNativeMapStatement) : LeConjecture :=
  leConjecture_of_nativeRouteInputs
    (nativeRouteInputs_of_remaining hext)

end OnLeConjecture.Analytic
