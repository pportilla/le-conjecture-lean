/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionNativeLevelFamily
public import OnLeConjecture.KnotFloer.GridMarkedCancelCleanup

/-!
# Lê's conjecture

This module proves Lê's conjecture for map germs `(ℂ², 0) → (ℂ³, 0)`: every germ with an
injective representative has a nonzero differential at the origin.

The proof is the native route (stage B of job J23 of the dependency audit). The theorem
`leConjecture_of_markedFactorCleanup` reduces the conjecture to the marked inverse cancellation
of Section 8 of the proof of Statement E, `MarkedFactorCleanupStatement`, which is proved as
`MarkedCancel.markedFactorCleanup`.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

/-- **Lê's conjecture.** Every germ of a holomorphic map `(ℂ², 0) → (ℂ³, 0)` with an injective
representative has a nonzero differential at the origin. -/
theorem leConjecture_native : LeConjecture :=
  leConjecture_of_markedFactorCleanup OnLeConjecture.KnotTheory.MarkedCancel.markedFactorCleanup

end OnLeConjecture.Analytic
